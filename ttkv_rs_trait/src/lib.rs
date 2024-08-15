//! Time traveling key-value store
#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::nursery)]
#![forbid(missing_docs)]
#![forbid(unsafe_code)]

use chrono::{DateTime, Utc};
use rusqlite::{
    types::{FromSql, ToSql},
    Connection, OptionalExtension, Row,
};
use std::{collections::BTreeMap, marker::PhantomData, time::Instant};

/// Time traveling key-value store
pub trait Ttkv<T, K: PartialEq, V>: Sized {
    /// Create a store.
    ///
    /// # Errors
    /// If something goes wrong.
    fn new() -> Result<Self, Error>;
    /// Is this store empty?
    ///
    /// # Errors
    /// If something goes wrong.
    fn is_empty(&self) -> Result<bool, Error>;
    /// Add a pair to the store. If a timestamp is specified, use it; otherwise, set the insertion
    /// timestamp to now - (when this store was created).
    ///
    /// # Errors
    /// If something goes wrong.
    fn put(&mut self, key: K, value: V, timestamp: Option<T>) -> Result<(), Error>;
    /// Grab a value associated with the given key, if it exists; if a timestamp is specified, grab the
    /// latest value inserted before the given timestamp.
    ///
    /// # Errors
    /// If something goes wrong.
    fn get(&self, key: &K, timestamp: Option<T>) -> Result<Option<V>, Error>;
    /// The timestamps at which things were added to this store, optionally restricting to a
    /// specific key.
    ///
    /// # Errors
    /// If something goes wrong.
    fn times(&self, key: Option<&K>) -> Result<Vec<T>, Error>;
}

/// Errors that might occur when working with TTKVs.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Error in creation
    #[error("Error in NEW: {0}")]
    New(String),
    /// Error in checking emptiness
    #[error("Error in IS_EMPTY: {0}")]
    IsEmpty(String),
    /// Error in getting something
    #[error("Error in GET: {0}")]
    Get(String),
    /// Error in putting something
    #[error("Error in PUT: {0}")]
    Put(String),
    /// Error in collecting times
    #[error("Error in TIMES: {0}")]
    Times(String),
}

macro_rules! map_err {
    ($kind:ident, $stuff:expr) => {
        $stuff.map_err(|e| Error::$kind(e.to_string()))
    };
}

/// BTreeMap-based TTKV
#[derive(Debug)]
pub struct Map<K, V> {
    started: Instant,
    mapping: BTreeMap<K, BTreeMap<u128, V>>,
}

impl<K: Ord + PartialEq, V: Clone> Ttkv<u128, K, V> for Map<K, V> {
    fn new() -> Result<Self, Error> {
        Ok(Self {
            started: Instant::now(),
            mapping: BTreeMap::new(),
        })
    }
    fn is_empty(&self) -> Result<bool, Error> {
        Ok(self.mapping.is_empty())
    }
    fn put(&mut self, key: K, value: V, timestamp: Option<u128>) -> Result<(), Error> {
        let t = match timestamp {
            Some(t) => t,
            None => Instant::now()
                .checked_duration_since(self.started)
                .ok_or_else(|| Error::Put("non-monotonic insertion".to_string()))
                .map(|x| x.as_nanos())?,
        };
        self.mapping.entry(key).or_default().insert(t, value);
        Ok(())
    }
    fn get(&self, key: &K, timestamp: Option<u128>) -> Result<Option<V>, Error> {
        Ok(self.mapping.get(key).and_then(|i| {
            i.range(0..timestamp.unwrap_or(u128::MAX))
                .last()
                .map(|(_, v)| v.clone())
        }))
    }
    fn times(&self, key: Option<&K>) -> Result<Vec<u128>, Error> {
        let mut ts = self
            .mapping
            .iter()
            .filter_map(|(k, v)| {
                if key.map_or(true, |x| x == k) {
                    Some(v.keys().copied())
                } else {
                    None
                }
            })
            .flatten()
            .collect::<Vec<_>>();
        ts.sort_unstable();
        Ok(ts)
    }
}

/// SQLite-based TTKV
#[derive(Debug)]
pub struct SQLite<K, V> {
    db: Connection,
    k: PhantomData<K>,
    v: PhantomData<V>,
}

impl<K, V> Ttkv<DateTime<Utc>, K, V> for SQLite<K, V>
where
    K: PartialEq + FromSql + ToSql,
    V: FromSql + ToSql,
{
    fn new() -> Result<Self, Error> {
        let db = map_err!(New, Connection::open_in_memory())?;
        map_err!(
            New,
            db.execute_batch(
                "
create table ttkv (t timestamp primary key, k blob not null, v blob not null);
create index k_ix on ttkv(k);
        ",
            )
        )?;
        let (k, v) = (PhantomData, PhantomData);
        Ok(Self { db, k, v })
    }
    fn is_empty(&self) -> Result<bool, Error> {
        let mut stmt = map_err!(
            IsEmpty,
            self.db.prepare_cached("select count(*) = 0 from ttkv")
        )?;
        map_err!(IsEmpty, stmt.query_row((), |row| row.get(0)))
    }
    fn put(&mut self, key: K, value: V, timestamp: Option<DateTime<Utc>>) -> Result<(), Error> {
        let mut stmt = map_err!(
            Put,
            self.db
                .prepare_cached("insert into ttkv values (?1, ?2, ?3)")
        )?;
        map_err!(
            Put,
            stmt.execute((timestamp.unwrap_or_else(Utc::now), key, value))
        )?;
        Ok(())
    }
    fn get(&self, key: &K, timestamp: Option<DateTime<Utc>>) -> Result<Option<V>, Error> {
        let mut stmt = map_err!(
            Get,
            self.db.prepare_cached(
                "select v from ttkv where k = ?1 and t <= ?2 order by t desc limit 1"
            )
        )?;
        map_err!(
            Get,
            stmt.query_row((key, timestamp.unwrap_or_else(Utc::now)), |row| row.get(0))
                .optional()
        )
    }
    fn times(&self, key: Option<&K>) -> Result<Vec<DateTime<Utc>>, Error> {
        let sql = format!(
            "select t from ttkv{}order by t desc",
            if key.is_some() { " where k = ?1 " } else { " " }
        );
        let mut stmt = map_err!(Times, self.db.prepare_cached(&sql))?;
        let get = |row: &Row| row.get(0);
        if let Some(k) = key {
            map_err!(Times, stmt.query_map([k], get))?
        } else {
            map_err!(Times, stmt.query_map((), get))?
        }
        .map(|r| map_err!(Times, r))
        .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::TimeDelta;
    use paste::paste;

    macro_rules! test {
        ($TTKV:tt, $T:ty, $f:expr) => {
            paste! {
                mod [<$TTKV:snake:lower _tests>] {
                    use super::*;
                    use proptest::prelude::*;

                    #[test]
                    fn initially_empty() {
                        let r = <$TTKV<String, String>>::new();
                        assert!(r.is_ok());
                        let t = r.unwrap();
                        let r = t.is_empty();
                        assert!(r.is_ok());
                        assert!(r.unwrap());
                        let r = t.times(None);
                        assert!(r.is_ok());
                        assert!(r.unwrap().is_empty());
                    }

                    proptest! {
                        #[test]
                        fn single_get(a: String, x : String) {
                            let r = $TTKV::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.times(None);
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 1);
                            let r = t.times(Some(&a));
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 1);
                            let r = t.get(&a, None);
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap(), Some(x));
                        }

                        #[test]
                        fn two_gets_different_keys(a: String, b: String, x: String, y: String) {
                            prop_assume!(a != b);
                            let r = $TTKV::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.put(b.clone(), y.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.times(None);
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 2);
                            let r = t.times(Some(&a));
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 1);
                            let r = t.times(Some(&b));
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 1);
                            let r = t.get(&a, None);
                            prop_assert!(r.is_ok());
                            let g = r.unwrap();
                            let r = t.get(&b, None);
                            prop_assert!(r.is_ok());
                            let h = r.unwrap();
                            prop_assert_eq!(g, Some(x));
                            prop_assert_eq!(h, Some(y));
                        }

                        #[test]
                        fn two_gets_same_key(a: String, x: String, y: String) {
                            prop_assume!(x != y);
                            let r = $TTKV::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x, None);
                            prop_assert!(r.is_ok());
                            let r = t.put(a.clone(), y.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.times(None);
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 2);
                            let r = t.get(&a, None);
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap(), Some(y));
                        }

                        #[test]
                        fn middle_get(a: String, x: String, y: String) {
                            prop_assume!(x != y);
                            let r = $TTKV::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.put(a.clone(), y, None);
                            prop_assert!(r.is_ok());
                            let r = t.times(None);
                            prop_assert!(r.is_ok());
                            let times = r.unwrap();
                            prop_assert_eq!(times.len(), 2);
                            let (t0, t1) = (times[0], times[1]);
                            let delta = (t1 - t0) / 2;
                            let r = t.get(&a, Some(t0 + delta));
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap(), Some(x));
                        }

                        #[test]
                        #[allow(clippy::cast_lossless)]
                        fn before_time(a: String, x: String, delta in (1i64 .. (i32::MAX as i64))) {
                            let r = $TTKV::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x, None);
                            prop_assert!(r.is_ok());
                            let r = t.times(None);
                            prop_assert!(r.is_ok());
                            let times = r.unwrap();
                            prop_assert_eq!(times.len(), 1);
                            let r = t.get(&a, $f(times[0], delta));
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap(), None);
                        }

                    }
                }
            }
        };
    }

    test!(Map, u128, |t: u128, d: i64| Some(
        t.saturating_sub(d.abs().try_into().unwrap())
    ));
    test!(SQLite, DateTime<Utc>, |t: DateTime<Utc>, d: i64| Some(
        t.checked_sub_signed(TimeDelta::seconds(d.abs()))
            .unwrap_or_default()
    ));
}
