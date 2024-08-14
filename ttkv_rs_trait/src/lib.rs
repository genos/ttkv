//! Time traveling key-value store
#![forbid(missing_docs)]
#![forbid(unsafe_code)]

use chrono::{DateTime, Utc};
use rusqlite::{
    types::{FromSql, ToSql},
    Connection, OptionalExtension,
};
use std::{collections::BTreeMap, marker::PhantomData, time::Instant};

/// Time traveling key-value store
pub trait Ttkv<T, K, V>: Sized {
    /// Create a store.
    fn new() -> Result<Self, Error>;
    /// Is this store empty?
    fn is_empty(&self) -> Result<bool, Error>;
    /// Add a pair to the store. If a timestamp is specified, use it; otherwise, set the insertion
    /// timestamp to now - (when this store was created).
    fn put(&mut self, key: K, value: V, timestamp: Option<T>) -> Result<(), Error>;
    /// Grab a value associated with the given key, if it exists; if a timestamp is specified, grab the
    /// latest value inserted before the given timestamp.
    fn get(&self, key: &K, timestamp: Option<T>) -> Result<Option<V>, Error>;
    /// The timestamps at which things were added to this store.
    fn times(&self) -> Result<Vec<T>, Error>;
}

/// Errors that might occur when working with TTKVs.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Errors on creation
    #[error("Unable to create a TTKV: {0}")]
    Creation(String),
    /// Error in checking emptiness
    #[error("Unable to IS_EMPTY: {0}")]
    IsEmpty(String),
    /// Error in getting something
    #[error("Unable to GET: {0}")]
    Get(String),
    /// Error in putting something
    #[error("Unable to PUT: {0}")]
    Put(String),
    /// Error in collecting times
    #[error("Unable to TIMES: {0}")]
    Times(String),
}

/// Map-based TTKV
#[derive(Debug)]
pub struct Map<K, V> {
    started: Instant,
    mapping: BTreeMap<K, BTreeMap<u128, V>>,
}

impl<K: Ord, V: Clone> Ttkv<u128, K, V> for Map<K, V> {
    fn new() -> Result<Self, Error> {
        Ok(Self {
            started: Instant::now(),
            mapping: Default::default(),
        })
    }
    fn is_empty(&self) -> Result<bool, Error> {
        Ok(self.mapping.is_empty())
    }
    fn put(&mut self, key: K, value: V, timestamp: Option<u128>) -> Result<(), Error> {
        let t = match timestamp {
            Some(t) => Ok(t),
            None => Instant::now()
                .checked_duration_since(self.started)
                .ok_or(Error::Put("non-monotonic insertion".to_string()))
                .map(|x| x.as_nanos()),
        }?;
        self.mapping.entry(key).or_default().insert(t, value);
        Ok(())
    }
    fn get(&self, key: &K, timestamp: Option<u128>) -> Result<Option<V>, Error> {
        Ok(self.mapping.get(key).and_then(|i| {
            i.range(0..timestamp.unwrap_or(u128::MAX))
                .last()
                .map(|(_, v)| v)
                .cloned()
        }))
    }
    fn times(&self) -> Result<Vec<u128>, Error> {
        let mut ts = self
            .mapping
            .values()
            .flat_map(|i| i.keys().copied())
            .collect::<Vec<_>>();
        ts.sort();
        Ok(ts)
    }
}

/// SQLite-based TTKV
#[derive(Debug)]
pub struct SQLite<K, V> {
    connection: Connection,
    k: PhantomData<K>,
    v: PhantomData<V>,
}

impl<K: FromSql + ToSql, V: FromSql + ToSql> Ttkv<DateTime<Utc>, K, V> for SQLite<K, V> {
    fn new() -> Result<Self, Error> {
        let connection =
            Connection::open_in_memory().map_err(|e| Error::Creation(e.to_string()))?;
        connection
            .execute_batch(
                "
create table ttkv (timestamp text primary key, key blob not null, value blob not null);
create index key_index on ttkv(key);
        ",
            )
            .map_err(|e| Error::Creation(e.to_string()))?;
        Ok(Self {
            connection,
            k: PhantomData,
            v: PhantomData,
        })
    }
    fn is_empty(&self) -> Result<bool, Error> {
        let mut stmt = self
            .connection
            .prepare_cached("select 1 from ttkv limit 1")
            .map_err(|e| Error::IsEmpty(e.to_string()))?;
        let count = stmt
            .query_row((), |row| row.get::<usize, usize>(0))
            .optional()
            .map_err(|e| Error::IsEmpty(e.to_string()))?;
        Ok(count.unwrap_or(0) == 0)
    }
    fn put(&mut self, key: K, value: V, timestamp: Option<DateTime<Utc>>) -> Result<(), Error> {
        let mut stmt = self
            .connection
            .prepare_cached("insert into ttkv values (?1, ?2, ?3)")
            .map_err(|e| Error::Put(e.to_string()))?;
        stmt.execute((timestamp.unwrap_or_else(Utc::now), key, value))
            .map_err(|e| Error::Put(e.to_string()))?;
        Ok(())
    }
    fn get(&self, key: &K, timestamp: Option<DateTime<Utc>>) -> Result<Option<V>, Error> {
        let t = timestamp.unwrap_or(Utc::now());
        let mut stmt = self.connection.prepare_cached(
                "select value from ttkv where key = ?1 and timestamp <= ?2 order by timestamp desc limit 1"
            ).map_err(|e| Error::Get(e.to_string()))?;
        stmt.query_row((key, t), |row| row.get::<usize, V>(0))
            .optional()
            .map_err(|e| Error::Get(e.to_string()))
    }
    fn times(&self) -> Result<Vec<DateTime<Utc>>, Error> {
        let mut stmt = self
            .connection
            .prepare_cached("select timestamp from ttkv order by timestamp desc")
            .map_err(|e| Error::Times(e.to_string()))?;
        let iter = stmt
            .query_map((), |row| row.get::<usize, DateTime<Utc>>(0))
            .map_err(|e| Error::Times(e.to_string()))?;
        iter.map(|r| r.map_err(|e| Error::Times(e.to_string())))
            .collect::<Result<Vec<_>, Error>>()
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
                        let r = <$TTKV<String, String> as Ttkv<$T, String, String>>::new();
                        assert!(r.is_ok());
                        let t = r.unwrap();
                        let r = t.is_empty();
                        assert!(r.is_ok());
                        assert!(r.unwrap());
                        let r = t.times();
                        assert!(r.is_ok());
                        assert!(r.unwrap().is_empty());
                    }

                    proptest! {
                        #[test]
                        fn single_get(a: String, x : String) {
                            let r = <$TTKV<String, String> as Ttkv<$T, String, String>>::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.times();
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 1);
                            let r = t.get(&a, None);
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap(), Some(x));
                        }

                        #[test]
                        fn two_gets_different_keys(a: String, b: String, x: String, y: String) {
                            prop_assume!(a != b);
                            let r = <$TTKV<String, String> as Ttkv<$T, String, String>>::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.put(b.clone(), y.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.times();
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 2);
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
                            let r = <$TTKV<String, String> as Ttkv<$T, String, String>>::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x, None);
                            prop_assert!(r.is_ok());
                            let r = t.put(a.clone(), y.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.times();
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap().len(), 2);
                            let r = t.get(&a, None);
                            prop_assert!(r.is_ok());
                            prop_assert_eq!(r.unwrap(), Some(y));
                        }

                        #[test]
                        fn middle_get(a: String, x: String, y: String) {
                            prop_assume!(x != y);
                            let r = <$TTKV<String, String> as Ttkv<$T, String, String>>::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x.clone(), None);
                            prop_assert!(r.is_ok());
                            let r = t.put(a.clone(), y, None);
                            prop_assert!(r.is_ok());
                            let r = t.times();
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
                        fn before_time(a: String, x: String, delta in (1i64 .. (std::i32::MAX as i64))) {
                            let r = <$TTKV<String, String> as Ttkv<$T, String, String>>::new();
                            prop_assert!(r.is_ok());
                            let mut t = r.unwrap();
                            let r = t.put(a.clone(), x, None);
                            prop_assert!(r.is_ok());
                            let r = t.times();
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
        t.saturating_sub(d.try_into().unwrap())
    ));
    test!(SQLite, DateTime<Utc>, |t: DateTime<Utc>, d: i64| Some(
        t.checked_sub_signed(TimeDelta::seconds(d))
            .unwrap_or_default()
    ));
}
