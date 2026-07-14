from datetime import timedelta

from hypothesis import assume, given, strategies as st

import ttkv

KEY = st.text(min_size=1)
VALUE = st.floats(allow_nan=False, allow_infinity=False)


@st.composite
def distinct(draw, f):
    a, b = draw(f), draw(f)
    assume(a != b)
    return a, b


@given(KEY, st.datetimes() | st.none())
def test_initially_empty(k, timestamp):
    engine = ttkv.create()
    assert ttkv.get(engine, k, timestamp) is None


@given(KEY, VALUE)
def test_single_get(k, v):
    engine = ttkv.create()
    ttkv.put(engine, k, v)
    assert ttkv.get(engine, k) == v


@given(distinct(KEY), distinct(VALUE))
def test_distinct_keys(ab, xy):
    engine = ttkv.create()
    a, b = ab
    x, y = xy
    ttkv.put(engine, a, x)
    ttkv.put(engine, b, y)
    assert ttkv.get(engine, a) == x
    assert ttkv.get(engine, b) == y


@given(KEY, distinct(VALUE))
def test_two_puts_same_key(k, xy):
    engine = ttkv.create()
    x, y = xy
    ttkv.put(engine, k, x)
    assert ttkv.get(engine, k) == x
    ttkv.put(engine, k, y)
    assert ttkv.get(engine, k) == y
    assert ttkv.get(engine, k) != x


@given(KEY, distinct(VALUE))
def test_two_puts_same_key_times(k, xy):
    engine = ttkv.create()
    x, y = xy
    ttkv.put(engine, k, x)
    ttkv.put(engine, k, y)
    assert len(ttkv.times(engine, k)) == 2


@given(distinct(KEY), distinct(VALUE))
def test_two_keys_times(ab, xy):
    engine = ttkv.create()
    a, b = ab
    x, y = xy
    ttkv.put(engine, a, x)
    ttkv.put(engine, b, y)
    assert len(ttkv.times(engine)) == 2


@given(KEY, distinct(VALUE), st.floats(min_value=0, max_value=0.75))
def test_get_between(k, xy, delta):
    engine = ttkv.create()
    x, y = xy
    ttkv.put(engine, k, x)
    ttkv.put(engine, k, y)
    times = ttkv.times(engine, k)
    assert len(times) == 2
    t1, t0 = times
    assert t1 > t0
    assert ttkv.get(engine, k, t0 + delta * (t1 - t0)) == x


@given(
    KEY,
    VALUE,
    st.timedeltas(min_value=timedelta(microseconds=1), max_value=timedelta(days=1_000)),
)
def test_before_time(k, v, delta):
    engine = ttkv.create()
    ttkv.put(engine, k, v)
    times = ttkv.times(engine, k)
    assert len(times) == 1
    t = times[0]
    assert ttkv.get(engine, k, t - delta) is None
