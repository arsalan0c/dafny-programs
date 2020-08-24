function update(s: seq<int>, i: int, v: int): seq<int>
   requires 0 <= i < |s|
   ensures update(s, i, v) == s[i := v]
{
  s[..i] + [v] + s[i+1..]
}

function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
  (if a[0] then 1 else 0) + count(a[1..])
}

method countTest() {
  assert count([]) == 0;
  assert count([true]) == 1;
  assert count([false]) == 0;
  assert count([true, true]) == 2;
}

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{
  if a == [] {
    assert a + b == b;
  } else {
    DistributiveLemma(a[1..], b);
    assert a + b == [a[0]] + (a[1..] + b);
  }
}