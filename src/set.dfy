// TestSet1 fails to verify
method TestSet1() returns (s: set<int>) 
ensures s == {-4, -2, 0, 2, 4}
{
  s := (set x: int | x in {-2, -1, 0, 1, 2} :: x * 2);
}
