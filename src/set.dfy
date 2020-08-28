// TestSet1 fails to verify
// method TestSet1() {
//   assert (set x: int | x in {-2, -1, 0, 1, 2} :: x * 2) == {-4, -2, 0, 2, 4};
// }

function Intersection<T>(s1: set<T>, s2: set<T>): set<T>
  ensures forall x :: x in s1 && x in s2 ==> x in Intersection(s1, s2)
  ensures forall x :: x in Intersection(s1, s2) ==> x in s1 && x in s2
{
  set x | x in s1 && x in s2
}

// Union fails to verify:
// Dafny uses syntactic heuristics to determine whether a set comprehension is finite
// The heuristics depend on type of the bound variables or conjuncts that constrain elements to be bounded
// Dafny has no syntactic heuristic for proving a bound for disjunctions
function Union<T>(s1: set<T>, s2: set<T>): set<T>
  ensures forall x :: x in s1 || x in s2 ==> x in Union(s1, s2)
  ensures forall x :: x in Union(s1, s2) ==> x in s1 || x in s2
{
  set x | x in s1 || x in s2
}
