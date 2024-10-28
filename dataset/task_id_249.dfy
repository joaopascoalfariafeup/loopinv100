// Returns a sequence with elements that belong to both arrays, without duplicates.
// The result follows the ordering of elements in a.
// In case of duplicates, it is keep an arbitrary occurrence. 
method Intersection<T(==)>(a: array<T>, b: array<T>) returns (res: seq<T>)
  // All elements in the output are in both a and b, and vice-versa
  ensures forall x :: x in res <==> x in a[..] && x in b[..]
  // The elements in the output are all different
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  // The result follows the ordering of elements in a
  ensures IsSubsequence(res, a[..])
{
  res := [];
  for i := 0 to a.Length
    invariant forall x :: x in res <==> x in a[..i] && x in b[..]
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
    invariant IsSubsequence(res, a[..i])
  {
    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
    }
  }
}

// Auxiliary predicate that checks if 'a' is a subsequence of 'b' 
// (not necessarily consecutive)
predicate IsSubsequence<T(==)>(a: seq<T>, b: seq<T>)  {
    (forall i :: 0 <= i < |a| ==> a[i] in b)
    && (forall i, j :: 0 <= i < j < |a| ==> containsInOrder(b, a[i], a[j]))
}

// Auxiliary predicate that checks if sequence 'a' contains 'x' before 'y'
predicate containsInOrder<T(==)>(a: seq<T>, x: T, y: T) {
  exists i, j :: 0 <= i < j < |a| && a[i] == x && a[j] == y
}

// Test cases checked statically
method IntersectionTest(){
  // Typical case
  var a1:= new int[] [1, 2, 3, 4, 5];
  var a2:= new int[] [1, 3, 6];
  var res1 := Intersection(a1,a2);
  // proof helpers
  assert a1[..] == [1, 2, 3, 4, 5]; 
  assert a2[..] == [1, 3, 6]; 
  assert 1 in res1 && 3 in res1;
  assert |res1| > 2 ==> res1[2] == res1[0] || res1[2] == res1[1];
  // now the assertion
  assert res1 == [1, 3];

  // Empty intersection
  var a3 := new int[] [1, 3, 5];
  var a4 := new int[] [2, 4, 6];
  var res2 := Intersection(a3, a4);
  assert |res2| > 0 ==> res2[0] in a3[..] && res2[0] in a4[..]; // helper by contradiction
  assert res2 == [];
}