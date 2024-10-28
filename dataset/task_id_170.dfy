// Calculates the sum of elements in an array, 
// from a 'start' index (inclusive) to an 'end' index (exclusive).
// The recursive definition is implemented iteratively.
function {:fuel 4} SumRange(a: array<int>, start: nat := 0, end: nat := a.Length): (sum: int)
  requires 0 <= start <= end <= a.Length
  reads a
{
  if start == end then 0 else SumRange(a, start, end-1) + a[end-1]
}
by method 
{
  sum := 0;
  for i := start to end
    invariant sum == SumRange(a, start, i)
  {
    sum := sum + a[i];
  }
}

// Test cases checked statically.
method SumInRangeTest(){
  var a1 := new int[] [2, 1, 5, 6];
  assert SumRange(a1, 1, 3) == 6;
  assert SumRange(a1, 0, 0) == 0;
  assert SumRange(a1, 0, 4) == 14;
}