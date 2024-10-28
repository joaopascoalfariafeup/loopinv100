// Computes the sum of the elements of an array between indices i (included) and j (excluded). 
// Specified recursively and implemente iteratively.
// 'fuel' attribute helps checking the assertions in the test cases.
function {:fuel 4,5} ArraySum(a: array<int>, i: nat := 0, j: nat := a.Length) : int
  requires 0 <= i <= j <= a.Length
  reads a
{
  if j <= i then 0 else ArraySum(a, i, j-1) + a[j-1]
}
by method
{
    var s := 0;
    for k := i to j
        invariant s == ArraySum(a, i, k)
    {
        s := s + a[k];
    }
    return s;
}

// Test cases checked statically.
method ArraySumTest(){
  var a1 := new int[] [1, 2, 3];
  assert ArraySum(a1) == 6;

  var a2 := new int[] [15, 12, 13, 10];
  assert ArraySum(a2) == 50;

  var a3 := new int[] [];
  assert ArraySum(a3) == 0;
}