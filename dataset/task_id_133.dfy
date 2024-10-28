// Returns the sum of the negative numbers in an array 'a' up to index 'n' (exclusive).  
// Recursive definition and iterative implementatiom.
function {:fuel 4} SumOfNegatives(a: array<int>, n: nat := a.Length) : (result: int)
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then 0 
  else if a[n-1] < 0 then SumOfNegatives(a, n-1) + a[n-1] 
  else SumOfNegatives(a, n-1)
}
by method 
{
  result := 0;
  for i := 0 to n
    invariant result == SumOfNegatives(a, i)
  {
    if a[i] < 0 {
      result := result + a[i];
    }
  }
}

// Test cases checked statically.
method SumOfNegativesTest(){
  var a1 := new int[] [2, 4, -6, -9];
  var out1 :=SumOfNegatives(a1);
  assert out1 == -15;

  var a2 := new int[] [10, 15, -14, 13];
  var out2 := SumOfNegatives(a2);
  assert out2 == -14;
}