// Counts the number of true values in the first 'n' positions of a boolean array 'a'.
// Recursive definition and iterative implementation.
function {:fuel 3} CountTrue(a: array<bool>, n: nat := a.Length): (result: nat)
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then 0 else CountTrue(a, n-1) + (if a[n-1] then 1 else 0)
}
by method
{
  result := 0;
  for i := 0 to n
    invariant result == CountTrue(a, i)
  {
    if a[i] {
      result := result + 1;
    }
  }
}

method CountTrueTest(){
  var a1 := new bool[] [true, false, true];
  assert CountTrue(a1) == 2;
 
  var a2 := new bool[] [false, false];
  assert CountTrue(a2) == 0;

  var a3 := new bool[] [true, true, true];
  assert CountTrue(a3) == 3;
}