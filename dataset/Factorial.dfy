
// Computes the factorial of a number n.
// The factorial is defined recursively and is computed iteratively. 
function Fact(n: nat) : nat
  decreases n
{
    if n == 0 then 1 else n * Fact(n-1)
}
by method
{
  var f := 1;
  for i := 1 to n + 1 
    invariant f == Fact(i-1)
  {
    f := f * i;
  }
  return f;
}

// Test cases checked statically.    
method TestFact()
{
  assert Fact(0) == 1;
  assert Fact(1) == 1;
  assert Fact(2) == 2;
  assert Fact(3) == 6;
 }
