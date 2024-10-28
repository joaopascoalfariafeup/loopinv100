/* 
* Formal specification and verification of a simple method for calculating 
* Fibonacci numbers applying dynamic programming.
*/

// Initial specification, functional style, recursive (exponential time)
function Fib(n : nat ) : nat {
    if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}  
// Iterative implementation in time O(n) and space O(1), using dynamic programming 
by method
{
    var x, y := 0, 1; // fib(0), fib(1)
    for i := 0 to n 
      invariant x == Fib(i) && y == Fib(i+1)
    {
        x, y := y, x + y; // simultaneous assignment
    }
    return x;
}

// Teste cases checked statically.  
method TestFib()
{
  assert Fib(0) == 0;
  assert Fib(1) == 1;
  assert Fib(2) == 1;
  assert Fib(3) == 2;
  assert Fib(4) == 3;
  assert Fib(5) == 5;
}
