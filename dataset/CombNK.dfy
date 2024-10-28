/* 
* Formal specification and verification of a dynamic programming algorithm for calculating
* the binomial coefficient C(n, k).
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
function Comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{
  if k == 0 || k == n then 1 else Comb(n-1, k) + Comb(n-1, k-1)  
}
// Iterative implementation in time O(k*(n-k)) and space O(n-k), using dynamic programming.
by method
{
  var maxj := n - k;
  var c := new nat[1 + maxj];
  // Start with the values (1) in the first ascending diagonal of the Pascal triangle
  for j := 0 to maxj + 1
    invariant forall k :: 0 <= k < j ==> c[k] == Comb(j, 0)
  {
       c[j] := 1; // Comb(j, 0)
  }

  // At the begin of each iteration 'i', C[k] contains the value of Comb(k+i-1, i-1)
  // (an ascending diagonal in the Pascal triangle)
  for i := 1 to k + 1 
    invariant forall j :: 0 <= j <= maxj ==> c[j] == Comb(j + i - 1, i - 1)
  {
    // Compute the values of the next ascending diagonal in the Pascal triangle
    for j := 1 to maxj + 1
        invariant forall k :: 0 <= k < j ==> c[k] == Comb(k + i, i) // from this iteration
        invariant forall k :: j <= k <= maxj ==> c[k] == Comb(k + i - 1, i - 1) // from previous iteration
    {
      // At this point c[j] contains Comb(j+i-1, i-1)  (not updated yet) 
      // and c[j-1] contains Comb(j-1+i, i) (already updated)
      c[j] := c[j] + c[j-1];   
      // At this point c[j] contains Comb(j+i, i)
    } 
  }
  return c[maxj];
}


// Test cases checked statically and dynamically  
method Main() {
  // Checked statically
  assert Comb(5, 0) == 1;
  assert Comb(5, 2) == 10;
  assert Comb(5, 5) == 1;

  // Checked dynamically
  expect Comb(40, 10) == 847660528;
}


