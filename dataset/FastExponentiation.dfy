// Recursive definiton of x^n.
function Power(x: real, n: nat) : (p: real) {
    if n == 0 then 1.0 else x * Power(x, n-1)
}

// Computes x^n in time O(log n) and space O(1) 
// using the fast exponentiation algorithm.
method FastExponentiation(x: real, n: nat) returns (p: real)
  ensures p == Power(x, n)
{
  p := 1.0; // partial result
  var mx: real := x; // remaining x
  var mn: nat := n; // remaining n
  while mn > 0 
    invariant Power(x, n) == p * Power(mx, mn)
  {
     PowerLemma(mx, mn/2); // invokes the lemma
     if mn % 2 == 1 { p := p * mx; } 
     mx := mx * mx;
     mn := mn / 2;
    }
}

// States the property x^(2*n) = (x^2)^(n).
lemma {:induction n} PowerLemma(x: real, n: nat) 
  ensures Power(x, 2 * n) == Power(x * x, n) 
{ /*proved automatically by Dafny (automatic induction)!*/ }

// Test cases checked statically by Dafny!
method testPowerDC() {
  var p1 := FastExponentiation(2.0, 10); assert p1 == 1024.0;
  var p2 := FastExponentiation(2.0, 0); assert p2 == 1.0;
  var p3 := FastExponentiation(-2.0, 1); assert p3 == -2.0;
}


