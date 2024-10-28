// Recursive definition of x^n.
function Power(x: nat, n: nat) : (p: nat) {
    if n == 0 then 1 else x * Power(x, n-1)
}
// Iterative computation of x^n in time O(log n) by
// the fast exponentiation algorithm.
by method
{
    var mx: nat  := x; // remaining base
    var mn: nat := n; // remaining exponent
    p := 1; // partial result
    while mn > 0 
        invariant Power(x, n) == p * Power(mx, mn) 
    {
        PowerLemma(mx, mn / 2);
        if mn % 2 == 1 {
            p := p * mx;
        } 
        mx := mx * mx;
        mn := mn / 2;
    }
}

// Definition of x^n mod m.
function PowerMod(x: nat, n: nat, m: nat) : (res: nat) 
  requires m > 1
{
    Power(x, n) % m
}
// Iterative computation of x^n mod m in time O(log n) by the 
// fast modular exponentiation algorithm.
by method
{
    var mn: nat := n; // remaining exponent

    ghost var mx: nat := x; // remaining base for computing Power(x, n) (ghost)
    ghost var p : nat := 1; // partial result for computing Power(x, n) (ghost)

    var mx2: nat := x % m; // remaining base for computing Power(x, n) % m (mx2 is the same as mx % m)
    var p2 : nat := 1; // partial result for computing Power(x, n) % m (p2 is the same as p % m)

    while mn > 0 
        invariant Power(x, n) == p * Power(mx, mn)
        invariant p2 == p % m
        invariant mx2 == mx % m
    {
        PowerLemma(mx, mn / 2);
        if mn % 2 == 1 {
            ModLemma(p, mx, m); //==> (p * mx) % m == ((p % m) * (mx % m)) % m == (p2 * mx2) % m
            p := p * mx;
            p2 := (p2 * mx2) % m;
        } 
        mn := mn / 2;
        ModLemma(mx, mx, m); // ==> (mx * mx) % m == ((mx % m) * (mx % m)) % m == (mx2 * mx2) % m
        mx := mx * mx;
        mx2 := (mx2 * mx2) % m;
    }
    
    assert Power(x, n) % m == p % m == p2; // helper
    return p2;
}

// Sattes the property (proved automatically) that x^(2n) = (x^2)^n.
lemma PowerLemma(x: nat, n: nat) 
  ensures Power(x, 2 * n) == Power(x * x, n) 
{}

// Prove by deduction that (a * b) % m == ((a % m) * (b % m)) % m, with m > 0
lemma ModLemma(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    var q1 := a / m;
    var r1 := a % m;
    assert a == q1 * m + r1;

    var q2 := b / m;
    var r2 := b % m;
    assert b == q2 * m + r2;

    assert a * b == (q1 * m + r1) * (q2 * m + r2);
    var q := q1 * q2 * m + q1 * r2 + q2 * r1;
    var r := r1 * r2;
    ModLemma2(q, r, m); // ==> (a * b) % m == (q * m + r) % m == r % m
 }

// Prove by induction that (q * m + r) % m == r % m, with m > 0.
lemma {:induction q} ModLemma2(q: nat, r: nat, m: nat)
  decreases q
  requires m > 0
  ensures (q * m + r) % m == r % m
{
    if q > 0 {
        ModLemma2(q - 1, r + m, m); // ==> (q * m + r) % m == (r + m) % m
        ModLemma3(r + m, m, r / m + 1, r % m); // ==> (r + m) % m == r % m
    } 
}

// Proves by contradiction that if n == q * m + r and r < m (with m > 0), then r == n % m.
lemma ModLemma3(n: nat, m: nat, q: nat, r: nat)
    requires m > 0 && n == q * m + r && r < m
    ensures r == n % m
{
    var q1 := n / m;
    var r1 := n % m;
    assert n == q1 * m + r1 && r1 < m;
    if q < q1 {
       ProdLemma(q1 - q, m); // ==> r - r1 == (q1 - q) * m >= m
       assert r >= m; // contradiciton
    }
    else if q1 < q {
       ProdLemma(q - q1, m); //  ==> r1 - r == (q - q1) * m >= m;
       assert r1 >= m; // contradiciton
    }
}

// States the property (proved automatically) that a * b >= b when a > 0.
lemma ProdLemma(a: nat, b: nat)
 requires a > 0
 ensures a * b >= b
{}

// A few test cases (checked statically by Dafny).
method TestModularExponentiation() {
    assert Power(2, 10) == 1024;
    assert PowerMod(2, 10, 7) == 2;

    assert Power(10, 6) == 1000000;
    assert PowerMod(10, 6, 9) == 1;
}