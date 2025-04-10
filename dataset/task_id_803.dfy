// Checks if a natural number is a perfect square.
ghost predicate isPerfectSquare(n: nat) {
     exists i : nat ::  i * i == n
}

method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result == isPerfectSquare(n)
{
    var i := 0;
    while i * i < n
        invariant 0 <= i <= n
        invariant i > 0 ==> (i - 1) * (i - 1) < n
    {
        i := i + 1;
    }

    // Proof helper
    forall j: nat 
        ensures j > i ==> j * j > i * i
    {}

    return i * i == n;
}

// Test cases checked statically
method IsPerfectSquareTest(){
    assert 0 * 0 == 0; // helper
    var r := IsPerfectSquare(0); assert r;

    assert 1 * 1 == 1; // helper
    r := IsPerfectSquare(1); assert r;
    
    r := IsPerfectSquare(2); assert !r;
    r := IsPerfectSquare(3); assert !r;

    assert 2 * 2 == 4; // helper (witness)
    r := IsPerfectSquare(4); assert r;

    r := IsPerfectSquare(1000001); assert !r;
}