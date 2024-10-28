// Checks if a natural number is a perfect square.
predicate IsPerfectSquare(n: nat) {
     exists i : nat ::  i * i == n
}
by method
{
    var i := 0;
    while i * i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> k * k < n
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
    assert IsPerfectSquare(0);

    assert 1 * 1 == 1; // helper
    assert IsPerfectSquare(1);

    assert ! IsPerfectSquare(2);
    assert ! IsPerfectSquare(3);

    assert 2 * 2 == 4; // helper
    assert IsPerfectSquare(4);

    assert ! IsPerfectSquare(1000001);
}