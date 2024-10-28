// Finds the index of the first odd number in an arrray.
// If there is no odd number, returns -1.
method FindFirstOdd(a: array<int>) returns (index: int)
    ensures IsFirstOdd(a, index)
{
    for i := 0 to a.Length
        invariant forall j :: 0 <= j < i ==> !IsOdd(a[j])
    {
        if IsOdd(a[i]) {
            return i;
        }
    }
    return -1;
}

// Post-condition of method FindFirstOdd defined separately for reuse.
predicate IsFirstOdd(a: array<int>, index: int)
  reads a
{
    if index == -1 then forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    else 0 <= index < a.Length && IsOdd(a[index]) 
         && forall i :: 0 <= i < index ==> !IsOdd(a[i])
}

predicate IsOdd(x: int) {
    x % 2 != 0
}

// Test cases checked statically.
method FindFirstOddTest(){
    // first
    var a1 := new int[] [1, 3, 5];
    var out1 := FindFirstOdd(a1);
    assert IsFirstOdd(a1, 0); // proof helper (satisfies post-condition)
    assert out1 == 0;

    // last
    var a2 := new int[] [2, 4, 1];
    var out2 := FindFirstOdd(a2);
    assert IsFirstOdd(a2, 2); // proof helper
    assert out2 == 2;

    // middle
    var a3 := new int[] [8, 9, 1];
    var out3 := FindFirstOdd(a3);
    assert IsFirstOdd(a3, 1); // proof helper
    assert out3 == 1;

    // none
    var a4 := new int[] [8, 6, 10];
    var out4 := FindFirstOdd(a4);
    assert out4 == -1;
}