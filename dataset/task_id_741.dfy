// Checks if all characters in a string are the same.
predicate AllCharactersSame(s: string) {
    forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
}
by method {
    if |s| > 1 {
        var firstChar := s[0];
        for i := 1 to |s|
            invariant forall k :: 0 <= k < i ==> s[k] == firstChar
        {
            if s[i] != firstChar {
                return false;
            }
        }
    }
    return true;
}

// Test cases checked statically.
method AllCharactersSameTest(){
    var s1 := "python";
    assert s1[0] != s1[1]; // proof helper (counter example)
    assert ! AllCharactersSame(s1);

    var s2 := "axa";
    assert s2[0] != s2[1]; // proof helper (counter example)
    assert ! AllCharactersSame(s2);

    assert AllCharactersSame("aaa");
    assert AllCharactersSame("a");
    assert AllCharactersSame("");
}