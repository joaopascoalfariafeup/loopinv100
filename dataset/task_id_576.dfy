// Interesting example that previously had a bug for empty lists.
// Checks if a sequence is a sublist of another sequence.
predicate IsSublist<T(==)>(sub: seq<T>, main: seq<T>){
    exists i :: 0 <= i <= |main| && sub <= main[i..]
} 
by method {
    var n := |main| - |sub|;
    if n >= 0 {
        for i := 0 to n + 1
            invariant forall j :: 0 <= j < i ==> !(sub <= main[j..])
        {
            if sub <= main[i .. ] {
                return true;
            }
        }
    }
    return false;
}

// Test cases checked statically.
method IsSublistTest(){
    var a0: seq<int> := [1, 0, 2, 2];
    var a1: seq<int> := [1, 2];
    assert a0[0] == a1[0] && a0[1] != a1[1]; // proof helper
    assert ! IsSublist(a1, a0);

    var a2: seq<int> :=  [0, 2, 2];
    assert a2 <= a0[1..]; // proof helper (example)
    assert IsSublist(a2, a0);

    var a3: seq<int> := [];
    assert IsSublist(a3, a0);
    assert a3 == a3[0..]; // proof helper (example)
    assert IsSublist(a3, a3);
}