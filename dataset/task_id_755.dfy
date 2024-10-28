// Obtains the second smallest element in an array of integers.
// The array must have at least two distinct elements.
method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires ! allEqual(s[..])
    ensures isSecondSmallest(s[..], secondSmallest)
{
    // index of the smallest element inspected so far.
    var minIndex := 0; 

    // index of the second smallest element inspected so far,
    // or -1 if all elements are equal so far.
    var secondMinIndex := -1; 

    for i := 1 to s.Length
      invariant 0 <= minIndex < i
      invariant -1 <= secondMinIndex < i
      invariant isSmallest(s[..i], s[minIndex]) 
      invariant secondMinIndex != -1 ==> isSecondSmallest(s[..i], s[secondMinIndex])
      invariant secondMinIndex == -1 ==> allEqual(s[..i])  // not found by GPT!
    {
        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] > s[minIndex] && (secondMinIndex == -1 || s[i] < s[secondMinIndex]) {
            secondMinIndex := i;
        }
    }

    secondSmallest := s[secondMinIndex];
}

// Checks if all elemts in a sequence of integers are equal.
ghost predicate allEqual(s: seq<int>) {
    forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
}

// Checks if a value (x) is the smallest element of a sequence of integers (s).
ghost predicate isSmallest(s: seq<int>, x: int) {
    x in s[..] && (forall i :: 0 <= i < |s| ==> x <= s[i])
}

// Checks if a value (x) is the second smallest element of a sequence of integers (s).
ghost predicate isSecondSmallest(s: seq<int>, x: int) {
    x in s[..] && ! isSmallest(s, x) && (forall i :: 0 <= i < |s| && !isSmallest(s, s[i]) ==> x <= s[i])
}

// Test cases checked statically.
method SecondSmallestTest(){
    var a1:= new int[] [1, 2, -8, -2, -2, -8];
    assert a1[2] != a1[3]; // proof helper (example for precondition)
    var out1 := SecondSmallest(a1);
    assert out1 == -2;

    var a2:= new int[] [2, 2, 1];
    assert a2[0] != a2[2];
    var out2 := SecondSmallest(a2);
    assert out2 == 2;

    var a3:= new int[] [-2, -3, -1];
    assert a3[1] != a3[0];
    var out3 := SecondSmallest(a3);
    assert out3 == -2;
}