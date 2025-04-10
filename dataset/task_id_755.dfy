
// Obtains the second smallest element in an array of integers(in a single scan).
// The array must have at least two distinct elements.
method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires exists i, j :: 0 <= i < j < s.Length && s[i] != s[j]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length &&
                s[j] == secondSmallest > s[i] &&
                (forall k :: 0 <= k < s.Length ==> s[k] == s[i] || s[k] >= s[j] > s[i]) 

{
    // index of the smallest element inspected so far.
    var minIndex := 0; 

    // or -1 if all elements are equal so far.
    var secondMinIndex := -1; 

    for i := 1 to s.Length
      invariant 0 <= minIndex < i
      invariant -1 <= secondMinIndex < i
      invariant secondMinIndex != -1 ==> s[secondMinIndex] > s[minIndex]
      invariant forall k :: 0 <= k < i ==> s[k] == s[minIndex] || (secondMinIndex != -1 && s[k] >= s[secondMinIndex])
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