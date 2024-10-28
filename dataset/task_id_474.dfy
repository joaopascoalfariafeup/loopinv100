// Replace all occurrences of oldChar in string s by newChar 
// and return the resulting string.
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures v == MapSeq(s, c => if c == oldChar then newChar else c)
{
    v := [];
    for i := 0 to |s|
        invariant v == MapSeq(s[..i], c => if c == oldChar then newChar else c)
    {
        if s[i] == oldChar {
            v := v + [newChar];
        }
        else {
            v := v + [s[i]];
        }
    }
}

// Auxiliary function that applies a function to every element of a sequence
// using sequence comprehension.
ghost function {:opaque} MapSeq<T, E>(s: seq<T>, f: T -> E) : (res: seq<E>) 
  ensures |res| == |s| && (forall i :: 0 <= i < |s| ==> res[i] == f(s[i]))
{
    seq(|s|, i requires 0 <= i < |s| => f(s[i])) 
}

// Test cases checked statically
method ReplaceCharsTest(){
    // single occurrence
    var out1 := ReplaceChars("polygon", 'y', 'i');
    assert out1 == "poligon";

    // multiple occurrences
    var out2 := ReplaceChars("polygon", 'o', 'a');
    assert out2 == "palygan";

    // no occurrence
    var out3 := ReplaceChars("polygon", 'a', 'b');
    assert out3 == "polygon";
}