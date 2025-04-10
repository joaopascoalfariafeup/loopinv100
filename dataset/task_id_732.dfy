// Replaces all spaces, commas and dots in a string with colons.
method ReplaceWithColon(s: string) returns (v: string)
    ensures v == MapSeq(s, ReplaceCharWithColon)
{
    v := [];
    for i := 0 to |s|
        invariant v == MapSeq(s[..i], ReplaceCharWithColon)
    {
        v := v + [ReplaceCharWithColon(s[i])];
    }
}

// Transformation to apply to each character.
function ReplaceCharWithColon(c: char) : char {
    if c == ' ' || c == ',' || c == '.' then ':' else c
}

// Auxiliary function that applies a function to every element of a sequence
// using sequence comprehension.
ghost function  MapSeq<T, E>(s: seq<T>, f: T -> E) : (res: seq<E>) 
  ensures |res| == |s| && (forall i :: 0 <= i < |s| ==> res[i] == f(s[i])) // helper
{
    seq(|s|, i requires 0 <= i < |s| => f(s[i])) 
}

// Test cases checked statically.
method ReplaceWithColonTest(){
    var out1 := ReplaceWithColon("Python language, Programming language.");
    assert out1 == "Python:language::Programming:language:";

    var out2 := ReplaceWithColon("a b c,d e f");
    assert out2 == "a:b:c:d:e:f";

    var out3 := ReplaceWithColon("ram reshma,ram rahim");
    assert out3 == "ram:reshma:ram:rahim";
}
