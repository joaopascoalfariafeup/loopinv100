// Converts a string to uppercase (only 'a' to 'z' characters are converted).
method ToUppercase(s: string) returns (v: string)
    ensures v == MapSeq(s, CharToUpper)
{
    v := [];
    for i := 0 to |s|
        invariant  v == MapSeq(s[..i], CharToUpper)
    {
        v := v + [CharToUpper(s[i])];
    }
}

function CharToUpper(c : char) : char {
    if 'a' <= c <= 'z' then c - ('a' - 'A') else c
}

// Auxiliary function that applies a function to every element of a sequence
// using sequence comprehension.
ghost function MapSeq<T, E>(s: seq<T>, f: T -> E) : (res: seq<E>) 
  ensures |res| == |s| && (forall i :: 0 <= i < |s| ==> res[i] == f(s[i])) // helper
{
    seq(|s|, i requires 0 <= i < |s| => f(s[i])) 
}

// Test cases checked statically.
method ToUppercaseTest(){
  var out1 := ToUppercase("person");
  assert out1 == "PERSON";

  var out2 := ToUppercase("final");
  assert out2 == "FINAL";

}