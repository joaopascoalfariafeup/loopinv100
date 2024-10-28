// Convert a string to lowercase
method ToLowercase(s: string) returns (v: string)
    ensures v == MapSeq(s, CharToLower)
{
    v := [];
    for i := 0 to |s|
        invariant v == MapSeq(s[..i], CharToLower)
    {
        v := v + [CharToLower(s[i])];
    }
}

// Convert a single character to lowercase
function CharToLower(c : char) : char {
    if 'A' <= c <= 'Z' then c + ('a' - 'A') else c
}


// Auxiliary function that applies a function to every element of a sequence
// using sequence comprehension.
ghost function {:opaque} MapSeq<T, E>(s: seq<T>, f: T -> E) : (res: seq<E>) 
  ensures |res| == |s| && (forall i :: 0 <= i < |s| ==> res[i] == f(s[i]))
{
    seq(|s|, i requires 0 <= i < |s| => f(s[i])) 
}

// Test cases checked statically
method TestToLowercase()
{
    // Test case 1
    var result := ToLowercase("Hello, World!");
    assert result == "hello, world!";

    // Test case 2
    result := ToLowercase("Dafny IS Fun!");
    assert result == "dafny is fun!";

    // Test case 3 - Testing an empty string
    result := ToLowercase("");
    assert result == "";

    // Test case 4 - Testing a string with no alphabetical characters
    result := ToLowercase("1234567890");
    assert result == "1234567890";
}