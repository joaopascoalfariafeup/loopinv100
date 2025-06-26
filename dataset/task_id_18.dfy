// Remove from the first string all characters which are present in the second string.
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == Filter(s1, c => !(c in s2))
{
  v := [];
  for i := 0 to |s1|
    invariant v == Filter(s1[..i], c => !(c in s2))
  {
    if !(s1[i] in s2) {
      v := v + [s1[i]];
    }
    assert s1[..i+1] == s1[..i] + [s1[i]]; // proof helper
  }
  assert s1 == s1[..|s1|]; // proof helper
}

// Sequence manipulation utilities

// Filters a sequence using a predicate.
// Returns a new sequence with the elements of s that satisfy the predicate p.
ghost function Filter<T>(s: seq<T>, p: T -> bool): (r : seq<T>)
    ensures |r| <= |s|
{
    if |s| == 0 then []
    else if p(Last(s)) then Filter(DropLast(s), p) + [Last(s)]
    else Filter(DropLast(s), p)
}

// Retrieves the same sequence with the last element removed 
ghost function  DropLast<T>(s: seq<T>): seq<T>
  requires |s| > 0
{ s[..|s|-1] }

// Retrieves the last element of a non-empty sequence
ghost function  Last<T>(s: seq<T>): T
  requires |s| > 0
{ s[|s|-1] }

// Test cases checked statically
method RemoveCharsTest(){
  var out1 := RemoveChars("a.b,c;", ".,;");
  assert "a.b,c;" == "a" + "." + "b" + "," + "c" + ";"; // proof helper
  assert out1 == "abc";

  var out2 := RemoveChars("exomile", "toxic");
  assert "exomile" == "e" + "x" + "o" + "m" + "i" + "l" + "e"; // proof helper
  assert out2 == "emle";
}
