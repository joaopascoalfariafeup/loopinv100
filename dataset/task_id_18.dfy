// Remove from the first string all characters which are present in the second string
method RemoveChars(s1: string, s2: string) returns (v: string)
  ensures v == filter(s1, c => !(c in s2))
{
  v := [];
  for i := 0 to |s1|
    invariant v == filter(s1[..i], c => !(c in s2))
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
function filter<T>(s: seq<T>, p: T -> bool): (r : seq<T>)
    ensures |r| <= |s| // useful sometimes    
{
    if |s| == 0 then s
    else if p(last(s)) then filter(butlast(s), p) + [last(s)]
    else filter(butlast(s), p)
}

// Retrieves the same sequence with the last element removed 
function  butlast<T>(s: seq<T>): seq<T>
  requires |s| > 0
{ s[..|s|-1] }

// Retrieves the last element of a non-empty sequence
function  last<T>(s: seq<T>): T
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
