// Returns a new string with the case of each character in the input string toggled.
method ToggleCase(s: string) returns (v: string)
  ensures v == MapSeq(s, Toggle) 
{
  v := [];
  for i := 0 to |s|
    invariant v == MapSeq(s[..i], Toggle)
  {
    v := v + [Toggle(s[i])];
  }
}

// Auxiliary function to toggle the case of a character.
function Toggle(c: char): char {
  if 'a' <= c <= 'z' then c - ('a' - 'A') 
  else if 'A' <= c <= 'Z' then c + ('a' - 'A')
  else c
}

// Auxiliary function that applies a function to every element of a sequence
// using sequence comprehension.
ghost function MapSeq<T, E>(s: seq<T>, f: T -> E) : (res: seq<E>) 
  ensures |res| == |s| && (forall i :: 0 <= i < |s| ==> res[i] == f(s[i])) // helper
{
    seq(|s|, i requires 0 <= i < |s| => f(s[i])) 
}

// Test cases chacked statically.
method ToggleCaseTest(){
  var out1 := ToggleCase("Python");
  assert out1=="pYTHON";

  var out2 := ToggleCase("LIttLE");
  assert out2=="liTTle";
}