// Replaces all blank characters in a string by a given character.
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures v == MapSeq(s, c => if c == ' ' then ch else c)
{
  v := [];
  for i := 0 to |s|
    invariant v == MapSeq(s[..i], c => if c == ' ' then ch else c)
  {
    if s[i] == ' ' {
      v := v + [ch];
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

// Test cases checked statically.
method ReplaceBlanksWithCharTest(){
  var res1 := ReplaceBlanksWithChar("hello people",'@');
  assert res1 == "hello@people";
  
  var res2 := ReplaceBlanksWithChar("python program language",'$');
  assert res2 == "python$program$language";
  
  var res3 := ReplaceBlanksWithChar("blank space",'-');
  assert res3=="blank-space";
}