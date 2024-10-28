// Checks if a string contains the letter 'z' or 'Z'
method ContainsZ(s: string) returns (result: bool)
    ensures result <==> 'z' in s || 'Z' in s
{
    result := false;
    for i := 0 to |s|
        invariant 'z' !in s[..i] && 'Z' !in s[..i]
    {
        if s[i] == 'z' || s[i] == 'Z' {
            return true;
        }
    }
    return false;

}

// Teste cases checked statically
method ContainsZTest() {
  var out1 := ContainsZ("pythonz");
  assert out1;

  var out2 := ContainsZ("XYZ.");
  assert out2;

  var out3 := ContainsZ("  lang  .");
  assert !out3;
}