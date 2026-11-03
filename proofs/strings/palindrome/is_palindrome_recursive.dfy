module PCC_strings_palindrome__is_palindrome_recursive_2a876c89 {
  import opened PyLib
  predicate pre(s: string) { true }
  predicate spec(s: string, result: bool) requires pre(s) { result == (s == py_reversed(s)) }

  lemma LemmaSmall(s: string)
    requires |s| <= 1
    ensures s == py_reversed(s)
  {
    assert |py_reversed(s)| == |s|;
    forall i | 0 <= i < |s|
      ensures s[i] == py_reversed(s)[i]
    {
      assert py_reversed(s)[i] == s[|s| - 1 - i];
    }
    assert s == py_reversed(s);
  }

  lemma LemmaMismatch(s: string)
    requires |s| > 1
    requires s[0] != s[|s| - 1]
    ensures s != py_reversed(s)
  {
    assert |py_reversed(s)| == |s|;
    assert py_reversed(s)[0] == s[|s| - 1 - 0];
    assert s[0] != py_reversed(s)[0];
  }

  lemma LemmaSliceLen(s: string)
    requires |s| > 1
    ensures |py_slice(s, 1, -1)| == |s| - 2
    ensures forall i :: 0 <= i < |py_slice(s, 1, -1)| ==> py_slice(s, 1, -1)[i] == s[1 + i]
  {
    var t := py_slice(s, 1, -1);
    if |s| == 2 {
      assert |t| == |s| - 2;
    } else {
      assert |s| > 2;
      assert |t| == |s| - 2;
    }
    forall i | 0 <= i < |t|
      ensures t[i] == s[1 + i]
    {
      assert t[i] == s[1 + i];
    }
  }

  lemma LemmaPalindromeStep(s: string)
    requires |s| > 1
    requires s[0] == s[|s| - 1]
    ensures (s == py_reversed(s) <==> py_slice(s, 1, -1) == py_reversed(py_slice(s, 1, -1)))
  {
    LemmaSliceLen(s);
    var t := py_slice(s, 1, -1);
    assert |t| == |s| - 2;
    assert |py_reversed(s)| == |s|;
    assert forall i :: 0 <= i < |s| ==> py_reversed(s)[i] == s[|s| - 1 - i];
    assert |py_reversed(t)| == |t|;
    assert forall j :: 0 <= j < |t| ==> py_reversed(t)[j] == t[|t| - 1 - j];
    assert forall i :: 0 <= i < |t| ==> t[i] == s[1 + i];
    if s == py_reversed(s) {
      forall j | 0 <= j < |t|
        ensures t[j] == py_reversed(t)[j]
      {
        assert 0 <= 1 + j < |s|;
        assert t[j] == s[1 + j];
        assert py_reversed(t)[j] == t[|t| - 1 - j];
        assert 0 <= |t| - 1 - j < |t|;
        assert t[|t| - 1 - j] == s[1 + (|t| - 1 - j)];
        assert s[1 + j] == py_reversed(s)[1 + j];
        assert py_reversed(s)[1 + j] == s[|s| - 1 - (1 + j)];
        assert 1 + (|t| - 1 - j) == |s| - 2 - j;
        assert |s| - 1 - (1 + j) == |s| - 2 - j;
      }
      assert t == py_reversed(t);
    }
    if t == py_reversed(t) {
      forall i | 0 <= i < |s|
        ensures s[i] == py_reversed(s)[i]
      {
        assert py_reversed(s)[i] == s[|s| - 1 - i];
        if i == 0 {
          assert s[i] == s[0];
          assert s[|s| - 1 - i] == s[|s| - 1];
        } else if i == |s| - 1 {
          assert s[i] == s[|s| - 1];
          assert s[|s| - 1 - i] == s[0];
        } else {
          assert 0 < i && i < |s| - 1;
          var j := i - 1;
          assert 0 <= j < |t|;
          assert s[i] == t[j];
          assert t[j] == py_reversed(t)[j];
          assert py_reversed(t)[j] == t[|t| - 1 - j];
          assert 0 <= |t| - 1 - j < |t|;
          assert t[|t| - 1 - j] == s[1 + (|t| - 1 - j)];
          assert 1 + (|t| - 1 - j) == |s| - 1 - i;
        }
      }
      assert s == py_reversed(s);
    }
  }

  method is_palindrome_recursive(s: string) returns (result: bool)
    requires pre(s)
    ensures spec(s, result)
    decreases |s|
  {
    assert py_len(s) == |s|;
    if py_len(s) <= 1 {
      assert |s| <= 1;
      LemmaSmall(s);
      assert s == py_reversed(s);
      assert spec(s, true);
      return true;
    }
    assert |s| > 1;
    assert py_index(s, 0) == s[0];
    assert py_index(s, py_len(s) - 1) == s[|s| - 1];
    if py_index(s, 0) == py_index(s, py_len(s) - 1) {
      assert s[0] == s[|s| - 1];
      LemmaSliceLen(s);
      assert |py_slice(s, 1, -1)| == |s| - 2;
      assert |py_slice(s, 1, -1)| < |s|;
      var pcc_t1 := is_palindrome_recursive(py_slice(s, 1, -1));
      assert spec(py_slice(s, 1, -1), pcc_t1);
      assert pcc_t1 == (py_slice(s, 1, -1) == py_reversed(py_slice(s, 1, -1)));
      LemmaPalindromeStep(s);
      assert (s == py_reversed(s) <==> py_slice(s, 1, -1) == py_reversed(py_slice(s, 1, -1)));
      assert spec(s, pcc_t1);
      return pcc_t1;
    } else {
      assert s[0] != s[|s| - 1];
      LemmaMismatch(s);
      assert s != py_reversed(s);
      assert spec(s, false);
      return false;
    }
  }

}
