-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/InstanceLaws.lean: the program's reader of a request takes the words that say an
instance, and reads the instance's numbers off them.

Main names:
  `size_requestWordsOf`: the request file's words are P.T + 2.
  `stFromCall_wordsOf`: `Model.Head.stFromCall` (OnBytes/Model/HeadLayout.lean) at `requestWordsOf
    x`, `replyWordsOf x` and P.T returns these words with r, e and y of x.
  `requestAt_range`, `buildAt_range`: a built instance meets what that law asks of x.
  `stFromCall_buildAt`: so the reader takes the words of every built instance.
Limits: `stFromCall_wordsOf` asks of x: r < e, and y = 0 if e < P.T, as the reader asks; all ask of
P: P.T and P.V fit a word of four bytes. Nothing on the tokens: the reader that is named here does
not look at them.

-/
import Johnson.Flat.Instance

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model

/-- The request file's words are P.T + 2. -/
theorem size_requestWordsOf {P : Params} (x : Instance' P) :
    (requestWordsOf x).size = P.T + 2 := by
  simp [requestWordsOf]

/-- Word number P.T is r. -/
theorem requestWordsOf_r {P : Params} (x : Instance' P) :
    (requestWordsOf x).getD P.T 0 = UInt32.ofNat x.r := by
  simp [requestWordsOf, Array.getD_eq_getD_getElem?]

/-- Word number P.T + 1 is e. -/
theorem requestWordsOf_e {P : Params} (x : Instance' P) :
    (requestWordsOf x).getD (P.T + 1) 0 = UInt32.ofNat x.e := by
  simp [requestWordsOf, Array.getD_eq_getD_getElem?]

/-- **The program's reader takes the words of an instance.** -/
theorem stFromCall_wordsOf {P : Params} (x : Instance' P) (hT : P.T < 2 ^ 32) (hV : P.V ≤ 2 ^ 32)
    (hre : x.r < x.e) (hy : x.e < P.T → x.y.val = 0) :
    Model.Head.stFromCall (requestWordsOf x) (replyWordsOf x) P.T =
      .ok { req := requestWordsOf x, r := x.r, e := x.e, y := x.y.val } := by
  have hrT : x.r ≤ P.T := Nat.lt_succ_iff.1 x.rF.isLt
  have heT : x.e ≤ P.T := Nat.lt_succ_iff.1 x.eF.isLt
  have hr : (UInt32.ofNat x.r).toNat = x.r := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have he : (UInt32.ofNat x.e).toNat = x.e := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hyv : (UInt32.ofNat x.y.val).toNat = x.y.val := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by have := x.y.isLt; omega)
  have hq : (replyWordsOf x).getD 0 0 = UInt32.ofNat x.y.val := rfl
  unfold Model.Head.stFromCall
  rw [requestWordsOf_r, requestWordsOf_e, hq, hr, he, hyv]
  have h1 : (!((requestWordsOf x).isEmpty || (replyWordsOf x).isEmpty)) = true := by
    simp [Array.isEmpty, size_requestWordsOf, replyWordsOf]
  have h2 : (!((requestWordsOf x).size != P.T + 2 || (replyWordsOf x).size != 1)) = true := by
    simp [size_requestWordsOf, replyWordsOf]
  have h3 : (!(decide (x.r ≥ x.e) || decide (x.e > P.T) ||
      (decide (x.e < P.T) && x.y.val != 0))) = true := by
    by_cases h : x.e < P.T
    · simp [hy h, Nat.not_le.2 hre, Nat.not_lt.2 heT]
    · simp [h, Nat.not_le.2 hre, Nat.not_lt.2 heT]
  simp only [h1, h2, h3, Model.Head.needed]
  rfl

/-- A built instance has a range that is not empty, and the reply token 0 if the range ends before
the window's end. -/
theorem requestAt_range {P : Params} {hV : 0 < P.V} {prompt output padding : List (Fin P.V)}
    {x : Instance' P} (h : requestAt P hV prompt output padding = some x) :
    x.r < x.e ∧ (x.e < P.T → x.y.val = 0) := by
  unfold requestAt at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases h
    refine ⟨?_, ?_⟩
    · show prompt.length - 1 < prompt.length - 1 + output.length
      omega
    · intro he
      have he' : prompt.length - 1 + output.length < P.T := he
      show ((prompt ++ output).getD P.T ⟨0, hV⟩).val = 0
      rw [List.getD_eq_default _ _ (by rw [List.length_append]; omega)]
  · cases h

/-- The same of `buildAt`. -/
theorem buildAt_range {P : Params} {hV : 0 < P.V} {t : List VerifiableInference.Token ×
    List VerifiableInference.Token} {padding : List VerifiableInference.Token} {x : Instance' P}
    (h : buildAt P hV t padding = some x) : x.r < x.e ∧ (x.e < P.T → x.y.val = 0) := by
  unfold buildAt at h
  split at h
  · exact requestAt_range h
  · cases h

/-- **The program's reader takes the words of every built instance.** -/
theorem stFromCall_buildAt {P : Params} {hV : 0 < P.V} {t : List VerifiableInference.Token ×
    List VerifiableInference.Token} {padding : List VerifiableInference.Token} {x : Instance' P}
    (hT : P.T < 2 ^ 32) (hV' : P.V ≤ 2 ^ 32) (h : buildAt P hV t padding = some x) :
    Model.Head.stFromCall (requestWordsOf x) (replyWordsOf x) P.T =
      .ok { req := requestWordsOf x, r := x.r, e := x.e, y := x.y.val } :=
  stFromCall_wordsOf x hT hV' (buildAt_range h).1 (buildAt_range h).2

end OnBytes.Flat
