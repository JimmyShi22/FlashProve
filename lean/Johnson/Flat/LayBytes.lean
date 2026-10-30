-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/LayBytes.lean: an instance written as its request file and its reply, with a decoder,
and the two laws that make the pair a one-to-one spelling.

An instance holds T tokens, the numbers r and e, and the reply y (`Inst.Model.Instance`). The
request file that says it (`requestBytesOf`, Johnson/Flat/WordsBytes.lean) holds the tokens, r and
e, and not y. So `layB x` is the pair of that file and y. `unlayB` reads such a pair back; it
refuses a file that is not made of T + 2 whole words, a token word that is not below the vocabulary,
and an r or e above T. Nothing is asked of r against e: the type has instances that the program's
reader refuses, and they are written and read back like the others.

Main names:
  `layB`, `unlayB`: the two functions.
  `unlayB_layB`: where the window is below 2 ^ 32 and the vocabulary at most 2 ^ 32: `unlayB (layB
    x) = some x`, at every instance x.
  `layB_of_unlayB`: `unlayB p = some x → layB x = p`, with no premise on the sizes.
  `layB_inj`: so `layB` is one to one, under the two bounds.
Limits: the two bounds are premises of the first law: a number of the instance is written as a word
of 32 bits. `sizesAt_planned` (Johnson/Flat/SizesPlanned.lean) gives them at the sizes of a
parameter file. Nothing on the statement's item, nor on any hash.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.EarlyApart

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model OnBytes.Model.Verify

/-- An entry that is there, read with a default. -/
theorem getD_of_lt (a : Array UInt32) (j : Nat) (h : j < a.size) : a.getD j 0 = a[j] := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- Word number t of the request's words is token t. -/
theorem requestWordsOf_tok {P : Params} (x : Instance' P) (t : Fin P.T) :
    (requestWordsOf x).getD t.val 0 = UInt32.ofNat (x.prompt t).val := by
  have ht : t.val < (requestWordsOf x).size := by
    rw [size_requestWordsOf]
    omega
  rw [getD_of_lt _ _ ht]
  simp [requestWordsOf, t.isLt]

/-- The request's words are the list w, if w has their number and agrees with them word by word. -/
theorem requestWordsOf_eq {P : Params} (x : Instance' P) (w : Array UInt32)
    (hs : w.size = P.T + 2) (ht : ∀ t : Fin P.T, UInt32.ofNat (x.prompt t).val = w.getD t.val 0)
    (hr : UInt32.ofNat x.r = w.getD P.T 0) (he : UInt32.ofNat x.e = w.getD (P.T + 1) 0) :
    requestWordsOf x = w := by
  apply Array.ext
  · rw [size_requestWordsOf, hs]
  · intro j h1 h2
    rw [← getD_of_lt _ _ h1, ← getD_of_lt _ _ h2]
    rw [size_requestWordsOf] at h1
    by_cases hj : j < P.T
    · rw [← ht ⟨j, hj⟩]
      exact requestWordsOf_tok x ⟨j, hj⟩
    · by_cases hj2 : j = P.T
      · rw [hj2, requestWordsOf_r, hr]
      · have hj3 : j = P.T + 1 := by omega
        rw [hj3, requestWordsOf_e, he]

/-- What `unlayB` asks of a request file's words. -/
def WordsFit (P : Params) (w : Array UInt32) : Prop :=
  w.size = P.T + 2 ∧ (∀ t : Fin P.T, (w.getD t.val 0).toNat < P.V) ∧
    (w.getD P.T 0).toNat < P.T + 1 ∧ (w.getD (P.T + 1) 0).toNat < P.T + 1

instance (P : Params) (w : Array UInt32) : Decidable (WordsFit P w) := by
  unfold WordsFit
  exact inferInstance

/-- **An instance as its request file and its reply.** -/
def layB {P : Params} (x : Instance' P) : ByteArray × Fin P.V := (requestBytesOf x, x.y)

/-- **The decoder.** -/
def unlayB {P : Params} (p : ByteArray × Fin P.V) : Option (Instance' P) :=
  if h : p.1.size % 4 = 0 ∧ WordsFit P (words32 p.1) then
    some ⟨fun t => ⟨((words32 p.1).getD t.val 0).toNat, h.2.2.1 t⟩, p.2,
      ⟨((words32 p.1).getD P.T 0).toNat, h.2.2.2.1⟩,
      ⟨((words32 p.1).getD (P.T + 1) 0).toNat, h.2.2.2.2⟩⟩
  else none

/-- The request file that says an instance is made of whole words. -/
theorem requestBytesOf_whole {P : Params} (x : Instance' P) : (requestBytesOf x).size % 4 = 0 := by
  unfold requestBytesOf bytesOfWords
  rw [size_catWords]
  omega

/-- **What is written is read back.** -/
theorem unlayB_layB {P : Params} (hT : P.T < 2 ^ 32) (hV : P.V ≤ 2 ^ 32) (x : Instance' P) :
    unlayB (layB x) = some x := by
  have hw : words32 (requestBytesOf x) = requestWordsOf x := words32_bytesOfWords _
  have back : ∀ n : Nat, n < 2 ^ 32 → (UInt32.ofNat n).toNat = n := fun n hn => by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt hn
  have bt : ∀ t : Fin P.T, ((requestWordsOf x).getD t.val 0).toNat = (x.prompt t).val := fun t => by
    rw [requestWordsOf_tok]
    exact back _ (Nat.lt_of_lt_of_le (x.prompt t).isLt hV)
  have br : ((requestWordsOf x).getD P.T 0).toNat = x.rF.val := by
    rw [requestWordsOf_r]
    exact back _ (by have := x.rF.isLt; show x.rF.val < _; omega)
  have be : ((requestWordsOf x).getD (P.T + 1) 0).toNat = x.eF.val := by
    rw [requestWordsOf_e]
    exact back _ (by have := x.eF.isLt; show x.eF.val < _; omega)
  have hfit : (requestBytesOf x).size % 4 = 0 ∧ WordsFit P (words32 (requestBytesOf x)) := by
    refine ⟨requestBytesOf_whole x, ?_⟩
    rw [hw]
    refine ⟨size_requestWordsOf x, fun t => ?_, ?_, ?_⟩
    · rw [bt]
      exact (x.prompt t).isLt
    · rw [br]
      exact x.rF.isLt
    · rw [be]
      exact x.eF.isLt
  unfold unlayB layB
  rw [dif_pos hfit]
  obtain ⟨prompt, y, rF, eF⟩ := x
  simp only [Option.some.injEq, Instance.mk.injEq]
  refine ⟨?_, trivial, ?_, ?_⟩
  · funext t
    apply Fin.ext
    show ((words32 (requestBytesOf _)).getD t.val 0).toNat = _
    rw [hw]
    exact bt t
  · apply Fin.ext
    show ((words32 (requestBytesOf _)).getD P.T 0).toNat = _
    rw [hw]
    exact br
  · apply Fin.ext
    show ((words32 (requestBytesOf _)).getD (P.T + 1) 0).toNat = _
    rw [hw]
    exact be

/-- **What is read is what was written.** -/
theorem layB_of_unlayB {P : Params} {p : ByteArray × Fin P.V} {x : Instance' P}
    (h : unlayB p = some x) : layB x = p := by
  unfold unlayB at h
  split at h
  · rename_i hf
    have e := Option.some.inj h
    have hw : requestWordsOf x = words32 p.1 := by
      rw [← e]
      exact requestWordsOf_eq _ (words32 p.1) hf.2.1 (fun _ => UInt32.ofNat_toNat)
        UInt32.ofNat_toNat UInt32.ofNat_toNat
    have hy : x.y = p.2 := by rw [← e]
    unfold layB requestBytesOf
    rw [hw, bytesOfWords_words32 _ hf.1, hy]
  · cases h

/-- So the spelling is one to one. -/
theorem layB_inj {P : Params} (hT : P.T < 2 ^ 32) (hV : P.V ≤ 2 ^ 32) {x x' : Instance' P}
    (h : layB x = layB x') : x = x' := by
  have e := unlayB_layB hT hV x
  rw [h, unlayB_layB hT hV x'] at e
  exact (Option.some.inj e).symm

end OnBytes.Flat
