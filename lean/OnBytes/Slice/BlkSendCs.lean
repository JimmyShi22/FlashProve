-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkSendCs.lean: at a code switch, the program's sample row is the library's sample.

A code switch sends a new oracle message, and the verifier asks for one linear form of it at a drawn
seed. The library's form is `csSample` (OnBytes/Slice/CsData.lean), on the names of a new message's
coordinates. The program builds a row (`Send.form`), whose coefficients on the two tables of the
message are found in OnBytes/Slice/BlkSend.lean. This file shows that the two agree, entry by entry.
At the shapes of a code switch the pad of a message (BlkSend.lean) is one entry: on it the form has
the seed's drawn factor in place of a weight.

Main definition.
 `SendFits`      what is asked of the message's shape as the program holds it: one answer, both
                tables, the sizes of the new stage, and the pad in the last entry of the mask table.
Main theorems.
 `csSample_pad`, `csSample_entry`   the library's sample in closed form: the drawn factor on the
                pad, the weight of the drawn point at the entry's vertex elsewhere.
 `sendCs_mat`    the two agree: the library's sample at an entry is the coefficient of the program's
                row at the entry's index (`rowOn` in OnBytes/Slice/BlkRead.lean).
 `sendFits_stage`   the shape that the program gives a new message inside a proximity test meets
                `SendFits`, if its two codes have the new stage's message lengths.

Not claimed. Nothing on the run of the program's block.
-/
import OnBytes.Iop.Cs
import OnBytes.Slice.BlkSend
import OnBytes.Slice.CsSmp

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Cb.Ood

variable {s s' : Sg}

/-! ## The library's sample in closed form -/

/-- On the pad the library's sample has the drawn factor. -/
theorem csSample_pad (hf : CsFit s s') (z : ℕ → GE) (β : GEˣ) (n : CsK s ⊕ CsFree hf)
    (h : csPlace hf n = csPad hf) :
    (csSample hf).mat (fun t => z t.val, β) () n = β.val := by
  show (padRow s'.st.na fun j : {j : s'.cIn.J // j ≠ csPad hf} => cubeAt s' j.1).mat
    (fun t => z t.val, β) () (splitAt (csPad hf) (csPlace hf n)) = _
  rw [h, splitAt_self, padRow_pad]

/-- On every other entry the library's sample has the weight of the drawn point at the entry's
vertex. -/
theorem csSample_entry (hf : CsFit s s') (z : ℕ → GE) (β : GEˣ) (n : CsK s ⊕ CsFree hf)
    (h : csPlace hf n ≠ csPad hf) :
    (csSample hf).mat (fun t => z t.val, β) () n = eqW s'.st.na z (cubeAt s' (csPlace hf n)) := by
  show (padRow s'.st.na fun j : {j : s'.cIn.J // j ≠ csPad hf} => cubeAt s' j.1).mat
    (fun t => z t.val, β) () (splitAt (csPad hf) (csPlace hf n)) = _
  rw [splitAt_ne h, padRow_entry]

/-! ## The program's row -/

/-- The coefficients of a row do not depend on its target. -/
theorem rowOn_target (row : Row) (y : E) (o : ℕ) : rowOn { row with target := y } o = rowOn row o :=
  rfl

/-- What is asked of the shape of the new message, as the program holds it, at the stage s'. -/
structure SendFits (s' : Sg) (codes : Codes) (sh : OracleShape) : Prop where
  /-- one answer to the sample -/
  one : sh.answers = 1
  /-- the message has main rows -/
  main : (Send.cube codes sh).hasMain = true
  /-- the message has mask rows -/
  mask : (Send.cube codes sh).hasMask = true
  /-- the main table has the new stage's number of index bits -/
  mainBits : (Send.cube codes sh).mainBits = s'.st.Am
  /-- the mask table has the new stage's number of index bits -/
  maskBits : (Send.cube codes sh).maskBits = s'.st.Az
  /-- the pad is the last entry of the mask table -/
  pad : padIndex codes sh = 2 ^ s'.h * s'.Z.l - 1

/-- 2^Am is the number of entries of the new stage's main table. -/
private theorem pow_Am (hf : CsFit s s') : 2 ^ s'.st.Am = 2 ^ (s'.h + s'.g) * s'.C.l := by
  show 2 ^ (s'.h + s'.g + Fmt.M1.lg s'.C.l) = _
  rw [pow_add, ← hf.powC]

/-- 2^Az is the number of entries of the new stage's mask table. -/
private theorem pow_Az (hf : CsFit s s') : 2 ^ s'.st.Az = 2 ^ s'.h * s'.Z.l := by
  show 2 ^ (s'.h + Fmt.M1.lg s'.Z.l) = _
  rw [pow_add, ← hf.powZ]

/-- The library's sample at an entry of the new message is the coefficient of the program's sample
row at that entry's index, if the program's weight on an entry of either table is the weight of
the point at the entry's vertex on the whole cube. -/
theorem sendCs_mat_of (hf : CsFit s s') (codes : Codes) (sh : OracleShape)
    (hs : SendFits s' codes sh) (o : ℕ) (seed : SampleSeed) (row : Row)
    (h : Send.form codes sh o seed 0 = some row)
    (hWm : ∀ i, i < 2 ^ s'.st.Am →
      tableW codes sh seed.z .main i = eqW s'.st.na (readL seed.z) i)
    (hWk : ∀ i, i < 2 ^ s'.st.Az →
      tableW codes sh seed.z .mask i = eqW s'.st.na (readL seed.z) (2 ^ (s'.st.na - 1) + i))
    (β : GEˣ) (hβ : β.val = readE seed.beta) (n : CsK s ⊕ CsFree hf) :
    (csSample hf).mat (readP _ seed.z, β) () n = rowOn row o (outAt s' (csPlace hf n)) := by
  have hpp : padPart (Send.cube codes sh) = .mask := by
    unfold padPart
    rw [hs.mask, if_pos rfl]
  have he : ((Send.cube codes sh).hasMask || sh.mainDeg == 3) = true := by
    rw [hs.mask, Bool.true_or]
  have hm : hasPart (Send.cube codes sh) .main = true := hs.main
  have hk : hasPart (Send.cube codes sh) .mask = true := hs.mask
  have hp : hasPart (Send.cube codes sh) (padPart (Send.cube codes sh)) = true := by
    rw [hpp]
    exact hk
  have hc := coefAt_form_one codes sh o seed row h hs.one he hp
  by_cases hj : csPlace hf n = csPad hf
  · refine (csSample_pad hf (readL seed.z) β n hj).trans ?_
    rw [hj]
    show β.val = coefAt row o .mask (idxOf (cell _ _ (2 ^ s'.h * s'.Z.l - 1) _))
    rw [idxOf_cell, hc, if_pos ⟨hpp.symm, hs.pad.symm⟩, hβ]
  · refine (csSample_entry hf (readL seed.z) β n hj).trans ?_
    generalize csPlace hf n = j at hj ⊢
    rcases j with x | x
    · have hlt : idxOf x < 2 ^ s'.st.Am := by
        rw [pow_Am hf]
        exact idxOf_lt x
      have hno : ¬ (Part.main = padPart (Send.cube codes sh) ∧ idxOf x = padIndex codes sh) :=
        fun e => Part.noConfusion (e.1.trans hpp)
      show eqW s'.st.na (readL seed.z) (idxOf x) = coefAt row o .main (idxOf x)
      rw [hc, if_neg hno, if_pos hm, hWm _ hlt]
    · have hlt : idxOf x < 2 ^ s'.st.Az := by
        rw [pow_Az hf]
        exact idxOf_lt x
      have hne : idxOf x ≠ padIndex codes sh := by
        rw [hs.pad]
        exact fun e => hj (congrArg Sum.inr (idxOf_inj (e.trans (idxOf_cell _ _ _ _).symm)))
      have hno : ¬ (Part.mask = padPart (Send.cube codes sh) ∧ idxOf x = padIndex codes sh) :=
        fun e => hne e.2
      show eqW s'.st.na (readL seed.z) (2 ^ (s'.st.na - 1) + idxOf x) =
        coefAt row o .mask (idxOf x)
      rw [hc, if_neg hno, if_pos hk, hWk _ hlt]

/-- The point of the sample has as many coordinates as the new stage says. -/
theorem SendFits.bits {codes : Codes} {sh : OracleShape} (hs : SendFits s' codes sh) :
    (Send.cube codes sh).bits = s'.st.na := by
  have hb : ((Send.cube codes sh).hasMain && (Send.cube codes sh).hasMask) = true := by
    rw [hs.main, hs.mask]
    rfl
  rw [cube_bits_both codes sh hb, hs.mainBits, hs.maskBits]
  rfl

/-- The library's sample at an entry of the new message is the coefficient of the program's sample
row at that entry's index, if the shape meets `SendFits`, the seed's point has the new stage's
number of coordinates and β is the reading of the seed's factor. -/
theorem sendCs_mat (hf : CsFit s s') (codes : Codes) (sh : OracleShape)
    (hs : SendFits s' codes sh) (o : ℕ) (seed : SampleSeed) (row : Row)
    (h : Send.form codes sh o seed 0 = some row) (hz : seed.z.length = s'.st.na)
    (β : GEˣ) (hβ : β.val = readE seed.beta) (n : CsK s ⊕ CsFree hf) :
    (csSample hf).mat (readP _ seed.z, β) () n = rowOn row o (outAt s' (csPlace hf n)) := by
  have hz' : seed.z.length = (Send.cube codes sh).bits := hz.trans hs.bits.symm
  refine sendCs_mat_of hf codes sh hs o seed row h (fun i hi => ?_) (fun i hi => ?_) β hβ n
  · have hi' : i < 2 ^ partBits (Send.cube codes sh) .main := by
      show i < 2 ^ (Send.cube codes sh).mainBits
      rw [hs.mainBits]
      exact hi
    have hx : cubeIdx (Send.cube codes sh) .main i = i := by
      unfold cubeIdx
      rw [show (Part.main == Part.mask) = false from rfl, Bool.and_false,
        if_neg Bool.false_ne_true, Nat.zero_add]
    rw [tableW_eq_eqW codes sh seed.z .main i hz' hs.main hi', hx, hs.bits]
  · have hi' : i < 2 ^ partBits (Send.cube codes sh) .mask := by
      show i < 2 ^ (Send.cube codes sh).maskBits
      rw [hs.maskBits]
      exact hi
    have hx : cubeIdx (Send.cube codes sh) .mask i = 2 ^ ((Send.cube codes sh).bits - 1) + i := by
      unfold cubeIdx
      rw [hs.main, hs.mask, show (Part.mask == Part.mask) = true from rfl]
      rfl
    rw [tableW_eq_eqW codes sh seed.z .mask i hz' hs.mask hi', hx, hs.bits]

/-! ## The shape of a new message inside a proximity test -/

/-- The shape that the program gives a new message inside a proximity test (2^(h + g) main rows
over the extension field, 2^h mask rows, one answer) meets what is asked above, if its two codes
have the message lengths of the new stage's. -/
theorem sendFits_stage (hf : CsFit s s') (codes : Codes) (code maskCode : ℕ)
    (hC : (codes.base.getD code default).ell = s'.C.l)
    (hZ : (codes.mask.getD maskCode default).ell = s'.Z.l) :
    SendFits s' codes (switchTargetStage code maskCode (s'.h + s'.g) s'.h 1).shape := by
  have hm : (Send.cube codes (switchTargetStage code maskCode (s'.h + s'.g) s'.h 1).shape).hasMain
      = true := (cube_hasMain_eq codes _).trans (decide_eq_true (Nat.two_pow_pos (s'.h + s'.g)))
  have hk : (Send.cube codes (switchTargetStage code maskCode (s'.h + s'.g) s'.h 1).shape).hasMask
      = true := (cube_hasMask_eq codes _).trans (decide_eq_true (Nat.two_pow_pos s'.h))
  have hrm : (Send.cube codes
      (switchTargetStage code maskCode (s'.h + s'.g) s'.h 1).shape).mainRowBits = s'.h + s'.g := by
    rw [cube_mainRowBits_eq, if_pos hm]
    exact ceilLog2_two_pow _
  have hrk : (Send.cube codes
      (switchTargetStage code maskCode (s'.h + s'.g) s'.h 1).shape).maskRowBits = s'.h := by
    rw [cube_maskRowBits_eq, if_pos hk]
    exact ceilLog2_two_pow _
  have hlC : ceilLog2 s'.C.l = Fmt.M1.lg s'.C.l :=
    (congrArg ceilLog2 hf.powC).trans (ceilLog2_two_pow _)
  have hlZ : ceilLog2 s'.Z.l = Fmt.M1.lg s'.Z.l :=
    (congrArg ceilLog2 hf.powZ).trans (ceilLog2_two_pow _)
  refine ⟨rfl, hm, hk, ?_, ?_, ?_⟩
  · rw [cube_mainBits_eq, if_pos hm, hrm]
    show s'.h + s'.g + ceilLog2 (codes.base.getD code default).ell =
      s'.h + s'.g + Fmt.M1.lg s'.C.l
    rw [hC, hlC]
  · rw [cube_maskBits_eq, if_pos hk, hrk]
    show s'.h + ceilLog2 (codes.mask.getD maskCode default).ell = s'.h + Fmt.M1.lg s'.Z.l
    rw [hZ, hlZ]
  · unfold padIndex padLen
    rw [if_pos hk, if_pos hk, if_pos hk, hrk]
    show 2 ^ s'.h - 1 + ((codes.mask.getD maskCode default).ell - 1) * 2 ^ s'.h = _
    rw [hZ]
    have hpos : 0 < 2 ^ s'.h := Nat.two_pow_pos s'.h
    have hl : s'.Z.l ≠ 0 := by
      intro h0
      have h1 := hf.mask
      rw [h0, Nat.mul_zero] at h1
      omega
    obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hl
    rw [hm', Nat.succ_sub_one, Nat.mul_succ, Nat.mul_comm m]
    omega

end OnBytes.Slice

#print axioms OnBytes.Slice.sendCs_mat
#print axioms OnBytes.Slice.sendFits_stage
#print axioms OnBytes.Slice.csSample_pad
#print axioms OnBytes.Slice.csSample_entry
#print axioms OnBytes.Slice.sendCs_mat_of
#print axioms OnBytes.Slice.rowOn_target
#print axioms OnBytes.Slice.pow_Am
#print axioms OnBytes.Slice.pow_Az
#print axioms OnBytes.Slice.SendFits.bits
