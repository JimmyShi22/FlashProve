-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/InRange.lean: THEOREMS: THE TWO STATEMENTS OF InRangeOwed.lean: AS TYPED THEY
ARE FALSE; WITH ONE PREMISE MORE, THAT EVERY CODE's MESSAGE LENGTH IS A POWER OF TWO
(Codes.lengthsOk codes = true), THEY HOLD.
WHY. The layout of a vector (vectorLay, OnBytes/Iop/Foldeq.lean) gives a row 2 ^ logEll places,
where logEll is the least a with ell ≤ 2 ^ a; the statements speak of ell. vectorRoom counts the
entries in front of the pad, and the pad stands at the end of the LAST row alone: so with rowsHigh,
two rows and ell = 3 the first row's entry 3 lies at place 3, which no message of length 3 has. No
conjunct of linOk says that a length is a power of two.
  foldl_min_le, room_facts   an entry below vectorRoom is below mainRows * 2 ^ logEll; and where the
                  rows are low the number of rows is a power of two.
  inRange_of_room **general in the message's shape**: where 2 ^ logEll = ell, every entry below
                  vectorRoom has its place below ell.
  omegaInRange_of_lengths, wInRange_of_lengths   THE TWO STATEMENTS UNDER Codes.lengthsOk.
  badCodes, badOmega, badW, not_omegaInRange, not_wInRange   two shapes with linOk's yes, by the
                  kernel, at which the statements as typed fail: ¬ OmegaInRange, ¬ WInRange.
What is not claimed. That a description's codes meet lengthsOk (every run of the blocks' engine
tests it: Blk.runNamed). Nothing on soundness.

-/
import Johnson.Desc.K14.Law.InRangeOwed
import Johnson.Desc.K1.Law.When

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params

theorem foldl_min_le {α : Type} (c : α → Bool) (f : α → Nat) :
    ∀ (l : List α) (r : Nat), l.foldl (fun m p => if c p then min m (f p) else m) r ≤ r
  | [], r => Nat.le_refl r
  | p :: l, r => by
    rw [List.foldl_cons]
    refine Nat.le_trans (foldl_min_le c f l _) ?_
    split
    · exact Nat.min_le_left _ _
    · exact Nat.le_refl r

/-- What an entry below vectorRoom has. -/
theorem room_facts (codes : Codes) (s : OracleShape) (hi : Bool) (y : Nat)
    (hy : y < vectorRoom codes s hi) :
    y < s.mainRows * 2 ^ (codes.base.getD s.code default).logEll ∧
      (hi = false → s.mainRows = 2 ^ ceilLog2 s.mainRows) := by
  simp only [vectorRoom] at hy
  split at hy
  · exact absurd hy (Nat.not_lt_zero _)
  · rename_i h1
    refine ⟨?_, ?_⟩
    · split at hy
      · exact absurd hy (Nat.not_lt_zero _)
      · split at hy
        · exact hy
        · split at hy
          · exact absurd hy (Nat.not_lt_zero _)
          · exact Nat.lt_of_lt_of_le hy (foldl_min_le _ _ _ _)
    · intro hf
      subst hf
      simpa [vectorLay] using h1

/-- **Every entry below vectorRoom has its place below the message's length**, where that length is
2 ^ logEll. -/
theorem inRange_of_room (codes : Codes) (s : OracleShape) (hi : Bool)
    (hE : 2 ^ (codes.base.getD s.code default).logEll = (codes.base.getD s.code default).ell)
    (y : Nat) (hy : y < vectorRoom codes s hi) :
    (vectorLay codes s hi).index y / 2 ^ ceilLog2 s.mainRows <
      (codes.base.getD s.code default).ell := by
  obtain ⟨hb, hr⟩ := room_facts codes s hi y hy
  have hR : s.mainRows ≤ 2 ^ ceilLog2 s.mainRows := OnBytes.Slice.le_two_pow_ceilLog2 _
  rw [← hE]
  cases hi with
  | true =>
    show (y / 2 ^ (codes.base.getD s.code default).logEll +
      y % 2 ^ (codes.base.getD s.code default).logEll * 2 ^ ceilLog2 s.mainRows) /
        2 ^ ceilLog2 s.mainRows < 2 ^ (codes.base.getD s.code default).logEll
    have ha : y / 2 ^ (codes.base.getD s.code default).logEll < 2 ^ ceilLog2 s.mainRows :=
      Nat.lt_of_lt_of_le (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)) hR
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt ha, Nat.zero_add]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  | false =>
    show y / 2 ^ ceilLog2 s.mainRows < 2 ^ (codes.base.getD s.code default).logEll
    exact Nat.div_lt_of_lt_mul
      (Nat.lt_of_lt_of_eq hb
        (congrArg (· * 2 ^ (codes.base.getD s.code default).logEll) (hr rfl)))

/-- **Omega's indices lie inside its message's range**, where the codes' lengths are powers of two.
-/
theorem omegaInRange_of_lengths (codes : Codes) (S : LinShape) (hl : codes.lengthsOk = true)
    (h : linOk codes S = true) (y : Nat) (hy : y < S.matrixRows) :
    (linLayOmega codes S).index y / 2 ^ ceilLog2 S.omega.mainRows <
      (Johnson.Pack.pMain codes S.omega).ell := by
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Codes.lengthsOk, Bool.and_eq_true] at hl
  obtain ⟨⟨⟨⟨⟨⟨_, hc⟩, _⟩, _⟩, _⟩, hroom⟩, _⟩ := h
  exact inRange_of_room codes S.omega S.omegaRowsHigh
    (VerifiableInference.Desc.K1.pow_logEll codes.base S.omega.code hc hl.1) y
    (Nat.lt_of_lt_of_le hy hroom)

/-- **W's indices lie inside its message's range**, where the codes' lengths are powers of two. -/
theorem wInRange_of_lengths (codes : Codes) (S : LinShape) (hl : codes.lengthsOk = true)
    (h : linOk codes S = true) (c : Nat) (hc' : c < 2 ^ S.kCol) :
    (linLayW codes S).index c / 2 ^ ceilLog2 S.w.mainRows <
      (Johnson.Pack.pMain codes S.w).ell := by
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Codes.lengthsOk, Bool.and_eq_true] at hl
  obtain ⟨⟨⟨⟨⟨_, hc⟩, _⟩, _⟩, _⟩, hroom⟩ := h
  exact inRange_of_room codes S.w S.wRowsHigh
    (VerifiableInference.Desc.K1.pow_logEll codes.base S.w.code hc hl.1) c
    (Nat.lt_of_lt_of_le hc' hroom)

/-! ## As typed the two statements fail -/

/-- Two codes for main rows: lengths 8 and 3; one for mask rows. -/
def badCodes : Codes := { base := #[⟨4, 8, 0⟩, ⟨4, 3, 0⟩], mask := #[⟨4, 4, 0⟩] }

/-- A message of one row under code 0; of two rows under code 1 (length 3); a split's message. -/
def one8 : OracleShape := { code := 0, mainRows := 1, mainDeg := 3, answers := 1 }

def two3 : OracleShape := { code := 1, mainRows := 2, mainDeg := 3, answers := 1 }

def splitM : OracleShape := { mainRows := 0, maskRows := 1, maskCode := 0, answers := 1 }

/-- A shape with linOk's yes whose Omega has two rows of length 3, rows high, and four entries. -/
def badOmega : LinShape :=
  { fold := { index := { code := ⟨4, 4, 0⟩, v := 0, answers := 0, saltBytes := 40 }, u := one8
              rowsHigh := true, leafClass := 0, columns := 1 }
    kLo := 0, matrixRows := 4, omega := two3, w := one8, omegaRowsHigh := true, wRowsHigh := true
    sharedSplit := splitM, ownSplit := splitM, omegaLeafClass := 0, sharedSplitLeafClass := 1
    wLeafClass := 0, ownSplitLeafClass := 1, sharedMaskCode := 0, ownMaskCode := 0
    masksAhead := false, testU := [], testOmega := [], testOwn := [], testOwnOmega := []
    choice := ⟨false⟩ }

/-- The like for W: four columns. -/
def badW : LinShape :=
  { badOmega with kLo := 2, matrixRows := 1, omega := one8, w := two3 }

theorem not_omegaInRange : ¬ OmegaInRange := fun h =>
  absurd (h badCodes badOmega (by decide +kernel) 3 (by decide +kernel)) (by decide +kernel)

theorem not_wInRange : ¬ WInRange := fun h =>
  absurd (h badCodes badW (by decide +kernel) 3 (by decide +kernel)) (by decide +kernel)

end Desc.K14.Law

#print axioms Desc.K14.Law.inRange_of_room
#print axioms Desc.K14.Law.omegaInRange_of_lengths
#print axioms Desc.K14.Law.wInRange_of_lengths
#print axioms Desc.K14.Law.not_omegaInRange
#print axioms Desc.K14.Law.not_wInRange
