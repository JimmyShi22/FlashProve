-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchMapsFit.lean: when the names of a code switch's two maps lie in the
tables of the sending.

Johnson/Top/H/SwitchMaps.lean writes the two maps of names iJ and iQ of a code switch out of the
program's frame, under one premise: every name lies in a table of the sending (`InTab`). Here that
premise is brought down to comparisons of public numbers. Definitions, statements and proofs.
Main names:
  `inTab_main`, `inTab_rest`, `inTab_kept`: one name lies in its table, from the laws on `cutIndex`
    and `SwitchPlaces.get` (OnBytes/Slice/SwitchPlacesLaws.lean).
  `padNoOf_lt`: the number of a place of the pad is below the pad's length.
  `Fit cs l s W mem row pl`: the comparisons: the two blocks lie in g's tables; the main row's
    message has room in its block; the rest has room in the places; each part of the rest ends
    inside the rest; a kept row's new message has the row and is long enough.
  `Fit.nameJ`, `Fit.nameQ`: under them all names lie in the tables.
Limits: that a frame of the programs meets `Fit` is not shown in this file. Nothing on soundness.

-/
import Johnson.Top.H.SwitchMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

section
variable (cs : Codes) (l : List (OracleShape × ℕ)) (W : SwitchFrame)

/-- An entry of the main row's message lies in g's main table. -/
theorem inTab_main (g : 0 < l.length) (hb : W.rowBits = ceilLog2 (l.get ⟨0, g⟩).1.mainRows)
    (hf : W.mainCut.Fits W.rowBits)
    (hr : W.mainCut.firstRow + 2 ^ W.mainCut.bits ≤ (l.get ⟨0, g⟩).1.mainRows) (j : ℕ)
    (hj : j < (pMain cs (l.get ⟨0, g⟩).1).ell * 2 ^ W.mainCut.bits) :
    InTab cs l (mainNm W j) := by
  refine ⟨g, ?_, ?_⟩
  · show cutIndex W.mainCut W.rowBits j % 2 ^ ceilLog2 (l.get ⟨0, g⟩).1.mainRows <
      (l.get ⟨0, g⟩).1.mainRows
    rw [← hb, cutIndex_mod hf]
    have := Nat.mod_lt j (Nat.two_pow_pos W.mainCut.bits)
    omega
  · show cutIndex W.mainCut W.rowBits j / 2 ^ ceilLog2 (l.get ⟨0, g⟩).1.mainRows <
      (pMain cs (l.get ⟨0, g⟩).1).ell
    rw [← hb, cutIndex_div hf]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)

/-- An entry of the rest lies in the table of g that takes the rest. -/
theorem inTab_rest (g : 0 < l.length)
    (hb : W.places.rowBits = ceilLog2 ((l.get ⟨0, g⟩).1.rows W.restPart))
    (hf : W.places.cut.Fits W.places.rowBits)
    (hr : W.places.cut.firstRow + 2 ^ W.places.cut.bits ≤ (l.get ⟨0, g⟩).1.rows W.restPart) (i : ℕ)
    (hi : i < ellOf cs (l.get ⟨0, g⟩).1 W.restPart * 2 ^ W.places.cut.bits - W.places.pad.length) :
    InTab cs l (restAt W i) := by
  refine ⟨g, ?_, ?_⟩
  · show W.places.get i % 2 ^ ceilLog2 ((l.get ⟨0, g⟩).1.rows W.restPart) <
      (l.get ⟨0, g⟩).1.rows W.restPart
    rw [← hb]
    exact lt_of_lt_of_le (SwitchPlaces.get_row W.places hf i).2 hr
  · show W.places.get i / 2 ^ ceilLog2 ((l.get ⟨0, g⟩).1.rows W.restPart) <
      ellOf cs (l.get ⟨0, g⟩).1 W.restPart
    rw [← hb]
    exact SwitchPlaces.get_place_lt W.places hf _ hi

/-- An entry of a kept row lies in the main table of its member's new message. -/
theorem inTab_kept (o rb b j : ℕ) (ho : o < l.length)
    (hb : rb = ceilLog2 (l.get ⟨o, ho⟩).1.mainRows) (hr : b < (l.get ⟨o, ho⟩).1.mainRows)
    (hj : j < (pMain cs (l.get ⟨o, ho⟩).1).ell) : InTab cs l (o, Part.main, b + 2 ^ rb * j) := by
  have h2 : b < 2 ^ rb := by
    rw [hb]
    exact lt_of_lt_of_le hr (le_two_pow_ceilLog2 _)
  refine ⟨ho, ?_, ?_⟩
  · show (b + 2 ^ rb * j) % 2 ^ ceilLog2 (l.get ⟨o, ho⟩).1.mainRows < (l.get ⟨o, ho⟩).1.mainRows
    rw [← hb, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
    exact hr
  · show (b + 2 ^ rb * j) / 2 ^ ceilLog2 (l.get ⟨o, ho⟩).1.mainRows <
      (pMain cs (l.get ⟨o, ho⟩).1).ell
    rw [← hb, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h2, Nat.zero_add]
    exact hj

end

/-- The number of a place of the pad is below the pad's length. -/
theorem padNoOf_lt : ∀ (pad : List PadPlace) (x : ℕ), x ∈ pad.map (·.index) →
    padNoOf pad x < pad.length
  | [], _, h => by simp at h
  | p :: ps, x, h => by
    unfold padNoOf
    by_cases e : p.index = x
    · rw [if_pos e, List.length_cons]
      omega
    · rw [if_neg e, List.length_cons]
      have h' : x ∈ ps.map (·.index) := by
        rw [List.map_cons, List.mem_cons] at h
        exact h.resolve_left fun k => e k.symm
      have := padNoOf_lt ps x h'
      omega

section
variable (cs : Codes) (l : List (OracleShape × ℕ)) (s : Sg) {K : Type} (W : SwitchFrame)
  (mem row : K → ℕ) (pl : K → KeptPlace)

/-- **What is asked of the public numbers.** -/
structure Fit : Prop where
  /-- the sending has a first message: g -/
  g : 0 < l.length
  mainBits : W.rowBits = ceilLog2 (l.get ⟨0, g⟩).1.mainRows
  mainFits : W.mainCut.Fits W.rowBits
  mainRows : W.mainCut.firstRow + 2 ^ W.mainCut.bits ≤ (l.get ⟨0, g⟩).1.mainRows
  /-- the main row's message has room in its block -/
  mainLen : s.C.l ≤ (pMain cs (l.get ⟨0, g⟩).1).ell * 2 ^ W.mainCut.bits
  restBits : W.places.rowBits = ceilLog2 ((l.get ⟨0, g⟩).1.rows W.restPart)
  restFits : W.places.cut.Fits W.places.rowBits
  restRows : W.places.cut.firstRow + 2 ^ W.places.cut.bits ≤ (l.get ⟨0, g⟩).1.rows W.restPart
  /-- the rest has room in the places -/
  room : W.parts.length ≤
    ellOf cs (l.get ⟨0, g⟩).1 W.restPart * 2 ^ W.places.cut.bits - W.places.pad.length
  /-- each part of the rest ends inside the rest -/
  mask : ∀ j, j < 2 → W.parts.maskAt.getD j 0 + s.Z.l ≤ W.parts.length
  mainTail : W.parts.mainTailAt + s.C.r ≤ W.parts.length
  keptTail : ∀ k, W.parts.keptTailAt.getD (keptNo W (mem k) (row k)) 0 + s.C.r ≤ W.parts.length
  maskTail : ∀ j, j < 2 → W.parts.maskTailAt.getD j 0 + s.Z.r ≤ W.parts.length
  oldPad : ∀ k, (pl k).oldPadAt + (pl k).pad.length ≤ W.parts.length
  /-- a kept row's new message is there, has the row, and is long enough -/
  keptMsg : ∀ k, ∃ h : 1 + mem k < l.length,
    (pl k).rowBits = ceilLog2 (l.get ⟨1 + mem k, h⟩).1.mainRows ∧
      row k < (l.get ⟨1 + mem k, h⟩).1.mainRows ∧
      s.C.l ≤ (pMain cs (l.get ⟨1 + mem k, h⟩).1).ell

variable {cs l s W mem row pl}

/-- An entry of the rest below the rest's length lies in its table. -/
theorem Fit.rest (F : Fit cs l s W mem row pl) (i : ℕ) (hi : i < W.parts.length) :
    InTab cs l (restAt W i) :=
  inTab_rest cs l W F.g F.restBits F.restFits F.restRows i (lt_of_lt_of_le hi F.room)

/-- **All names of the message's entries lie in the tables.** -/
theorem Fit.nameJ (F : Fit cs l s W mem row pl)
    (x : (Option K × Fin s.C.l) ⊕ (Fin s.Z.l ⊕ Fin s.Z.l)) :
    InTab cs l (nameJ s W mem row pl x) := by
  rcases x with ⟨_ | k, j⟩ | j | j
  · exact inTab_main cs l W F.g F.mainBits F.mainFits F.mainRows j.val
      (lt_of_lt_of_le j.isLt F.mainLen)
  · show InTab cs l (keptNm W (mem k) (pl k) (row k + 2 ^ (pl k).rowBits * j.val))
    unfold keptNm
    split
    · rename_i hp
      have h1 := padNoOf_lt _ _ hp
      have h2 := F.oldPad k
      exact F.rest _ (by omega)
    · obtain ⟨h, hb, hr, hl⟩ := F.keptMsg k
      exact inTab_kept cs l _ _ _ _ h hb hr (lt_of_lt_of_le j.isLt hl)
  · have h := F.mask 0 (by decide)
    have hj := j.isLt
    exact F.rest _ (by omega)
  · have h := F.mask 1 (by decide)
    have hj := j.isLt
    exact F.rest _ (by omega)

/-- **All names of the randomness' entries lie in the tables.** -/
theorem Fit.nameQ (F : Fit cs l s W mem row pl)
    (x : (Option K × Fin s.C.r) ⊕ (Fin s.Z.r ⊕ Fin s.Z.r)) :
    InTab cs l (nameQ s W mem row x) := by
  rcases x with ⟨_ | k, q⟩ | q | q
  · have h := F.mainTail
    have hq := q.isLt
    exact F.rest _ (by omega)
  · have h := F.keptTail k
    have hq := q.isLt
    exact F.rest _ (by omega)
  · have h := F.maskTail 0 (by decide)
    have hq := q.isLt
    exact F.rest _ (by omega)
  · have h := F.maskTail 1 (by decide)
    have hq := q.isLt
    exact F.rest _ (by omega)

end

end Johnson.Top.H

#print axioms Johnson.Top.H.inTab_main
#print axioms Johnson.Top.H.inTab_rest
#print axioms Johnson.Top.H.inTab_kept
#print axioms Johnson.Top.H.Fit.nameJ
#print axioms Johnson.Top.H.Fit.nameQ
