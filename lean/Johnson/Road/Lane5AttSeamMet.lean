-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttSeamMet.lean

THE TWO PREMISES WITH CONTENT OF linkOK_of_usual (Johnson/Road/Lane5AttSeam.lean), AttR0 S Z AND
(callsA S fs Z).InTables, HOLD TOGETHER OF SOME Z AT THE RECORD THAT shapeHid RETURNS; and together
they say what "the attention link is in order" says.

* **"attOrd_iff_usual"**: AttOrd S Z ↔ AttR0 S Z ∧ (callsA S fs Z).InTables, from shapeHid lid cf =
  ok (S, fs) and the premises on the configuration (attOrd_iff_calls, Johnson/Road/Lane5KeysZ.lean,
  with its four public premises as theorems).
* "attOrd_hid_met": some list Z meets AttOrd S Z at that S. The list is read out of the matrices of
  the library's honest trace of a true request (premise_met, Johnson/Road/Lane5Plain.lean: all
  weights and tokens 0), by the way back of Johnson/Road/Lane5AttBack.lean. Beside the premises of
  linkOK_of_usual: the table of scales is lawful; the matrix "as" has at least one part. AttOrd S Z
  names neither the group g nor the table of scales s: the premises hg and hsh come from the way
  back, which reads the list out of link 2 g + 1's matrices at s.
* **"seam_met"**: so some Z meets both premises.

It shows "not empty" and no more.
AttR0 is the light part: cells small, bits, the row's maximum and denominator. The scores and the
accumulators stand in "InTables". The equivalence moves that weight; it does not carry it.
The key vectors in "InTables" are kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this library
over the verifier's records, at the cells that addrA (Johnson/Road/Lane5AttDef.lean) places. The
verifier holds no key vector. That its key forms evaluate kvA is shown elsewhere under a premise
(rule, OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean); that addrA is the program's rule is shown nowhere.
"The verifier's own" is said here of shapeHid's record alone: sizes, pieces, tables.
-/
import Johnson.Road.Lane5AttTabsEq
import Johnson.Road.Lane5KeysZ
import Johnson.Road.Lane5AttBack
import Johnson.Road.Lane5Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Attention (Cfg Shape shapeHid)

variable {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}

/-- **The attention link is in order if and only if its part without the lookup clause holds and
every call's keys lie in its table**, from the verifier's own call. -/
theorem attOrd_iff_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) (Z : Zs) :
    AttOrd S Z ↔ AttR0 S Z ∧ (callsA S fs Z).InTables :=
  attOrd_iff_calls (numsA_of_hid h hc.ldh) (laidA_of_hid h U) (tabsEq_of_usual h hc hkF h12 h8 U)
    (inside_of_four (shaped_of_hid h) (tests_of_hid h).1 (four_of_hid h U)) Z

/-- **Some list meets AttOrd at the shape that shapeHid returns.** -/
theorem attOrd_hid_met (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf) (h12 : cf.S = 12)
    (h8 : cf.rx = 8) (hN : 0 < cf.NAs) {s : Cm.Scales} (hs : s.Lawful) {g : ℕ} (hg : g < 12)
    (hsh : (s.kap (4 * g)).sh = cf.sh.getD 0 0) : ∃ Z : Zs, AttOrd S Z := by
  obtain ⟨i, x, A, _, _, P⟩ := premise_met hs
  have Q := shaped_of_hid h
  exact ⟨_, ord_of_premise hg (attSized_hid h hc h12 h8) (wide_of_shaped Q hc hN)
    (by rw [Q.cfg]; exact hsh) (exp_of_hid h h12 h8) P⟩

/-- **The two premises with content of linkOK_of_usual hold together of some list.** -/
theorem seam_met (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf) (hkF : cf.kFD = 16)
    (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) (hN : 0 < cf.NAs) {s : Cm.Scales}
    (hs : s.Lawful) {g : ℕ} (hg : g < 12) (hsh : (s.kap (4 * g)).sh = cf.sh.getD 0 0) :
    ∃ Z : Zs, AttR0 S Z ∧ (callsA S fs Z).InTables := by
  obtain ⟨Z, O⟩ := attOrd_hid_met h hc h12 h8 hN hs hg hsh
  exact ⟨Z, (attOrd_iff_usual h hc hkF h12 h8 U Z).1 O⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.attOrd_iff_usual
#print axioms OnBytes.Road.L5.attOrd_hid_met
#print axioms OnBytes.Road.L5.seam_met
