-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/HeadNumbers.lean: THE PUBLIC NUMBERS AT THE OUTPUT HEAD's SEGMENT (l = 24), AS WRITTEN
NUMERALS, UNDER THE LIBRARY's HEAD. Statements and proofs; no definition; no goal is stated.
  `numbers_head` the two lookups' stretches: the calls' begins at slot 0 and has 1995 slots; the digits' begins at slot
      2168 and has 1363: the sealed `calls_place`, `digits_place` (Johnson/Desc/Kinds/Law/K6PubInScope.lean),
      `fs_in_scope` (HeadFsWritten.lean there), `plan_in_scope` (HeadPlanWritten.lean there)
  `filled_head` at K9's seat at 24 the tests' number of filled slots is 3570: the lines of `seated_w_head`
      (Honest/K9/TotalHead.lean) a second time, and `plan_in_scope`'s ns: typed anew so that TotalHead.lean's ground
      does not lie beneath this file
WHAT IS NOT CLAIMED. Nothing on any state or run. The head h (`P5J.AtMgA`) is a premise: the full size and the format's
second hash function alone. Called by Honest/K9/GoodHeadNums.lean; `numbers_head` by K6GoodHanded.lean too. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtSeatAll
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.Desc.Kinds.Law.K6PubInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Kinds.Head.Law.InScope (calls_place digits_place fs_in_scope plan_in_scope)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The two lookups' stretches at the head's segment, in written numbers**: the calls' begins at 0 and has 1995
slots; the digits' begins at 2168 and has 1363. -/
theorem numbers_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pC pD : Look.P}
    (hC : Look.placeAt (P5J.At.X Zp) 24 false = some pC) (hD : Look.placeAt (P5J.At.X Zp) 24 true = some pD) :
    pC.first = 0 ∧ pD.first = 2168 ∧
      ∃ hsC hsD, pC.shape = some hsC ∧ pD.shape = some hsD ∧ Forest.elems hsC = 1995 ∧ Forest.elems hsD = 1363 := by
  obtain ⟨p, e, s, f, -⟩ := calls_place h.scope h.pubOne
  obtain rfl : pC = p := Option.some.inj (hC.symm.trans e)
  obtain ⟨q, e', s', f'⟩ := digits_place h.scope h.reads h.pubOne
  obtain rfl : pD = q := Option.some.inj (hD.symm.trans e')
  exact ⟨f, f', _, _, s, s', (fs_in_scope h.scope h.reads h.pubOne).elems,
    (plan_in_scope h.scope h.reads h.pubOne).elems⟩

/-- **The tests' number of filled slots at the head's segment is 3570.** -/
theorem filled_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p w) :
    w.2.2.filled = 3570 := by
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  have ht := Sd.tested
  have h4' : Zp.p.X.p4 = true := h4
  have hN' : Zp.p.X.NGr = 12 := hN
  unfold Desc.K9.testsWhere at ht
  simp only [h4', hN', if_true] at ht
  rw [← Option.some.inj ht]
  exact (plan_in_scope h.scope h.reads h.pubOne).ns

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.numbers_head
#print axioms ProofFile.Honest.K9.filled_head
