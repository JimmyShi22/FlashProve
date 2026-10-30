-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodAttPlan.lean: "GOOD" (`goodW`) IN FRONT OF THE BATCHING OF AN ATTENTION SEGMENT
AT THE PLAN's OWN NUMBERS: Honest/K9/GoodAttSeat.lean's `goodW_att` with K5's two public premises 
paid under the library's head, and n THE PUBLIC NUMBER THAT K9's TEST BEHIND THE BATCHING READS. Statements and proofs
ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated. No probability is in this file.
  **`seated_w_att`**   under the head, at K9's seat at 2 g + 1, a the segment's plan off the public parameters: the
      seat's letter w IS (.attention, a.nLin, ⟨1, 2 g + 1, 0, a.nMsg, a.seam.nU⟩): so the number of slots that K9's
      test reads (`w.2.2.filled`) is a.nMsg, and the plan's number of claims (`w.2.1`) is a.nLin
  `stretches_att`   so the three stretches end at that number: `k5End a.own (Forest.elems a.fs) + Forest.elems
      a.seam.tl.f9 = w.2.2.filled` (K5's house's `k5End_msgs`, over the library's tiling of the plan's slots)
  **`goodW_att_plan`**   from the head, g < 12, the seat, the plan, `HeldLive a.own k s` and `LookLive Lk p a.own k
      w.2.2.filled s`: `goodW p ‹the segment's gatherer› s w.2.2.filled`. K5's `LiveFits` and a.NC = a.S.calls.size
      are premises no more (`liveFits_at_head`, `nc_at_head`: Johnson/Desc/K5/Honest/Law/SlotsTiled.lean)
WHAT IS NOT CLAIMED. `HeldLive` or `LookLive` at any state: `LookLive` MAY BE UNMEETABLE. That k, the ledger's next
slot in front of K5's hearing, is `Forest.elems a.fs` (k stays a letter in `goodW_att_plan`). Which slots the lookups'
claims name. No member. `goodW_att_plan`, `stretches_att`: called by no line. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodAttSeat
import Johnson.Desc.K5.Honest.Law.SlotsTiled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (HeldLive k5End liveFits_at_head nc_at_head k5End_msgs)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The seat's letter w at an attention segment is the plan's.** -/
theorem seated_w_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    w = (.attention, a.nLin, ⟨1, 2 * g + 1, 0, a.nMsg, a.seam.nU⟩) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h4, g', hg', eg, _⟩ := LPFK9.att_facts h O (2 * g + 1) (by omega) (sub_odd g hg)
  obtain rfl : g = g' := by omega
  rw [O.W] at h4 hg'
  have ht := Sd.tested
  have ha' : Zp.p.X.A[g]? = some a := ha
  unfold Desc.K9.testsWhere at ht
  simp only [h4, if_true] at ht
  have e1 : (2 * g + 1 == 2 * Zp.p.X.NGr) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : ((2 * g + 1) % 2 == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e3 : (2 * g + 1) / 2 = g := by omega
  rw [e1, e2, e3, ha'] at ht
  exact (Option.some.inj ht).symm

/-- The three stretches end at the number that K9's test reads. -/
theorem stretches_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    k5End a.own (Forest.elems a.fs) + Forest.elems a.seam.tl.f9 = w.2.2.filled := by
  rw [seated_w_att h hg Sd ha]
  exact k5End_msgs h ha

/-- **"Good" at the plan's own numbers.** -/
theorem goodW_att_plan (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {k : ℕ} (s : S) (hI : HeldLive a.own k s)
    (hJ : LookLive Lk p a.own k w.2.2.filled s) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s w.2.2.filled :=
  goodW_att h hg Sd u ha (liveFits_at_head h hg ha) (nc_at_head h ha) s _ hI hJ

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.seated_w_att
#print axioms ProofFile.Honest.K9.stretches_att
#print axioms ProofFile.Honest.K9.goodW_att_plan
