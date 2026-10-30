-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SharesSmallAtTheTest.lean: CONDITIONAL.

What is here. `k4_shares_small` (Law/SharesSmall.lean) in the form of the test `shareSmall`
(E2E/TheFallsSum.lean).

  `k4_shares_pass`   `shareSmall` is true at `k4Fall`'s and `k4MarkWide`'s shares, at each member of K4
  `k4MarksWide_small`, `k4MarksWide_small_at_base`   `markSmall` at every mark of the written list

Limits. A statement on two numbers, under the head: nothing on what the tests say at a run, or on
whether a stated share is the chance of its event.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SharesSmall
import Johnson.Desc.ProofFile.Honest.K4.Law.K4MarksWide
import Johnson.Desc.ProofFile.Honest.K4.Law.LaidAtGroup
import E2E.TheFallsSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block KindName)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4 laid_at)
open AtPublicFiles.TheFalls (shareSmall markSmall)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h and Lh. **K4's fall and K4's wider mark at the member pass the test on a stated
share.** A statement on two numbers: nothing on the tests at a run. -/
theorem k4_shares_pass (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {S : Type} :
    shareSmall (k4Fall (S := S) (k4PubAt cF k x)).share = true ∧
      shareSmall (k4MarkWide (k4PubAt cF k x)).share = true := by
  obtain ⟨⟨a, b⟩, c, d⟩ := k4_shares_small h Lh (S := S)
  unfold shareSmall
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨a, b⟩, c, d⟩

/-- CONDITIONAL on h and hG. **Every wider mark of the written list passes the test.** -/
theorem k4MarksWide_small (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    (k4MarksWide Zp G₀).all markSmall = true := by
  rw [List.all_eq_true]
  intro mk hm
  obtain ⟨g, hp, hg, hh, rfl⟩ := k4MarksWide_of_mem hm
  obtain ⟨x, blk, Lh⟩ := laid_at h hg
  obtain ⟨G₁, hG₁, hx⟩ := Lh.lot
  have eG : G₁ = G₀ := Option.some.inj (hG₁.symm.trans hG)
  rw [eG] at hx
  obtain ⟨eP, -, -, ehp⟩ := IM.k4_seated h.laid.pub hG hx
  rw [Lh.grp] at ehp
  have ep : x.2.hp = hp := Option.some.inj (ehp.symm.trans hh)
  have e : shareSmall (k4MarkWide ⟨x.2.P, x.2.hp, x.2.g, x.2.link, x.2.piece,
      roundsTo cF.blocksInOrder (28 * g + 4), 2 * x.2.g⟩).share = true :=
    (k4_shares_pass h Lh (S := Unit)).2
  rw [eP, Lh.grp, Lh.link, Lh.piece, ep] at e
  rw [k4MarkWide_blind G₀.W.layers hp g (2 * g) 3 0 (roundsTo cF.blocksInOrder (28 * g + 4)) (2 * g)
    (2 * g)]
  unfold markSmall
  rw [if_neg (by
    show ¬(KindName.K4 = KindName.K3 ∨ KindName.K4 = KindName.K6)
    decide)]
  exact e

/-- CONDITIONAL on h and hB. **The same at the ground of baseOf's return.** -/
theorem k4MarksWide_small_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (k4MarksWide Zp Bs.G₀).all markSmall = true := by
  obtain ⟨Bs', base, Op⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (Op.made.symm.trans hB)
  exact k4MarksWide_small h Op.blank

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_shares_pass
#print axioms ProofFile.Honest.K4.k4MarksWide_small
#print axioms ProofFile.Honest.K4.k4MarksWide_small_at_base
