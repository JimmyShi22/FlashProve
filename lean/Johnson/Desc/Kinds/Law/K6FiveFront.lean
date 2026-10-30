-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6FiveFront.lean: AN ACCEPTING DECISION OF EACH OF THE FIVE MEMBERS THAT
STAND BETWEEN THE OUTPUT HEAD's OWN ROUNDS AND THE HEAD's BATCHING LEAVES WHAT THE HEAD HAS HEARD AS
IT WAS, AND, WHERE THE LEDGER HAS ITS SIZES, HANDS ON A LATER ONE. One theorem ON THE VERIFIER's
TEXT, over the library alone; no prover is in this file, and no goal is stated.

  `five_decide_frontLater`   **at each number i from 342 to 346 of the first chain's flat list: the
                    member that stands there decides `FrontLater`**
                    (Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean): from the state in front to
                    the state behind, what `AlikeFront` compares beside the ledger stays, and the
                    ledger, where it has its sizes, is a later one

Why. The library walks these five BACKWARD: from a state reached in front of the batching it finds
some reached state behind the head's own rounds (`frontLater_back_head`, same file). A fact that
hangs on the very samples of a run cannot be carried so: the state that the walk finds is bound
inside its "there is". Read forward, member by member, the same five accepts carry such a fact from
the state at which it stands to the next.

Limits. CONDITIONAL: the scope (hS, hR), the opening `IM.Open`, and hp: every member of the flat
list passes its test on the plan. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE: the scope binds
the one, the opening stands at `OnBytes.secondHashFunction`. ON THE DECISIONS ALONE: nothing on the runs of
claims. No "reached" is asked, and none is shown. Nothing at another number. THE PROOF IS THE
LIBRARY's OWN FIVE BLOCKS OF `frontLater_back_head`, each taken in that proof's letters: the reads'
sending (342), the smallness test's hearing (343), the digits' sending (344), the lookup on the
digits (345), the merge (346). Called: `alone_decides`, `flat_at` (Johnson/K11R/MaskSeat.lean), in
the manner of `seated_five` (Johnson/K11R/LeavesAt346.lean); `k1Reads_frontLater`, `k8_frontLater`,
`k1Later_frontLater`, `k11_frontLater` (K6HeardAtBatch.lean); `k3Digits_front`
(Johnson/Desc/First/Link/Law/FrontStays.lean), `later_behind_digits` (LaterStretch.lean there),
`piece_digits` (FourAtBatch.lean there), `k8Ix`, `k8_kind_at` (StretchBack.lean there);
`IM.k1_reads_of`, `IM.k8_alone`, `IM.k1_digits_of`, `IM.k3_of`, `IM.k11_of`, `IM.subs_scope`,
`IM.alone_planOk`.
Nothing on any property.

-/
import Johnson.Desc.First.Link.Law.K6HeardAtBatch
import Johnson.K11R.MaskSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Five
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.First.MergeLaw (alone_decides flat_at)
open VerifiableInference.Desc.LinkJoin

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AN ACCEPTING DECISION OF EACH OF THE FIVE MEMBERS BETWEEN THE OUTPUT HEAD's OWN ROUNDS AND THE
HEAD's BATCHING (numbers 342 to 346 of the first chain's flat list) GIVES `FrontLater`.** The five
blocks of `frontLater_back_head` (Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean), read forward: no
"reached" is asked. -/
theorem five_decide_frontLater (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {i : ℕ} (h1 : 342 ≤ i) (h2 : i < 347)
    {blk : Block S ProofFile.Cl} (hb : c.blocksInOrder[i]? = some blk) : Decides FrontLater blk := by
  interval_cases i
  · -- 342: the reads' sending
    obtain ⟨Lk0, b0, X0, pd, reads0, digits0, m1, m2, _, _, m4⟩ :=
      IM.k1_reads_of hS hR O 24 (by omega)
    obtain rfl : b0 = blk := Option.some.inj ((flat_at hS hR O m1 m2 rfl).symm.trans hb)
    exact alone_decides (by intro k; cases k) m4
      (fun s rs gs t hd => k1Reads_frontLater _ _ _ _ _ _ s rs gs t hd)
  · -- 343: the smallness test's hearing
    obtain ⟨Lk8, b8, X8, k1, k2, _, _, k4⟩ := IM.k8_alone O 24 (IM.subAt 24)
      (IM.subs_scope hS hR O 24 (by omega)) (k8Ix 24) (k8_kind_at 24) (by decide)
    obtain rfl : b8 = blk := Option.some.inj ((flat_at hS hR O k1 k2 rfl).symm.trans hb)
    exact alone_decides (by intro k; cases k) k4 (k8_frontLater _)
  · -- 344: the digits' sending
    obtain ⟨Lk1, b1, Xl, pr, reads, digits, g1, g2, _, _, g4⟩ :=
      IM.k1_digits_of hS hR O 24 (by omega)
    obtain rfl : b1 = blk := Option.some.inj ((flat_at hS hR O g1 g2 rfl).symm.trans hb)
    exact alone_decides (by intro k; cases k) g4
      (fun s rs gs t hd => k1Later_frontLater _ _ _ _ _ _ s rs gs t hd)
  · -- 345: the lookup on the digits
    obtain ⟨Lk3, b3, b3', f1, f2, f3, f4⟩ := IM.k3_of hS hR O 24 (by omega) true
    have hf3 : c.blocksInOrder[345]? = some b3 := flat_at hS hR O f1 f2 rfl
    have hOk3 : b3'.planOk = true := by
      rw [← IM.alone_planOk f4]
      exact hp b3 (List.mem_of_getElem? hf3)
    have h7 : 7 ≤ (IM.k3Place 24 true).piece := by decide
    have hpc := piece_digits _ _ _ _ _ _ b3' f3 24 rfl h7
    obtain rfl : b3 = blk := Option.some.inj (hf3.symm.trans hb)
    exact alone_decides (by intro k; cases k) f4
      (fun s rs gs t hd => ⟨k3Digits_front _ _ _ _ _ _ b3' f3 hOk3 24 rfl hpc s rs gs t hd,
        fun G hG hz => later_behind_digits _ _ _ _ _ _ b3' f3 hOk3 24 rfl hpc s t rs gs hd hG hz⟩)
  · -- 346: the merge
    obtain ⟨Lk, b, e1, e2, e4, _⟩ := IM.k11_of hS hR O
    obtain rfl : b = blk := Option.some.inj ((flat_at hS hR O e1 e2 rfl).symm.trans hb)
    exact fun s rs gs s' hd => (alone_decides (by intro k; cases k) e4
      (fun s rs gs s' hd => k11_frontLater _ s rs gs s' hd) s rs gs s' hd).1

end VerifiableInference.Desc.Kinds.Head.Law.Five

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Five.five_decide_frontLater
