-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupOpenItemsRidePastTheDigits.lean: the kind "lookup" (K3):
the debt `RidesPastS` (Honest/Thread/PaysS.lean) at the border in front of each of the 25 lookups on
the digits, at the first chain's thread of `lettersHead` (Honest/Thread/FirstHead.lean) with "keeps"
by the place's kind (`kpBy f`), gathered item by item. One theorem and one lemma.

What is shown.
  `weightsSentenceIsEmptyOffTheHead`: off link 24 the sentence on the weights holds.
  `lookupOpenItemsRidePastTheDigits`: **`RidesPastS` at `borderOf l true`, l < 25.**

Hypotheses that remain.
  `atHead`: `P5J.AtMgA` at the hash function `secondHashFunction`. `linkBelow`: l < 25.
  `saidGivesWordsBelowThePrime`: the letter `Said` gives `SaidOk`.
  Three arrows on the letter f at the kind K3: `keepsGivesTheLookupClause`,
  `keepsGivesTheFormsTestsBehind`, `keepsGivesThatTheReadersStay`.
  Every other letter of the thread is free.

How the proof goes. `openItemIsSortedAtTheDigits` sorts the items that ride past. The plain ones go by
`plainItemRidesPast`, the link's `wo` by `pendingRowSentenceRidesPastTheDigits`, the link's `forms` by
`formsItemRidesPastTheDigits`. That last asks that the sentence on the weights pass: at link 24 by
`weightsSentenceGoesOnPastTheHeadsDigits`; at the other links the sentence is empty. `ridesPastS_shares`
joins the items.

Limits. An implication: `RidesPastS` is a step law from the invariant, and nothing here shows that
the invariant holds at any run. At the full size alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupFormsRidePastTheDigits
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupPlainItemsRidePast
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupPendingRowRidesPast
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupWeightsGoOn
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupReadersStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain Place Strs KindName)
open VerifiableInference.Desc.First (Item Pub pubOfItems)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K3.Law.AtThr

-- the closed lists are not unfolded
attribute [local irreducible] IM.openAt VerifiableInference.Desc.First.flatPlacesOf

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-- Off link 24 the sentence on the weights holds, since it begins "the link is 24". Conditional on
the head and on the link. -/
theorem weightsSentenceIsEmptyOffTheHead {l : Nat} (notTheHead : l ≠ 24)
    (statement : ProofFile.InstPub × TS) (y : Strs) (v : WtF) : atHead.𝔇.wt l statement y v := by
  show VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6 (P5J.At.cs Zp)
      (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0 l statement y v
  intro isTheHeadsLink
  exact absurd isTheHeadsLink notTheHead

/-- **`RidesPastS` AT THE BORDER OF EVERY LOOKUP ON THE DIGITS.** Conditional on what this file's head
lists. -/
theorem lookupOpenItemsRidePastTheDigits
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat}
    (linkBelow : l < 25)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t')
    (keepsGivesTheFormsTestsBehind : ∀ t t', f .K3 (IM.k3Place l true) t t' →
      ∀ q ∈ pubOfItems (IM.openAt P5J.At.links P5J.At.ps
          (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true)) + 1)),
        VerifiableInference.Desc.K9.pubForms atHead.𝔇.pubD.Rd atHead.𝔇.pubD.runs atHead.𝔇.pubD.ah
          atHead.𝔇.pubD.N (fun _ (_ : Unit × TS) => true) q ((), t') = true)
    (keepsGivesThatTheReadersStay : ∀ t t', f .K3 (IM.k3Place l true) t t' → ∀ mm kk ρ,
      Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps
        (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true))) →
      Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps
        (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true)) + 1) →
      ∀ q ∈ atHead.𝔇.pubD.runs mm kk ρ,
        VerifiableInference.Reads.Pass.Fwd (atHead.𝔇.pubD.Rd mm) q.1 q.2 t t') :
    RidesPastS (LK).thread Said (borderOf l true) := by
  have borderIs := borderOfTheDigitsPlace linkBelow
  refine ridesPastS_shares _ _ fun i opened notShut notOwed => ?_
  rcases openItemIsSortedAtTheDigits linkBelow opened notShut notOwed with
    plain | rfl | ⟨kk, ρ, rfl, inFront, behind⟩
  · exact plainItemRidesPast atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said
      keepsGivesTheLookupClause linkBelow true plain
  · exact pendingRowSentenceRidesPastTheDigits atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said
      keepsGivesTheLookupClause linkBelow l
  · refine formsItemRidesPastTheDigits atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said linkBelow
      keepsGivesTheLookupClause keepsGivesTheFormsTestsBehind keepsGivesThatTheReadersStay
      (by rw [borderIs]; exact inFront) (by rw [borderIs]; exact behind) ?_
    intro _ k s m E s' y y' v invariant kept said
    by_cases isTheHead : l = 24
    · subst isTheHead
      exact weightsSentenceGoesOnPastTheHeadsDigits atHead H Q test carryX item n₁ n₂ b₀ Vd Rd f w
        Said saidGivesWordsBelowThePrime keepsGivesTheLookupClause invariant kept y y' v said
    · exact weightsSentenceIsEmptyOffTheHead atHead isTheHead _ y' v

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.weightsSentenceIsEmptyOffTheHead
#print axioms ProofFile.Honest.K3.Term.lookupOpenItemsRidePastTheDigits
