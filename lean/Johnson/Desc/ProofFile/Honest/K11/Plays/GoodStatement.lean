-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/GoodStatement.lean: THE FRAME's `Good` (Honest/Side.lean) AT
THE SIDE OF THE MERGE OF THE CLAIMS ON THE WEIGHTS, UNDER ONE PREMISE ON THE SUMCHECK's PART AND ONE
ON THE BOOK: STATEMENTS ALONE: one definition that is needed, and two definitions of propositions.
NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they are lemmas'
statements. WHAT FOLLOWS FROM `Good` IS NOT SAID HERE.

The side σ, the face, the book, the order of places, the chain's two numbers and the declared rounds
whose reads are handed (pre) are variables. What is spent of σ is two named premises: its
sub-protocol is the kind's block as it stands alone at a seat AT THE KIND's OWN PLACE; its row is
the kind's (`headMergeSided`, Honest/K11/Part.lean).

  `ExactAtOne`      the field exact of `Good`, at On := True and bud := True, AT ONE MEMBER u,
                    WITHOUT THE FIELD's HYPOTHESIS ON THE COLUMNS HANDED (m.opened = …): SO IT ASKS
                    MORE THAN THE FIELD, AND NAMES NO pre: A FURTHER TEXT of `Small.ExactMember`
                    (Honest/Small/Field.lean) at these two: the tie: ExactAtOneIs.lean of this
                    folder
  `HeadMergeFits`   under the two premises on σ: the field fits: σ.fits = true
  `HeadMergeGood`   under these two, and
                      unspent: no entry of the book lets any part spend a coin of a part of this row
                        (both parts take no coin of their own);
                      sum: `ExactAtOne` at the row's member number 1: THE SUMCHECK's PART, LIFTED
                        (`headMergeSum`, Honest/K11/Part.lean: `sumPart` under `Part.lift`):
                    `Good pre φ σ Bk ord chain firstTree A' B' On bud` at every pre, at
                    A' := B' := False, On := True, bud := True

What the lemma itself brings: fits; exact at the row's member number 0, which sends nothing, by a
law on such a member (Honest/Small/Quiet.lean); fresh at both members, from the premise on the book,
by the frame's own lemma. plays and acc hold from False: nothing is shown by them.

Limits. The four premises are shown at no side and no book. sum is the weight of exact: it is not
shown here: so of exact this lemma shows the quiet member's share alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Part
import Johnson.Desc.K11.Returns.SeatStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Claim Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)

/-- The field exact of `Good`, at On := True and bud := True, at one member, without the field's
hypothesis on the columns handed. -/
def ExactAtOne {St Cl V W X Pb : Type} (φ : Face V W Pb) (σ : Side St Cl V W X Pb)
    (chain firstTree : Nat) (u : Member V W X Pb) : Prop :=
  ∀ ca m front ds asks, m.seen = front.seen → drawsFit (u.rounds.map (·.1)) ds = true →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks

/-- The statement on the field fits. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadMergeFits : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (σ : Side S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String),
    σ.block = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name (headMergePlace P) →
    σ.row = headMergeSided P claims weights → σ.fits = true

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. pre is tied to
no description; at each pre this says no more than its premise `ExactAtOne` gives. -/
def HeadMergeGood : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (σ : Side S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (name : String),
    σ.block = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name (headMergePlace P) →
    σ.row = headMergeSided P claims weights →
    (∀ j q, Bk.spentBy ⟨σ.block.place, j⟩ q = []) →
    (∀ u ∈ σ.members, u.number = 1 → ExactAtOne φ σ chain firstTree u) →
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ _ => True)

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.ExactAtOne
#print axioms ProofFile.Honest.K11.HeadMergeFits
#print axioms ProofFile.Honest.K11.HeadMergeGood
