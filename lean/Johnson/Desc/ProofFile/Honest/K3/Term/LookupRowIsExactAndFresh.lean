-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupRowIsExactAndFresh.lean: AT ANY FILLING. The kind
"lookup" (K3): the two sentences `ExactK3` and `FreshK3` (Honest/K3/Law/Good/K3ExactStated.lean),
proved. Two theorems; no definition. A join by cases on the member, of laws at one member that other
files hold. No new equation between two distributions is proved here.

  `lookupRowIsExact`   ExactK3 φ chain firstTree A s bs fs
  `lookupRowIsFresh`   FreshK3 φ Bk ord A s bs fs
The face, the book, the order of places, the chain's number and its first tree, the filling, the
site, the list of sub-protocols and the falls are variables.

What is called. At a stage with a sumcheck: `lookupMemberAtSumcheckStage`, then
`exact_sumPart_field` (Honest/SumLaw/SumExact.lean), at the lens (fun _ => (), A.wit s, fun _ => (),
fun y _ => y). At a stage that sends nothing: `lookupMemberAtQuietStage`, then
`quietPart_exact_lift` (Honest/Small/Quiet.lean). For the second sentence: `fresh_of_nil`
(Honest/Law/ToyLaw.lean), by one term at every member.

What the two sentences are.
  * On and bud are "true" in both. They are hypotheses of the field `exact` of `Good`
    (Honest/Side.lean), so this is that field's strongest form: the equation holds at every state,
    every `front` that agrees with it on the rounds seen, and every list of positions.
  * The first sentence is THE SPENDER'S HALF ALONE, as the head of Honest/SumLaw/SumExact.lean says:
    the two blocks of coins that a part spends are taken as uniform and independent of all that is
    fixed. That they are so in a run is the field `fresh` at the parts that own them. These are no
    parts of a lookup.
  * The second sentence is TRUE AND EMPTY. A lookup's parts take no coin of their own, so under its
    premise (by the book no part spends a coin of a lookup's part) both sides are one law.

What may be said of the two sentences is not this file's to say. The
limits of the laws that are called are in the heads of the files that hold them.

The sites of a public part (`lookSites`) are PLACES OF THE PROOF FILE ALONE (fifty under the
library's hypothesis at the full size): THE KEY FILE'S TWO LOOKUPS ARE NOT SPOKEN OF.

Limits. Conditional: the first on `RowStated`, the second on `OwnsNone`. Neither premise is shown
here at any site or book. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact
import Johnson.Desc.ProofFile.Honest.Small.Quiet
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3ExactStated
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupMemberWrittenOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Place)
open ProofFile.Honest.SumLaw (exact_sumPart_field)
open ProofFile.Honest.Small (ExactMember FreshMember quietPart_exact_lift)
open ProofFile.Honest.K3.Law

variable {S Cl V W X Pb : Type}

/-- **The field `exact` at the lookup's row**, at On and bud "true". The spender's half alone.
Conditional, inside `ExactK3`, on the side and on `RowStated`. -/
theorem lookupRowIsExact (φ : Face V W Pb) (chain firstTree : Nat) (A : Fill W) (s : Site)
    (bs : List (Block S Cl)) (fs : List (Fall S)) :
    ExactK3 (X := X) φ chain firstTree A s bs fs := by
  intro σ seated stated u member
  obtain ⟨stage, atNumber, cases⟩ := lookupMemberHasStage A s bs fs σ seated u member
  rcases cases with ⟨call, hasCall⟩ | noCall
  · obtain ⟨h1, h2, h3⟩ := stated.sums u member stage call atNumber hasCall
    rw [lookupMemberAtSumcheckStage A s bs fs σ seated u member stage call atNumber hasCall]
    exact exact_sumPart_field φ σ chain firstTree _ _ (fun _ => ()) (A.wit s) (fun _ => ())
      (fun y _ => y) (fun _ _ => rfl) (fun _ => rfl) _ _
      (jobOf theReads (A.jobs s).asked s.at_ stage call) h1 u.rounds h2 h3 u.number _
  · have h1 := stated.quiets u member stage atNumber noCall
    rw [lookupMemberAtQuietStage A s bs fs σ seated u member stage atNumber noCall]
    exact quietPart_exact_lift φ σ chain firstTree _ _ u.number 1 u.rounds _ (fun _ => ())
      (A.wit s) (fun _ => ()) (fun y _ => y) h1

/-- **The field `fresh` at the lookup's row.** True and empty: a lookup's parts own no coin.
Conditional, inside `FreshK3`, on the side and on `OwnsNone`. -/
theorem lookupRowIsFresh (φ : Face V W Pb) (Bk : ProverCoinCounts) (ord : List Place) (A : Fill W) (s : Site)
    (bs : List (Block S Cl)) (fs : List (Fall S)) : FreshK3 (X := X) φ Bk ord A s bs fs :=
  fun σ _ ownsNone u member p sp ca m ds asks _ _ _ =>
    fresh_of_nil (Bk.spentBy ⟨σ.block.place, u.number⟩ p) (ownsNone u member p)
      (fun c => σ.shows φ u (c, sp, ca) m ds asks)
      fun c => cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupRowIsExact
#print axioms ProofFile.Honest.K3.Term.lookupRowIsFresh
