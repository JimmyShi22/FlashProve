-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EntsMerge.lean: THE CLAUSE "entsMerge" OF WHAT IS FIXED IN FRONT OF THE
HEAD's BATCHING, AT EVERY STATE REACHED THERE: NO PREMISE IS LEFT BUT THE SCOPE AND "REACHED".
In the goals' scope. Statements and proofs: calls.

The clause says of wo, what the head's merge has left in the state (`woOf`, PhiAll.lean): the test
`entsAtB` says yes of the one form `wo.p.rowForm wo.fvp {}`. THAT FORM NAMES NO ENTRY. The road: one
step back from 347: the sub-protocol there is the merge, alone (`IM.k11_of`); behind its yes the
state holds the very wo that `mergeHear` returned (`decide_inv`,
Johnson/Top/H0/MergeLaw/Says.lean); of that return the sumcheck's start form is the merge's own
(`hear_ended`, MergeLaw/Said.lean: the field start); a row form over that start, with nothing kept,
names no entry (`rowForm_ents`, MergeLaw/MergeMakesForms.lean). All three are other files'.

  `merge_bare`: behind a yes of the merge's decision: what is left there has a row form without an
    entry.
  `wo_bare_at_347`: **reached at 347 ⊢ ∀ wo, woOf s = some wo →
    (wo.p.rowForm wo.fvp {}).ents = #[].**
  `entsMerge_at_347`: **the clause**, at every π, φ, nU: `EntsAt π nU (fixed9 φ s) [..]`.
Limits. The clause is met idly: there is no entry to test. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.EntsAtBatch
import Johnson.Desc.First.Link.Law.PhiAll
import Johnson.Desc.First.Link.Law.StretchBack
import Johnson.Top.H0.MergeLaw.MergeMakesForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (decide_inv hear_ended rowForm_ents)
open VerifiableInference.Desc.PhiAll (woOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)
open Johnson.Desc.First.Walk.Tied (Reach stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

/-- Behind a yes of the merge's decision. -/
theorem merge_bare {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') :
    ∀ wo, woOf s' = some wo → (wo.p.rowForm wo.fvp {}).ents = #[] := by
  obtain ⟨a, a', tp, F, claim, x, wo, _, ha', _, _, hwo, _, hm, _⟩ := decide_inv h
  obtain ⟨x₁, mu, c, beta, v, T, r1, rY, rV, qs, _, _, _, _, hE, _⟩ := hear_ended hm
  intro wo' e
  unfold woOf at e
  rw [ha'] at e
  obtain rfl : wo = wo' := Option.some.inj (hwo.symm.trans e)
  apply Array.toList_inj.1
  exact rowForm_ents wo.p wo.fvp #[x.sV] _ hE.start

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **IN FRONT OF THE HEAD's BATCHING.** -/
theorem wo_bare_at_347 (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∀ wo, woOf s' = some wo → (wo.p.rowForm wo.fvp {}).ents = #[] := by
  obtain ⟨z', s, s'', b₀, e, _, hb, hy⟩ := reach_pred (k := 346) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, e1, e2, e4, _⟩ := IM.k11_of hS hR O
  have hfl : c.blocksInOrder[346]? = some b := by
    have := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 8] at this
    exact this
  obtain rfl : b = b₀ := Option.some.inj (hfl.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' : headMergeDecide (K11.parOf Z Bs.G₀) s rs = .ok s' := ((IM.k11_yes e4 _ _ _ _).1 hd).1
  exact merge_bare hd'

/-- **THE CLAUSE entsMerge.** -/
theorem entsMerge_at_347 (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) {α : Type}
    (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (nU : Array ℕ) :
    ∀ wo, woOf s' = some wo → EntsAt π nU (fixed9 φ s') [wo.p.rowForm wo.fvp {}] :=
  fun wo e => ents_nil π fun f hf => by
    rw [List.mem_singleton.1 hf]
    exact wo_bare_at_347 hS hR O h wo e

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.merge_bare
#print axioms VerifiableInference.Desc.LinkJoin.wo_bare_at_347
#print axioms VerifiableInference.Desc.LinkJoin.entsMerge_at_347
