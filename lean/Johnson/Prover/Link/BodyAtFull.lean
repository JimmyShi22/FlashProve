-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyAtFull.lean: THE TWO FACTS THAT RIDE BESIDE THE INVARIANT, MET IN FRONT OF
THE FIRST STAGE AT THE FULL SIZE: the declared rounds behind "BAT" ask just bodyAll's sorts
(SortsFrom: public, by the kernel), and at every run the draws from round 6 on fit them (FitFrom).
Statements and proofs.

  decls_test     (general in P) the chain's declared rounds are the six front blocks' and then the
                 test's, which are laidOf's
  fr_sortsL      SortsFrom at the full size
  forall₂_get    two lists in a relation, entry by entry
  fitFrom_run    FitFrom (the run's draws) ((laidOf (p12Of frP)).drop 1) 6, at every ρ

LIMITS RAISED: set_option maxRecDepth at the one closed fact (decide +kernel), as the library does
at this size.
By: flat_split | decls_split's kin (FormWalks.lean) · the library's k12_rounds · roundFits_run
(ChainRounds.lean) · fr_isOf2 | fr_nz (ChainAtFull.lean) · ltE_drawnSL (ViewWords.lean).
Not shown here. Nothing on a decision, on soundness or on what any value discloses or does not
disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodySorts
import Johnson.Prover.Link.LinkAtFull
import Johnson.Prover.Link.LinkView
import Johnson.Prover.Link.FormWalks
import Johnson.Prover.Link.ChainAtFull
import Johnson.Desc.K12.Law.StepGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of frP linkDeclaredRounds frontBlock blocksOrV testBlock linkProtocolChain)
open H2K.JointK (laidOf)
open OnBytes.Flat (dsFull)
open TypedOracleCompiler.Run.PQ (RD drawnSL uL)
open _root_.Run (ckP)
open _root_.Iop (Rho)

theorem decls_test (P : P15) (hp : (proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).planOk = true) :
    linkDeclaredRounds P =
      (frontBlock P :: blocksOrV P).flatMap (·.rounds) ++ (laidOf (p12Of P)).map (·.1) := by
  unfold linkDeclaredRounds
  rw [flat_split, List.flatMap_append, List.flatMap_map]
  show _ ++ ((proximityTestKind guardedProximityTestParts (p12Of P) : Block T12 Unit).rounds ++ ([] ++ [])) = _
  rw [H2K.Sw.k12_rounds guardedProximityTestParts (p12Of P) hp, List.append_nil, List.append_nil]

set_option maxRecDepth 100000 in
theorem fr_sortsL : SortsFrom ((laidOf (p12Of frP)).drop 1) frFirst frRest := by
  unfold SortsFrom
  decide +kernel

theorem forall₂_get {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ (i : ℕ) (a : α), l₁[i]? = some a → ∃ b, l₂[i]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons h _, 0, a, e => by
    cases e
    exact ⟨_, rfl, h⟩
  | _, _, .cons _ t, i + 1, a, e => forall₂_get t i a e

/-- **At every run the draws from round 6 on fit the rounds behind "BAT".** -/
theorem fitFrom_run (ρ : Rho (uL (ckP .two) dsFull)) :
    FitFrom (drawsOf (drawnSL (ckP .two) dsFull ρ)) ((laidOf (p12Of frP)).drop 1) 6 :=
  fun n d hd => by
    obtain ⟨_, _, h5⟩ := decls_split frP plan_full.1
    have hdec : (linkDeclaredRounds frP)[6 + n]? = some d.1 := by
      rw [decls_test frP (_root_.Desc.K15.test_planOk frP _ _ (_root_.Desc.K15.descV_planOk frP _ _
        _root_.Desc.K15.planOk_full)), List.getElem?_append_right (by rw [h5]; omega), h5,
        List.getElem?_map]
      rw [List.getElem?_drop] at hd
      have e : 6 + n - 5 = 1 + n := by omega
      rw [e, hd]
      rfl
    obtain ⟨Dn, hDn, hR⟩ := forall₂_get (roundFits_run (linkDeclaredRounds frP) dsFull fr_isOf2 fr_nz ρ)
      (6 + n) d.1 hdec
    have e : drawsOf (drawnSL (ckP .two) dsFull ρ) (6 + n) = Dn := by
      unfold drawsOf
      rw [List.getD_eq_getElem?_getD, hDn]
      rfl
    rw [e]
    exact ⟨hR, ltE_drawnSL dsFull ρ Dn (List.mem_of_getElem? hDn)⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.fitFrom_run
#print axioms Johnson.Prover.Link.decls_test
#print axioms Johnson.Prover.Link.fr_sortsL
#print axioms Johnson.Prover.Link.forall₂_get
