-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/AtDescription.lean: at the description that the release's goal statements use
(VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription), at all public files in scope, there is a family T at which
the four clauses about one and the same scheme (MeetsRoad, Bundle.lean) follow from the hypothesis
Spec.frontPrivacyAt and from LeftToAsk: premises on the honest sides, the map from weights, the
encoder and the relation Rel. Conditional, no member known, of a shell. Not one of the release's
goal statements. The premises on the public reading, on the verifier and on the key's code are
theorems there. FrontProof.lean proves the hypothesis (Joined.lean drops it).
Terms and the limits that go with any quote: Spec.lean.

What this file has. Both theorems have the hypothesis Spec.frontPrivacyAt, a named proposition
(proved as frontPrivacyAt in FrontProof.lean, which this file does not import; without the
hypothesis: Joined.lean).
  LeftToAsk   the nine premises that are left: over one F at every d, PremAll and ZetaLe (the
      premises of index privacy and one bound, PremAt.lean) and HonAll and AlphaLe (the same for
      completeness, HonAt.lean); UndoOn (Complete.lean); every weight's index is in the range ok;
      what Bundle.lean requires of Rel; the bounds NC and NP on the two counts of typed queries.
  meetsRoad_of_laws   At any description D, public files in scope and a family T with FamilyLaws
      (AtBuiltMore.lean): LeftToAsk gives MeetsRoad at α, 8 + NC * (K + 1) + 1, NP * (K + 1) and ζ.
      FamilyLaws gives the premises of meetsRoad_of on the reading, fits (fits_of_eq, FitsOf.lean),
      reads, "every key with a told part has a code", and at most 8 queries of the reading. A typed
      answer has at most K + 1 blocks under every coding: a round's answer is K digests and one more
      (blocks_le, Blocks.lean).
  meetsRoad_description   At VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription: for all public files Z in scope
      there are c₀, m₀, T and pair with FamilyLaws (hasFamilyLaws_description) such that, for all
      honest sides F, all G : FallsAt F, relations, encoders and numbers, LeftToAsk gives MeetsRoad.

Limits. Here the clause on index privacy rests on the hypothesis.
No honest side with the protocol's three provers is written in Lean. No member of HonAll is known,
and none of PremAll and HonAll together: the theorems may apply to nothing. Of PremAll by itself a
member with two placeholder provers, which send fixed messages, is known, at the built description
with the number of the committer's coins set anew (premAll_laid, LaidAll.lean).
The parser, the encoder, the map from weights to indices and Rel are variables. Yes is a variable
too, and Rel is required to imply it, not the converse: a Rel that holds of nothing satisfies that,
and then the clause on index privacy speaks of the key only.
Whether UndoOn holds at the description's own form and parser is not proved. There is no clause on
index binding, and no number but 8 and K + 1. All limits of Bundle.lean hold.
-/
import Johnson.FrontRoad.Bundle
import Johnson.FrontRoad.FitsOf
import Johnson.FrontRoad.AtBuiltMore
import Johnson.FrontRoad.Blocks

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What is left to require, at a family T over the description D at the public files Z, of honest
sides F with G : FallsAt F, a map from weights to indices, an encoder with its parser, the relation
Rel, and numbers. -/
structure LeftToAsk (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (F : SidesAt T) (G : FallsAt F)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (back : (D.input Z c₀ m₀).Instance → List Token × List Token) {Form : Type}
    (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) {PP' : Type}
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) (ok : (D.input Z c₀ m₀).Index → Prop)
    (α : ℝ≥0∞) (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP : ℕ) : Prop where
  prem : PremAll F ok Yes fun _ => True
  zeta : ZetaLe F (fun _ => True) ζ
  hon : HonAll G Yes fun _ => True
  alpha : AlphaLe G (fun _ => True) α
  undo : UndoOn D Z c₀ m₀ T F.side idx Yes parse encF
  range : ∀ w, ok (idx w)
  tie : ∀ w x', Rel.rel w x' () →
    ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ Yes (idx w) x ∧ back x = x'
  commits : ∀ d, commitN (D.input Z c₀ m₀).queryLayout (F.side d) ≤ NC
  proves : ∀ d, proveN (D.input Z c₀ m₀).queryLayout (F.side d) ≤ NP

/-- At any description, public files in scope and a family T with FamilyLaws, LeftToAsk gives
MeetsRoad, from the hypothesis H (Spec.frontPrivacyAt, the statement of index privacy at the shell
frontAt), which is not proved here (without it: meetsRoad_laws_joined, Joined.lean). Conditional, no
member known, of a shell. -/
theorem meetsRoad_of_laws (H : Spec.frontPrivacyAt) (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope Z = true) (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (pair : Digest → D.More → T.D) (hL : FamilyLaws D Z c₀ m₀ T pair) (F : SidesAt T)
    (G : FallsAt F) (s : IntegerTransformer.Settings)
    (idx : ModelWeights s → (D.input Z c₀ m₀).Index) (x₀ : (D.input Z c₀ m₀).Instance)
    (back : (D.input Z c₀ m₀).Instance → List Token × List Token) (Form : Type)
    (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) (PP' : Type)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) (ok : (D.input Z c₀ m₀).Index → Prop)
    (α : ℝ≥0∞) (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP : ℕ)
    (h : LeftToAsk D Z c₀ m₀ T F G s idx back parse encF Rel Yes ok α ζ NC NP) :
    MeetsRoad D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel α
      (8 + NC * ((D.input Z c₀ m₀).queryLayout.K + 1) + 1) (NP * ((D.input Z c₀ m₀).queryLayout.K + 1)) ζ :=
  meetsRoad_of D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel H G Yes ok α ζ 8
    ((D.input Z c₀ m₀).queryLayout.K + 1) NC NP pair
    h.prem h.zeta h.hon h.alpha hL.noCoin hL.asks hL.once hL.spare
    (fits_of_eq D Z c₀ m₀ T pair hL.eq) hL.reads scope h.undo hL.total h.range h.tie hL.eight
    (fun d o => blocks_le (T.m d) (by norm_num) o) h.commits h.proves

/-- At the description that the release's goal statements use and all public files in scope, there
is a family T with FamilyLaws at which LeftToAsk gives MeetsRoad, from the hypothesis H
(Spec.frontPrivacyAt), which is not proved here (without it: meetsRoad_description_joined,
Joined.lean). Conditional, no member known, of a shell. -/
theorem meetsRoad_description (H : Spec.frontPrivacyAt) (Z : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope Z = true) :
    ∃ (c₀ : Digest) (m₀ : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More)
      (T : LayoutsByPublicReading ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀))
      (pair : Digest → (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More → T.D),
      FamilyLaws (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription) Z c₀ m₀ T pair ∧
        ∀ (F : SidesAt T) (G : FallsAt F) (s : IntegerTransformer.Settings)
          (idx : ModelWeights s → ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).Index)
          (x₀ : ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).Instance)
          (back : ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).Instance →
            List Token × List Token)
          (Form : Type) (parse : VerifierAndGoals.Parser (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription) Z Form)
          (encF : VerifierAndGoals.TypedProof ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).F Z)
            ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).P Z) → Form)
          (PP' : Type)
          (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
          (Yes : ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).Index →
            ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).Instance → Prop)
          (ok : ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).Index → Prop) (α : ℝ≥0∞)
          (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP : ℕ),
          LeftToAsk (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription) Z c₀ m₀ T F G s idx back parse encF Rel
              Yes ok α ζ NC NP →
            MeetsRoad (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription) Z c₀ m₀ T F s idx x₀ back Form parse
              encF Rel α
              (8 + NC * (((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).queryLayout.K + 1) + 1)
              (NP * (((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).queryLayout.K + 1)) ζ := by
  obtain ⟨c₀, m₀, T, pair, hL⟩ := hasFamilyLaws_description Z
  exact ⟨c₀, m₀, T, pair, hL, fun F G s idx x₀ back Form parse encF PP' Rel Yes ok α ζ NC NP h =>
    meetsRoad_of_laws H _ Z scope c₀ m₀ T pair hL F G s idx x₀ back Form parse encF PP' Rel Yes ok
      α ζ NC NP h⟩

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.meetsRoad_of_laws
#print axioms OnBytes.FrontRoad.meetsRoad_description
