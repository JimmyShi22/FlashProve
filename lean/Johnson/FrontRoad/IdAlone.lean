-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/IdAlone.lean: three of the four clauses on the scheme whose key is the commitment
ID alone (frontId) follow from the premises of index privacy alone, with no premise on completeness.
Conditional, of a shell.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
threeOfId_of_laws: let T be a family of inputs over the values d of the public reading of a
description D, with the properties FamilyLaws (Johnson/FrontRoad/AtBuiltMore.lean). Let F give, for
every d, an honest side and simulators that satisfy the premises of index privacy (PremAll,
Johnson/FrontRoad/PremAt.lean) with an error of at most ζ (ZetaLe). Let every index that comes from
weights lie in the range ok, and let every request that the relation Rel calls true build an
instance, with no further tokens, that Yes calls true and from which the request can be read back.
Let NC and NP bound commitN and proveN (Johnson/WholeKey/Work.lean) at every d. Then the scheme
frontId (Johnson/FrontRoad/FrontId.lean) at the honest sides of F satisfies ThreeOfId at asked = 8
+ NC · (K + 1) + 1 and askedEach = NP · (K + 1).

  ThreeOfId   three clauses about the one scheme frontId. verifier: its verifier is the verifier of
      the argument system that Ladder.lean builds from D. within: its committer makes at most asked
      calls of the hash function on every path, and its prover at most askedEach. privacy: index
      privacy in the stronger of the library's two forms (ZKCP.HasStrongIndexPrivacyWith), at all
      weights, with the explicit simulator frontSimK, at ζ at one query more.
  threeOfId_of_meetsId   the four clauses of MeetsId (Johnson/FrontRoad/Joined.lean) give these
      three: ThreeOfId is MeetsId without its clause on completeness.

How it fits. meetsId_joined (Johnson/FrontRoad/Joined.lean) proves four clauses from the premises of
index privacy and of completeness together. No honest side is known that satisfies both. Parameters
that satisfy the premises of index privacy alone are known, with two placeholder provers, which send
fixed messages (Johnson/FrontRoad/LaidAll.lean), and this file is the form of the theorem that can
be applied to them. Not one of the release's goal statements.

Limits.
  There is no clause on completeness. Index privacy does not read a scheme's verifier, so the clause
      verifier holds by definition, whatever the committer and the prover do. What connects them to
      that verifier is completeness of the same scheme. Without it these three clauses are satisfied
      by placeholder provers, which send fixed messages (see Johnson/FrontRoad/Spec.lean on this).
  The committer and the prover of frontId are this folder's, not the fields commit and prove of D.
  The premises are asked at every d of the type T.D, whether some hash function gives that d or not.
  Yes, Rel and ζ are variables: a Rel that holds of nothing satisfies the premise on Rel, and then
      no proof is in the view.
  All limits of Johnson/FrontRoad/FrontId.lean, Johnson/FrontRoad/PremAt.lean and
      Johnson/FrontRoad/Joined.lean hold here too.
-/
import Johnson.FrontRoad.Joined

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (F : SidesAt T) (s : IntegerTransformer.Settings)
  (idx : ModelWeights s → (D.input Z c₀ m₀).Index) (x₀ : (D.input Z c₀ m₀).Instance)
  (back : (D.input Z c₀ m₀).Instance → List Token × List Token) (Form : Type)
  (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) {PP' : Type}
  (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')

/-- Three of the four clauses of MeetsId (Johnson/FrontRoad/Joined.lean) about the scheme that
publishes the commitment ID alone: all but completeness. -/
structure ThreeOfId (asked askedEach : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  verifier : ∀ prove : ModelWeights s → D.Rand → List Token → List Token →
      RandomizedAlgorithm Form,
    (frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF).V =
      (VerifierAndGoals.system D Z s Form prove parse).uploadArgument.V
  within : (∀ w, ((frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF).C w).QueryBound asked) ∧
    ∀ isk x', ((frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF).P isk x' ()).QueryBound
      askedEach
  privacy : ZKCP.HasStrongIndexPrivacyWith Rel
    (frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF)
    (frontSimK T x₀ back (fun id _ => id) (fun k π => encF ([], (lowKey k, lowPrf k π))) F.sim
      fun _ => ())
    fun t N => ζ (t + 1) N

/-- The four clauses give these three. -/
theorem threeOfId_of_meetsId {α : ℝ≥0∞} {asked askedEach : ℕ} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : MeetsId D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel α asked askedEach ζ) :
    ThreeOfId D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel asked askedEach ζ :=
  ⟨h.verifier, h.within, h.privacy⟩

/-- **If the premises of index privacy hold at every d, the three clauses hold of frontId.** No
premise on completeness is asked. -/
theorem threeOfId_of_laws (pair : Digest → D.More → T.D) (hL : FamilyLaws D Z c₀ m₀ T pair)
    (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) (ok : (D.input Z c₀ m₀).Index → Prop)
    (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP : ℕ) (hP : PremAll F ok Yes fun _ => True)
    (hζ : ZetaLe F (fun _ => True) ζ) (hok : ∀ w, ok (idx w))
    (hrel : ∀ w x', Rel.rel w x' () →
      ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ Yes (idx w) x ∧ back x = x')
    (hNC : ∀ d, commitN (D.input Z c₀ m₀).queryLayout (F.side d) ≤ NC)
    (hNP : ∀ d, proveN (D.input Z c₀ m₀).queryLayout (F.side d) ≤ NP) :
    ThreeOfId D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel
      (8 + NC * ((D.input Z c₀ m₀).queryLayout.K + 1) + 1) (NP * ((D.input Z c₀ m₀).queryLayout.K + 1)) ζ where
  verifier := fun prove => frontId_V D Z c₀ m₀ T F.side s idx x₀ Form parse encF prove
  within :=
    ⟨queryBound_frontKC T F.side idx x₀ _ _ _ 8 ((D.input Z c₀ m₀).queryLayout.K + 1) NC hL.eight
        (fun d o => blocks_le (T.m d) (by norm_num) o) fun d i =>
        (work_commitW (hP d trivial) i).mono (hNC d),
      queryBound_frontKP T F.side idx x₀ _ _ _ ((D.input Z c₀ m₀).queryLayout.K + 1) NP
        (fun d o => blocks_le (T.m d) (by norm_num) o) fun d isk b =>
        (work_proveW (hP d trivial) (D.input Z c₀ m₀).fixedSample isk b).mono (hNP d)⟩
  privacy := privacy_frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF back
    (ZKCP.languageRelation Yes) Rel (fun _ => ()) F.sim ζ ok hL.noCoin hL.asks hL.once hL.spare
    (fun d => privacy_typedAt (ZKCP.Special.toPair (ZKCP.languageRelation Yes))
      (fun _ _ _ hy => hy) hP hζ d trivial)
    hok (fun _ => rfl) fun w x' hr => by
      obtain ⟨x, hb, hy, hbk⟩ := hrel w x' hr
      have hi : instOf (D.input Z c₀ m₀) x₀ x' = x := by
        unfold instOf
        rw [hb]
        rfl
      rw [hi]
      exact ⟨hy, hbk⟩

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.threeOfId_of_meetsId
#print axioms OnBytes.FrontRoad.threeOfId_of_laws
