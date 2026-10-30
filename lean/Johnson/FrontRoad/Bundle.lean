-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Bundle.lean: from the premises listed below and from the hypothesis
Spec.frontPrivacyAt follow four clauses about one and the same scheme, the shell frontAt over one
family of honest sides (MeetsRoad): what its verifier is, completeness, a bound on the honest side's
queries of the hash function, and index privacy. Conditional, no member known, of a shell.
Terms and the limits that go with any quote: Spec.lean.

What this file has.
  MeetsRoad   of the shell frontAt at the honest sides F.side, with numbers α, asked, askedEach, ζ:
      verifier   it is the verifier of the library's system of D, in the form of ZKCP/Defs.lean, at
                 the ID, the request, and the form computed from the whole key and the proof (by
                 unfolding: frontAt_V), while committer and prover are this folder's, not the
                 description's own;
      complete   completeness (ZKCP.HasCompletenessError) at α;
      within     the committer makes at most asked queries of the hash function on every path, the
                 prover at most askedEach;
      privacy    index privacy (ZKCP.HasStrongIndexPrivacyWith, the stronger form of ZKCP/Defs.lean)
                 at all weights, at ζ at one query more, with the simulator frontSim at hp the map
                 to Unit: it does not use Rel.pp of the index.
  meetsRoad_of   MeetsRoad at α, q₀ + NC * Bk + 1, NP * Bk and ζ, from the hypothesis
      Spec.frontPrivacyAt, a named proposition (proved as frontPrivacyAt in FrontProof.lean, which
      this file does not import; without the hypothesis: Joined.lean) and these premises:
  - PremAll and ZetaLe (PremAt.lean), HonAll and AlphaLe (HonAt.lean), over the same F, at every
    value d of the type T.D, whether or not the public reading can return it;
  - the four premises on the public reading; fits (innerCompiledVerifier is the same at the description's input
    at (c, m) and at T's input at pair c m); reads (at every hash function pair of the values of
    the description's two readings is what T's public reading returns); the public files are in
    scope;
  - the parser undoes the encoder at every key and proof that the honest side can produce and that
    the verifier after the public reading accepts (UndoOn, Complete.lean); every key with a told
    part has a code;
  - every weight's index is in the range ok; a request of which Rel holds builds, with no further
    tokens, an instance of which Yes holds at the weight's index, and from which the request can be
    read back (ok, a range of inner indices, and Yes, a relation on inner indices and instances, are
    variables);
  - bounds q₀, Bk, NC, NP on the reading's queries, on the blocks of a typed answer, and on the two
    counts of Johnson/WholeKey/Work.lean at every d.

Limits. The four clauses count only together. Index privacy by itself is easy to satisfy: honest
sides that send fixed messages have it (argued; for the premises on provers proved: silent_good,
Johnson/WholeKey/Foes.lean). Completeness by itself says nothing on hiding. Both, at two different
provers, say nothing of either prover. A long search could find an accepted string without the index
(argued). So one term frontAt at one family F is in all four clauses, and PremAll and HonAll are
required of the same (F.a d).Hs. The map idx is a variable: a constant map satisfies what is
required of it, and then "at all weights" says nothing of the weights.
In this file the clause on index privacy rests on the hypothesis. No member is built, not even a
small example. There is no clause on index binding. No number is given: α, ζ and the counts are
variables. A bound of index privacy says nothing until ζ + ζ < 1; to pass that bar is not to hide;
and "below 1" is no bar for α either (argued, not proved: the heads of Johnson/WholeKey/Half.lean
and Johnson/WholeKey/Bundle.lean). All limits of Johnson/WholeKey/Statement.lean,
ZKCP/PublicRead/Spec.lean and Complete.lean hold.
-/
import Johnson.FrontRoad.HonAt
import Johnson.FrontRoad.Within

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

/-- Four clauses about one and the same scheme, the shell frontAt at the honest sides F.side: what
its verifier is, completeness at α, bounds on the committer's and the prover's queries of the hash
function, and index privacy (ZKCP.HasStrongIndexPrivacyWith) with the simulator frontSim at ζ at one
query more. -/
structure MeetsRoad (α : ℝ≥0∞) (asked askedEach : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  verifier : ∀ (prove : ModelWeights s → D.Rand → List Token → List Token →
      RandomizedAlgorithm Form) k x' π,
    (frontAt D Z c₀ m₀ T F.side s idx x₀ Form parse encF).V k x' π =
      (VerifierAndGoals.system D Z s Form prove parse).uploadArgument.V k.1 x'
        (encF ([], (lowKey k.2, lowPrf k.2 π)))
  complete : ZKCP.HasCompletenessError Rel (frontAt D Z c₀ m₀ T F.side s idx x₀ Form parse encF) α
  within : (∀ w, ((frontAt D Z c₀ m₀ T F.side s idx x₀ Form parse encF).C w).QueryBound asked) ∧
    ∀ isk x', ((frontAt D Z c₀ m₀ T F.side s idx x₀ Form parse encF).P isk x' ()).QueryBound
      askedEach
  privacy : ZKCP.HasStrongIndexPrivacyWith Rel
    (frontAt D Z c₀ m₀ T F.side s idx x₀ Form parse encF)
    (frontSim T x₀ back F.sim fun _ => ()) fun t N => ζ (t + 1) N

/-- MeetsRoad, from the hypothesis H (Spec.frontPrivacyAt, not proved here; without it:
meetsRoad_joined, Joined.lean) and the premises over one family F of honest sides that the head
lists. Conditional, no member known, of a shell. -/
theorem meetsRoad_of (H : Spec.frontPrivacyAt) (G : FallsAt F)
    (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) (ok : (D.input Z c₀ m₀).Index → Prop)
    (α : ℝ≥0∞) (ζ : ℕ → ℕ → ℝ≥0∞) (q₀ Bk NC NP : ℕ) (pair : Digest → D.More → T.D)
    (hP : PremAll F ok Yes fun _ => True) (hζ : ZetaLe F (fun _ => True) ζ)
    (hH : HonAll G Yes fun _ => True) (hα : AlphaLe G (fun _ => True) α)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (fits : ∀ c m commitment prompt output (proof : VerifierAndGoals.TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (reads : ∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (scope : VerifierAndGoals.InScope Z = true)
    (hparse : UndoOn D Z c₀ m₀ T F.side idx Yes parse encF)
    (hcode : ∀ ck, ∃ code, T.encT ck = some code) (hok : ∀ w, ok (idx w))
    (hrel : ∀ w x', Rel.rel w x' () →
      ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ Yes (idx w) x ∧ back x = x')
    (hq : T.Pub.QueryBound q₀) (hB : ∀ d o, (T.m d).blocks o ≤ Bk)
    (hNC : ∀ d, commitN (D.input Z c₀ m₀).queryLayout (F.side d) ≤ NC)
    (hNP : ∀ d, proveN (D.input Z c₀ m₀).queryLayout (F.side d) ≤ NP) :
    MeetsRoad D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel α (q₀ + NC * Bk + 1) (NP * Bk) ζ where
  verifier := fun prove k x' π => frontAt_V D Z c₀ m₀ T F.side s idx x₀ Form prove parse encF k x' π
  complete := frontComplete_hon D Z c₀ m₀ T F G Yes α s idx x₀ Form parse encF pair PP' Rel noCoin
    asks once spare fits reads scope hparse hcode hH hα fun w x' hr => by
      obtain ⟨x, hb, hy, -⟩ := hrel w x' hr
      exact ⟨x, hb, hy⟩
  within := within_front T idx x₀ _ F hP q₀ Bk NC NP hq hB hNC hNP
  privacy := H D Z c₀ m₀ T F.side s idx x₀ back Form parse encF Unit PP'
    (ZKCP.languageRelation Yes) Rel (fun _ => ()) F.sim ζ ok noCoin asks once spare
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

#print axioms OnBytes.FrontRoad.meetsRoad_of
