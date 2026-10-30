-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Joined.lean: if one committer and prover satisfy the premises of index privacy and
the premises of completeness, both at every value d of the type T.D, whether or not the public
reading can return it, and the further premises of meetsRoad_of (Bundle.lean), then the shell made
of these two (frontAt, or frontId) satisfies four clauses about one and the same scheme (MeetsRoad,
Bundle.lean; MeetsId, here). Conditional, no member known, of a shell. Spec.frontPrivacyAt is not a
hypothesis here. At the built description the hypotheses are that the public files are in scope and
the eight fields of LeftAtWeights (30 clauses, counting the 20 of PremW and the 4 of HonAll); the
other theorems have more.
Terms and the limits that go with any quote: Spec.lean.

What this file proves. First, for the shell frontAt, which publishes its whole key together with the
commitment ID. Each theorem is the one named in brackets, which has Spec.frontPrivacyAt as a
hypothesis, applied to that statement's proof frontPrivacyAt (FrontProof.lean); the premises are
written out there. In the clause on index privacy of MeetsRoad and of MeetsId, hp is the map to the
one value of Unit: the simulator does not use Rel.pp of the index. It is given each request.
  meetsRoad_joined   for arbitrary parameters (meetsRoad_of, Bundle.lean).
  meetsRoad_laws_joined   at any description, from FamilyLaws (meetsRoad_of_laws,
      AtDescription.lean).
  meetsRoad_description_joined   at the description that the release's goal statements use
      (meetsRoad_description).
  meetsRoad_weights_joined   at the built description, the library's own map from weights and the
      range of all matrices that hold an index (meetsRoad_weights, AtWeights.lean).
Second, for the shell frontId (FrontId.lean), which publishes the commitment ID only. A proof is a
form; the verifier is that of the library's system, as a function, while committer and prover are
this folder's, not the description's own.
  MeetsId   the four clauses about that scheme: verifier (frontId_V), complete, within, privacy.
  meetsId_joined   for arbitrary parameters, from the same premises as meetsRoad_joined. By
      frontIdComplete_hon, queryBound_frontKC, queryBound_frontKP (CompleteK.lean) and
      privacy_frontId at privacy_typedAt (PremAt.lean).
  meetsId_weights_joined   at the built description and the library's own map from weights, from
      LeftAtWeights.

Limits.
  - No honest side with the protocol's three provers is written in Lean, and nothing is known to
    satisfy the premises, not even a small example: the theorems may apply to nothing.
  - Whether the premise on the parser (UndoOn, Complete.lean) holds at the description's own form
    and parser is not proved.
  - Yes, the relation on inner indices and instances, is a variable, and Rel is required to imply
    it, not the converse. A Rel that holds of nothing satisfies that. A Yes that holds of nothing
    makes UndoOn vacuous, and with it the clauses of HonFit on acceptance and on measures (LawFit,
    WiresFit and SideFit do not read Yes).
  - At settings that are not valid the library's map (FlashProve.backThe) sends all weights to one
    matrix.
  - There is no clause on index binding. The only numbers are 8, for the reading's queries, and K +
    1, for the blocks of a typed answer; α, ζ, NC and NP (and q₀ and Bk for arbitrary parameters)
    are variables. A bound of index privacy says nothing until ζ + ζ < 1; to pass that bar is not to
    hide; and "below 1" is no bar for the error of completeness either (argued, not proved: the
    heads of Johnson/WholeKey/Half.lean and Johnson/WholeKey/Bundle.lean).
  - All limits of Johnson/WholeKey/Statement.lean, ZKCP/PublicRead/Spec.lean, Complete.lean,
    AtWeights.lean and FrontId.lean hold.
-/
import Johnson.FrontRoad.AtWeights
import Johnson.FrontRoad.CompleteK
import Johnson.FrontRoad.FrontProof

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead FlashProve
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Letters
variable (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (F : SidesAt T) (s : IntegerTransformer.Settings)
  (idx : ModelWeights s → (D.input Z c₀ m₀).Index) (x₀ : (D.input Z c₀ m₀).Instance)
  (back : (D.input Z c₀ m₀).Instance → List Token × List Token) (Form : Type)
  (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) {PP' : Type}
  (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')

/-- If the premises of meetsRoad_of (Bundle.lean) other than Spec.frontPrivacyAt hold over one
family of honest sides at every d of the type, the four clauses (MeetsRoad) hold of frontAt, for
arbitrary parameters. Conditional, no member known, of a shell. -/
theorem meetsRoad_joined (G : FallsAt F)
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
    MeetsRoad D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel α (q₀ + NC * Bk + 1) (NP * Bk) ζ :=
  meetsRoad_of D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel frontPrivacyAt G Yes ok α ζ q₀ Bk NC
    NP pair hP hζ hH hα noCoin asks once spare fits reads scope hparse hcode hok hrel hq hB hNC hNP

/-- Four clauses about one and the same scheme, the shell frontId, which publishes the commitment ID
only: its verifier is that of the library's system, as a function, while committer and prover are
this folder's, not the description's own; completeness at α; bounds on queries of the hash function;
index privacy with the simulator frontSimK, which does not use Rel.pp of the index (hp is the map to
Unit), at ζ at one query more. -/
structure MeetsId (α : ℝ≥0∞) (asked askedEach : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  verifier : ∀ prove : ModelWeights s → D.Rand → List Token → List Token →
      RandomizedAlgorithm Form,
    (frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF).V =
      (VerifierAndGoals.system D Z s Form prove parse).uploadArgument.V
  complete : ZKCP.HasCompletenessError Rel (frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF) α
  within : (∀ w, ((frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF).C w).QueryBound asked) ∧
    ∀ isk x', ((frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF).P isk x' ()).QueryBound
      askedEach
  privacy : ZKCP.HasStrongIndexPrivacyWith Rel
    (frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF)
    (frontSimK T x₀ back (fun id _ => id) (fun k π => encF ([], (lowKey k, lowPrf k π))) F.sim
      fun _ => ())
    fun t N => ζ (t + 1) N

/-- If the premises of meetsRoad_joined hold, the four clauses (MeetsId) hold of frontId, for
arbitrary parameters. Conditional, no member known, of a shell. -/
theorem meetsId_joined (G : FallsAt F)
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
    MeetsId D Z c₀ m₀ T F s idx x₀ back Form parse encF Rel α (q₀ + NC * Bk + 1) (NP * Bk) ζ where
  verifier := fun prove => frontId_V D Z c₀ m₀ T F.side s idx x₀ Form parse encF prove
  complete := frontIdComplete_hon D Z c₀ m₀ T F G Yes α s idx x₀ Form parse encF pair PP' Rel
    noCoin asks once spare fits reads scope hparse hcode hH hα fun w x' hr => by
      obtain ⟨x, hb, hy, -⟩ := hrel w x' hr
      exact ⟨x, hb, hy⟩
  within :=
    ⟨queryBound_frontKC T F.side idx x₀ _ _ _ q₀ Bk NC hq hB fun d i =>
        (work_commitW (hP d trivial) i).mono (hNC d),
      queryBound_frontKP T F.side idx x₀ _ _ _ Bk NP hB fun d isk b =>
        (work_proveW (hP d trivial) (D.input Z c₀ m₀).fixedSample isk b).mono (hNP d)⟩
  privacy := privacy_frontId D Z c₀ m₀ T F.side s idx x₀ Form parse encF back
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

end Letters

/-- At any description, public files in scope and a family T with FamilyLaws, if LeftToAsk holds,
the four clauses (MeetsRoad) hold of frontAt. Conditional, no member known, of a shell. -/
theorem meetsRoad_laws_joined (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles)
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
  meetsRoad_of_laws frontPrivacyAt D Z scope c₀ m₀ T pair hL F G s idx x₀ back Form parse encF PP'
    Rel Yes ok α ζ NC NP h

/-- At the description that the release's goal statements use and all public files in scope, there
is a family T with FamilyLaws at which LeftToAsk gives the four clauses (MeetsRoad) of frontAt.
Conditional, no member known, of a shell. -/
theorem meetsRoad_description_joined (Z : VerifierAndGoals.PublicFiles)
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
              (NP * (((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c₀ m₀).queryLayout.K + 1)) ζ :=
  meetsRoad_description frontPrivacyAt Z scope

/-- If the eight fields of LeftAtWeights hold, the four clauses (MeetsRoad) hold of frontAt, at the
built description, public files in scope and all weights. Conditional, no member known, of a
shell. -/
theorem meetsRoad_weights_joined (Z : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope Z = true) (F : SidesAt (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z)) (G : FallsAt F)
    (s : IntegerTransformer.Settings) (x₀ : (flashProveDescription.input Z allZeroDigest []).Instance)
    (back : (flashProveDescription.input Z allZeroDigest []).Instance → List Token × List Token) (Form : Type)
    (parse : VerifierAndGoals.Parser flashProveDescription Z Form) (encF : VerifierAndGoals.TypedProof (flashProveDescription.F Z) (flashProveDescription.P Z) → Form)
    (PP' : Type) (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (Yes : (flashProveDescription.input Z allZeroDigest []).Index → (flashProveDescription.input Z allZeroDigest []).Instance → Prop) (α : ℝ≥0∞)
    (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP : ℕ)
    (h : LeftAtWeights Z F G s back parse encF Rel Yes α ζ NC NP) :
    MeetsRoad flashProveDescription Z allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) F s (backThe Z s) x₀ back Form parse encF
      Rel α (8 + NC * ((flashProveDescription.input Z allZeroDigest []).queryLayout.K + 1) + 1)
      (NP * ((flashProveDescription.input Z allZeroDigest []).queryLayout.K + 1)) ζ :=
  meetsRoad_weights frontPrivacyAt Z scope F G s x₀ back Form parse encF PP' Rel Yes α ζ NC NP h

/-- If the eight fields of LeftAtWeights hold, the four clauses (MeetsId) hold of frontId, at the
built description, public files in scope and all weights. Conditional, no member known, of a
shell. -/
theorem meetsId_weights_joined (Z : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope Z = true) (F : SidesAt (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z)) (G : FallsAt F)
    (s : IntegerTransformer.Settings) (x₀ : (flashProveDescription.input Z allZeroDigest []).Instance)
    (back : (flashProveDescription.input Z allZeroDigest []).Instance → List Token × List Token) (Form : Type)
    (parse : VerifierAndGoals.Parser flashProveDescription Z Form) (encF : VerifierAndGoals.TypedProof (flashProveDescription.F Z) (flashProveDescription.P Z) → Form)
    (PP' : Type) (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (Yes : (flashProveDescription.input Z allZeroDigest []).Index → (flashProveDescription.input Z allZeroDigest []).Instance → Prop) (α : ℝ≥0∞)
    (ζ : ℕ → ℕ → ℝ≥0∞) (NC NP : ℕ)
    (h : LeftAtWeights Z F G s back parse encF Rel Yes α ζ NC NP) :
    MeetsId flashProveDescription Z allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) F s (backThe Z s) x₀ back Form parse encF Rel
      α (8 + NC * ((flashProveDescription.input Z allZeroDigest []).queryLayout.K + 1) + 1) (NP * ((flashProveDescription.input Z allZeroDigest []).queryLayout.K + 1)) ζ :=
  meetsId_joined flashProveDescription Z allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) F s (backThe Z s) x₀ back Form parse
    encF Rel G Yes (okThe Z) α ζ 8 ((flashProveDescription.input Z allZeroDigest []).queryLayout.K + 1) NC NP Prod.mk h.prem h.zeta h.hon
    h.alpha (familyLaws_the Z).noCoin (familyLaws_the Z).asks (familyLaws_the Z).once
    (familyLaws_the Z).spare
    (fits_of_eq flashProveDescription Z allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] Z) Prod.mk (familyLaws_the Z).eq)
    (familyLaws_the Z).reads scope h.undo (familyLaws_the Z).total
    (fun w => inRange_backThe Z s w) h.tie (familyLaws_the Z).eight
    (fun d o => blocks_le ((layoutsOfBuiltDescription flashProveData allZeroDigest [] Z).m d) (by norm_num) o) h.commits h.proves

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.meetsRoad_joined
#print axioms OnBytes.FrontRoad.meetsRoad_laws_joined
#print axioms OnBytes.FrontRoad.meetsRoad_description_joined
#print axioms OnBytes.FrontRoad.meetsRoad_weights_joined
#print axioms OnBytes.FrontRoad.meetsId_joined
#print axioms OnBytes.FrontRoad.meetsId_weights_joined
