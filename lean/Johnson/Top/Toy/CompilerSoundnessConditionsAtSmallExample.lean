-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean: the 16 named hypotheses of Johnson/Top/InnerCompiledVerifier.lean hold together at a
toy, with nothing assumed; and a coding of the typed oracles of that form exists.

A guard against a hollow theorem: `innerCompiledVerifier_sound` takes `CompilerSoundnessConditionsWithMeaning b`. The toy is that of
Johnson/Top/Toy/Teeth.lean: one index, one seed, one answer; no word has a collision; every word
decodes; an instance is a list of tokens; the relaxed relation says "all tokens are 0"; the key
file's and the entry file's protocols have one silent round and accept; the proof file's verifier
decides the relation; `buildInstance` refuses nothing; the model's next token is always 0. All rounds of
the key file and the entry file are marked local. Definitions, statements and proofs.
Main names:
  `TypedOracleCompiler.Compile.Batch.countable_pts`, `exists_impl`: for every interface of this form whose
    instances, bodies of leaves and plain parts are countable, the points of the typed oracles are
    countable, and there is a coding in one hash function with one-block leaf and node answers
    (`implOf`, OnBytes/TypedOracleCompiler/Compile/Batch/ImplOf.lean, at codes by choice). After
    CompileK/ImplCountable.lean and CompileK/ImplExists.lean.
  `two_holes`: there are an input r and b : SoundnessAnalysisData r with `CompilerSoundnessConditionsWithMeaning b`, at εs = 0, such that
    `buildInstance` refuses nothing, some instance is not true, and the proof file's verifier rejects
    something.
  `two_sound`: the conclusion of `innerCompiledVerifier_sound` there, with no hypothesis left: a control that
    the theorem fires; by itself it says little.
  `Sd2`: the wire of the record, written out: one seed. The one list of answers is written as the
    empty list of digests.
Limits: a toy of the form. The hypotheses on the key file and the entry file hold because their
languages are all of the space. No oracle is read and no round's error is paid (εs = 0). Nothing is
proved on whether `innerCompiledVerifier` accepts anything. The wires are the library's generic ones, carried
(`okc_passed`, Johnson/TypedOracleCompiler/RecCompile/Wire.lean); the coding is an existence by choice. All marks
are local, all depths of request trees are 0 and no part of an instance is named late: what sets
this form apart from Johnson/Top/OnFilesAt.lean is exercised by nothing here. The wire of the record
and the code of the answers are written for one seed and one answer alone.

-/
import Johnson.Top.InnerCompiledVerifier
import Johnson.TypedOracleCompiler.RecCompile.Wire
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import Johnson.Top.Toy.Teeth
import CompileK.ImplExists

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

theorem countable_PB : ∀ (s : Shape) (A : RoundSplits s), CtbS s A → Countable (PlainPart s A)
  | [], _, _ => inferInstanceAs (Countable Empty)
  | _ :: s, (a, A), h => by
      haveI := h.1.2.2.1
      haveI := h.1.2.2.2
      haveI := countable_PB s A h.2
      exact inferInstanceAs (Countable ((a.P0 ⊕ a.Pj) ⊕ PlainPart s A))

theorem countable_head (lam : ℕ) (X : Type) [Countable X] : Countable (Head lam X) := by
  let f : Head lam X →
      (List (Dig lam) × Option X × Bits) ⊕ (Option X × Bits) ⊕ (Bits × Bits) ⊕
        (List (Dig lam) × Bits) ⊕ Bits := fun h => match h with
    | .f1 a b c => .inl (a, b, c)
    | .f2 a b => .inr (.inl (a, b))
    | .f3 a b => .inr (.inr (.inl (a, b)))
    | .f4 a b => .inr (.inr (.inr (.inl (a, b))))
    | .f5 a => .inr (.inr (.inr (.inr a)))
  refine Function.Injective.countable (f := f) ?_
  intro a b hab
  cases a <;> cases b
    <;> simp only [f, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at hab
    <;> simp [hab]

/-- The points of the real oracles and of the ghost names are countable. -/
theorem countable_pts {I X : Type} (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (hX : Countable X)
    (hBd : Countable L.Bd) (hA : ∀ t : Tag, CtbS (shapeOf L t) (annOf L t)) :
    Countable (RealPts lam K L) ∧ Countable (GhostPts lam K L) := by
  haveI := hX
  haveI := hBd
  haveI := countable_head lam X
  haveI : ∀ t : Tag, Countable (PlainPart (shapeOf L t) (annOf L t)) := fun t => countable_PB _ _ (hA t)
  haveI : Countable Tag := ⟨⟨fun t => match t with | .test => 0 | .link => 1 | .onl => 2,
    fun a b h => by cases a <;> cases b <;> first | rfl | cases h⟩⟩
  haveI : Countable (LeafIn L) :=
    Function.Injective.countable (f := fun x : LeafIn L => (x.body, x.salt)) fun a b h => by
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  haveI : ∀ t : Tag, Countable (FbIn lam L t) := fun t =>
    Function.Injective.countable
        (f := fun x : FbIn lam L t => (x.round, x.head, x.rt, x.plain)) fun a b h => by
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  haveI : ∀ t : Tag, Countable (JoiningRoundQuery lam L t) := fun t =>
    Function.Injective.countable
        (f := fun x : JoiningRoundQuery lam L t => (x.round, x.ρ, x.rt, x.plain)) fun a b h => by
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  exact ⟨inferInstance, inferInstance⟩

/-- A coding of the typed oracles in one hash function exists, with one-block leaf and node
answers. -/
theorem exists_impl {I X : Type} (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (hX : Countable X)
    (hBd : Countable L.Bd) (hA : ∀ t : Tag, CtbS (shapeOf L t) (annOf L t)) :
    ∃ m : OracleCoding (typedOracleFamily lam K L) lam, m.blocks OracleName.leaf = 1 ∧ m.blocks OracleName.node = 1 := by
  obtain ⟨h1, h2⟩ := countable_pts lam K L hX hBd hA
  haveI := h1
  haveI := h2
  exact ⟨implOf lam K L (StrCode.ofCountable _) (StrCode.ofCountable _), rfl, rfl⟩

end TypedOracleCompiler.Compile.Batch

namespace VerifiableInference.OnPublicFiles.Toy.Two
open Rom ZKCP Prob
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Tagged
open VerifiableInference.OnPublicFiles.Toy
open VerifiableInference.OnPublicFiles.Toy.Teeth (T0 Tp zeros_local)

/-- a fixed plain part of a shape that is not empty -/
def pbDflt : (s : Shape) → (A : RoundSplits s) → s ≠ [] → PlainPart s A
  | [], _, h => absurd rfl h
  | r :: _, (a, _), _ => .inl (.inl (a.plain r.dPlain).1)

theorem below_times_zero (N : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (c : ℝ≥0∞),
    Err.Below (Err.timesShared N A (zeroErr s)) c
  | [], _, _ => trivial
  | _ :: s, (a, A), c => ⟨by
      show (((match a.kind with | .lo => 0 | .sh => N * 0 : ℕ) : ℕ) : ℝ≥0∞) ≤ _
      cases a.kind <;> simp, below_times_zero N s A c⟩

abbrev BdT : Type := Body0 Tp.carrierC
abbrev aT : RoundSplits Tp.offline.shape := RoundSplits.allLocal _
abbrev aL : RoundSplits Tp.link.shape := RoundSplits.allLocal _

/-- The library's generic wires at the passed toy, carried to the types of this form. -/
def W2 : QueryLayout 256 (typedOracleCarrier Tp BdT aT aL) :=
  wireOf (K1 + 1)
    (ofQB ((_root_.Iop.ProtocolQueryLayout.ofLocalD 256 K1 T0.offline pt1 d1 (numPosOf _ pt1)
      (WireE.one T0.wordLength T0.Symbol ()) 0 (Nat.clog 2 T0.wordLength)).grindLocal cap64 (GBits.zero _)))
    (ofQB ((_root_.Iop.ProtocolQueryLayout.ofLocalD 256 K1 T0.link pt1 d1 (numPosOf _ pt1)
      (WireE.two T0.wordLength T0.Symbol ()) 0 (Nat.clog 2 T0.wordLength)).grindLocal cap64 (GBits.zero _)))
    (ofQB ((_root_.Iop.ProtocolQueryLayout.ofDraws 256 K1 T0.onlineBatch pt1 d1 (numPosBOf _ _ pt1)
      (WireE.one T0.wordLength T0.Symbol ()) 0 (Nat.clog 2 T0.wordLength)).grind cap64 (GBits.zero _)))
    (Nat.clog 2 T0.wordLength) 0 0 0

/-- The wire of the record: one seed; the one record is written as the empty list. -/
def Sd2 : OutOfDomainSampleQueryLayout 256 W2.K Tp BdT aT aL where
  t := .onl
  cfg := []
  shape := []
  pl0 := pbDflt _ _ (List.cons_ne_nil _ _)
  pl1 := pbDflt _ _ (List.cons_ne_nil _ _)
  seed := fun _ => ()
  code := fun _ => []
  num := fun _ _ => true
  decS := inferInstanceAs (DecidableEq Unit)

theorem sd2_ok : Sd2.OK := ⟨fun ⟨⟨⟩, ⟨⟩⟩ ⟨⟨⟩, ⟨⟩⟩ _ => rfl, fun _ _ => rfl⟩

theorem sd2_law : Sd2.Law 0 :=
  seedLaw_of_fibres (c := Fintype.card (Fin W2.K → Dig 256)) (eR := 0)
    (fun _ => Prob.cnt_le_card _) (fun _ => le_of_eq (Prob.cnt_false fun _ h => h)) (by simp)

theorem wires2_ok : OKC W2 Sd2 :=
  okc_passed (Fin (2 ^ 64)) T0 pt1 pt1 pt1 d1 d1 d1 (numPosOf _ pt1) (numPosOf _ pt1)
    (numPosBOf _ _ pt1) () 0 0 0 K1 0 0 0 le_rfl le_rfl le_rfl (fun _ _ _ => le_rfl)
    (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) rfl cap64 0 (cap64_ok_le (Nat.zero_le _))
    (Nat.zero_le _) (GBits.zero _) (GBits.zero _) (GBits.zero _) ⟨le_rfl, trivial⟩
    ⟨le_rfl, trivial⟩ ⟨le_rfl, trivial⟩ Sd2 sd2_ok

theorem ctbP : CtbSh Tp.offline.shape := ctbSh_grind (Fin (2 ^ 64)) _ (ctbSh_pull _ ctb1)

theorem impl2_exists : ∃ m : OracleCoding (typedOracleFamily 256 W2.K (typedOracleCarrier Tp BdT aT aL)) 256,
    m.blocks OracleName.leaf = 1 ∧ m.blocks OracleName.node = 1 := by
  have hB : CtbS Tp.onlineBatch.loc.shape Tp.onlineBatch.ann := by
    show CtbS ((s1.pull σ1).grind (Fin (2 ^ 64)) (GBits.zero _))
      (((RoundSplits.allLocal s1).pull σ1).grind (Fin (2 ^ 64)) (GBits.zero _))
    exact ctbS_grind _ _ (ctbS_pull _ (ctbS_allLocal ctb1))
  have hA : ∀ t : Tag, CtbS (shapeOf (typedOracleCarrier Tp BdT aT aL) t) (annOf (typedOracleCarrier Tp BdT aT aL) t) :=
    fun t => by
      cases t
      · exact ctbS_allLocal ctbP
      · exact ctbS_allLocal ctbP
      · exact hB
  haveI : ∀ t : Tag, Countable (SymAny (shape0 Tp.carrierC t)) := fun t => by
    cases t
    · exact _root_.Compile.Batch.countable_symAny _ _ (ctbS_allLocal ctbP)
    · exact _root_.Compile.Batch.countable_symAny _ _ (ctbS_allLocal ctbP)
    · exact _root_.Compile.Batch.countable_symAny _ _ hB
  haveI : Countable Tag := ⟨⟨fun t => match t with | .test => 0 | .link => 1 | .onl => 2,
    fun a b h => by cases a <;> cases b <;> first | rfl | cases h⟩⟩
  exact exists_impl 256 W2.K (typedOracleCarrier Tp BdT aT aL)
    (inferInstanceAs (Countable (Option (List ℕ) × (Unit × Unit) × (Unit × Unit))))
    (inferInstanceAs (Countable (Option (Unit ⊕ (Σ t : Tag, SymAny (shape0 Tp.carrierC t)))))) hA

theorem key2_countable : Countable (KeyRoot 256 Tp) :=
  Function.Injective.countable (f := fun k : KeyRoot 256 Tp => (k.cm, k.rcd)) (by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    cases h
    rfl)

def key2 : KeyRoot 256 Tp := ⟨dig0, ((), ())⟩
def prf2 : OfflineLinkOnlineProof 256 Tp aT aL := ⟨0, none, (dig0, ((), ()), none), none⟩

/-- The toy input, at a coding. The model: the next token is always 0. The instance that is built
from a prompt with output tokens is the list of the output tokens, whatever they are. -/
def inputAt (m : OracleCoding (typedOracleFamily 256 W2.K (typedOracleCarrier Tp BdT aT aL)) 256) : InnerCompilerInput where
  Index := Unit
  Instance := List Token
  protocol := Tp
  LeafBody := BdT
  offlineRoundSplits := aT
  linkRoundSplits := aL
  queryLayout := W2
  seedQueries := Sd2
  answerCode := fun _ => []
  fixedSample := ((), ())
  compilerParameters := ⟨0, 0, 0, 0⟩
  oracleCoding := m
  keyCode := codeUnderTag 0 key2_countable
  buildInstance := fun x' _ => some x'.2
  nextToken := fun _ _ => some 0
  ProverKey := Unit
  commit := fun _ => OComp.pure (key2, ())
  prove := fun _ b => OComp.pure ⟨b.map fun _ => prf2, List.length_map _⟩
  coinBound := 0
  fallbackProof := (key2, prf2)

def besideAt (m : OracleCoding (typedOracleFamily 256 W2.K (typedOracleCarrier Tp BdT aT aL)) 256) : SoundnessAnalysisData (inputAt m) where
  Wn := Unit
  Rno := fun _ (x : List Token) _ => ∀ t ∈ x, t = 0
  ext := (Special.extOf (extractorOverOneHashFunction m (indexExtractorAtRootAndOutOfDomainSample W2))).digestKey (codeUnderTag 0 key2_countable)
  εId := fun t => (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256
  x₀ := []
  εs := 0

/-- All sixteen, at the toy. -/
theorem two_holes : ∃ (r : InnerCompilerInput) (b : SoundnessAnalysisData r), CompilerSoundnessConditionsWithMeaning b ∧ b.εs = 0 ∧
    (∀ x' a, (r.buildInstance x' a).isSome) ∧ (∃ i x, ¬ HasRelaxedRelationWitness b i x) ∧
    (∃ x, ∀ y τ, r.protocol.onlineBatch.loc.accept x y τ = false) := by
  obtain ⟨m, -, -⟩ := impl2_exists
  have hW := wires2_ok
  obtain ⟨wit, ε, hε, hP⟩ := Teeth.proof_sound
  refine ⟨inputAt m, besideAt m, ⟨⟨fun _ _ h => h.elim,
    ⟨zeroErr _, below_times_zero _ _ _ _,
      fun _ _ h => absurd (Or.inr (Option.some_ne_none ())) h⟩,
    ⟨zeroErr _, below_times_zero _ _ _ _, fun _ _ h => absurd (Or.inr (Or.inr rfl)) h⟩,
    ⟨wit, ε, hε, hP⟩,
    ((yes_local s1).pull σ1).grind _, ((yes_local s1).pull σ1).grind _,
    ((zeros_local s1).pull σ1).grind _, BatchOne.BAnn.allLocal_coherent _,
    BatchOne.BAnn.allLocal_coherent _,
    BatchGrind.coherent_grind _ (BatchPull.coherent_pull σ1 (BatchOne.BAnn.allLocal_coherent s1)),
    sd2_law, ⟨hW.base, hW.T, hW.Lk, hW.B⟩, fun ⟨⟩ ⟨⟩ _ => rfl, fun _ _ => rfl,
    Rec.commitmentBinds_of_code _ _ _ (codeUnderTag_oneToOne 0 key2_countable) _ _⟩, ?_⟩,
    rfl, fun _ _ => rfl, ⟨(), [1], ?_⟩, ⟨([1], ((), ())), fun _ _ => rfl⟩⟩
  · intro i x' a x hb hx position hpos
    obtain ⟨_, hw⟩ := hx
    have hx' : x = x'.2 := (Option.some.inj hb).symm
    subst hx'
    show some 0 = some x'.2[position]
    rw [hw _ (List.getElem_mem hpos)]
  · rintro ⟨_, hw⟩
    exact absurd (hw 1 (List.mem_singleton.2 rfl)) (by decide)

/-- The theorem fires: no hypothesis is left. -/
theorem two_sound : ∃ (r : InnerCompilerInput) (b : SoundnessAnalysisData r),
    SoundForWith (innerSystem r) (compiledIndexExtractor b) (innerSystem r).IsModelOutput (compiledSoundnessError b) :=
  let ⟨r, b, h, _⟩ := two_holes
  ⟨r, b, innerCompiledVerifier_sound b h⟩

end VerifiableInference.OnPublicFiles.Toy.Two

#print axioms TypedOracleCompiler.Compile.Batch.exists_impl
#print axioms VerifiableInference.OnPublicFiles.Toy.Two.two_holes
#print axioms VerifiableInference.OnPublicFiles.Toy.Two.two_sound
