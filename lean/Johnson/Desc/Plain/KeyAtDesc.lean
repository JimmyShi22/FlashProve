-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/KeyAtDesc.lean: `keySound_at_desc`: THE KEY FILE's HYPOTHESIS OF THE TOP,
`CompilerSoundnessConditionStatements.keySound`, AT A DESCRIPTION's OWN DECISION (runK := `FileDescription.run`), from one plain law a
block.

The library's door (`keySound_at`, OnBytes/TypedOracleCompiler/Joined/TwoChains.lean) asks `tieT` of the language
outright:
"where the first chain's clause speaks of (rec, y) its relation has a witness" must give the key
file's language, WITHOUT THE VERIFIER's YES: so the first condition has to hold of every record and
word outside the language, also of those that the running verifier refuses by its test on the
instance. Here the tie is asked UNDER THE VERIFIER's YES, on the very transcript:

  `sound_of_plain`: `InteractiveOracleProof.Sound` of a file's protocol for a language Lg, from `PlainFile.Leads3`,
    `decides`, and `ties`: the file's yes at (x, y) on τ; what the first chain handed on, on τ; and
    "on₀ → M": give Lg x y. Where on₀ fails, `ties` has the yes alone: it is met where the yes gives
    on₀.
  `keySound_plainYes`: in `keySound_at`'s own words.
  `keySound_at_desc`: at `filesOf` with runK := FK.run.

Limits: those of AtDesc.lean. The shared chain's rounds pay 2 ^ depthReqT each: that factor stands
in the top's own hypothesis.

-/
import Johnson.Desc.Plain.AtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

/-- **A file's protocol is sound round by round for Lg**, the tie asked under the verifier's yes. -/
theorem sound_of_plain {G : Chains} {Y : Type} {E : ExtSpec} (D : Desc G Y E)
    (P : PlainFile G (Y × E.Str)) (h : P.Leads3)
    (decides : ∀ x y (τ : Tr G.sh), D.accept x y τ = true →
      (P.links.all.out (x, y) τ).isSome = true)
    (Lg : Y → E.Str → Prop)
    (ties : ∀ x y (τ : Tr G.sh) b, D.accept x y τ = true →
      P.out₁ (x, y) (Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) τ) = some b →
      (P.on₀ (x, y) → P.M (x, y) b) → Lg x y) :
    D.proto.Sound Lg P.links.err := by
  intro x y hL
  by_cases ho : P.on₀ (x, y)
  · refine Doomed.mono _ _ ?_ ((P.knows h).all (x, y) ho)
    intro τ hτ
    cases ha : D.accept x y τ with
    | false => exact ha
    | true =>
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (decides x y τ ha)
      obtain ⟨b, hb⟩ := P.first_of_all _ τ (decides x y τ ha)
      have hR := hτ u () hu trivial
      rw [P.ext_eq _ τ b hb] at hR
      exact absurd (ties x y τ b ha hb fun _ => hR) hL
  · refine Doomed.of_forall _ _ fun τ => ?_
    cases ha : D.accept x y τ with
    | false => exact ha
    | true =>
      obtain ⟨b, hb⟩ := P.first_of_all _ τ (decides x y τ ha)
      exact absurd (ties x y τ b ha hb fun ho' => absurd ho' ho) hL

/-- **The key file's hypothesis of the top**, in `keySound_at`'s own words. -/
theorem keySound_plainYes {I X : Type} (L : HolographicProtocol I X) {G : Chains}
    (D : Desc G L.Rec (oneExternalString L.wordLength L.Symbol)) (aT : RoundSplits L.offline.shape) (hT : L.offline = D.proto)
    (ha : HEq aT G.ann) (P : PlainFile G (L.Rec × (oneExternalString L.wordLength L.Symbol).Str)) (laws : G.Laws)
    (h : P.Leads3)
    (decides : ∀ x y (τ : Tr G.sh), D.accept x y τ = true →
      (P.links.all.out (x, y) τ).isSome = true)
    (ties : ∀ rec y (τ : Tr G.sh) b, D.accept rec y τ = true →
      P.out₁ (rec, y) (Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) τ) = some b →
      (P.on₀ (rec, y) → P.M (rec, y) b) → L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none)
    (dT : ℕ) {εs : ℝ≥0∞} (worst : P.links.worst (2 ^ dT) ≤ εs) :
    ∃ ε : Err L.offline.shape, Err.Below (Err.timesShared (2 ^ dT) aT ε) εs ∧
      L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) ε := by
  have key : ∀ (Q : InteractiveOracleProof L.Rec (oneExternalString L.wordLength L.Symbol)) (a : RoundSplits Q.shape), Q = D.proto → HEq a G.ann →
      ∃ ε : Err Q.shape, Err.Below (Err.timesShared (2 ^ dT) a ε) εs ∧
        Q.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) ε := by
    rintro _ a rfl h'
    obtain rfl : a = G.ann := eq_of_heq h'
    exact ⟨P.links.err, by
      rw [timesShared_err P.links laws]
      exact Err.Below.mono_bound worst (below_errN P.links _),
      sound_of_plain D P h decides _ ties⟩
  exact key L.offline aT hT ha

end TypedOracleCompiler.Joined

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc worst_le)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (FK : FileDescription Kc.conf.Rec) (all : List LeftT) {X₁ X₂ W : Type}
  (T : ThreeAt (ckP .two) (DK.at a) all FK X₁ X₂ W)
  (Pl : PPlaces (DK.at a) all (FK.XiPub × FK.S₁) ((FK.XiPub × FK.S₁) × FK.S₂)
    ((FK.XiPub × FK.S₁ × FK.S₂) × FK.S₃))
  (h₁ : (rowIOR (atDesc FK T).p₁ (atDesc FK T).l₁).shape = uLT (ckP .two) (DK.at a).ds₁)
  (h₂ : (rowIOR (atDesc FK T).p₂ (atDesc FK T).l₂).shape = uLT (ckP .two) (DK.at a).ds₂)
  (h₃ : (rowIOR (atDesc FK T).p₃ (atDesc FK T).l₃).shape = uLT (ckP .two) (DK.at a).ds₃)
  (M : Kc.conf.Rec × (oneExternalString (2 ^ (DK.at a).a) SgX).Str →
    (FK.XiPub × FK.S₁) × (EAll (DK.at a) all).Str → Prop)
  (L₁ : (FK.XiPub × FK.S₁) × (EAll (DK.at a) all).Str → Prop)
  (L₂ : (FK.XiPub × FK.S₁ × FK.S₂) × (EAll (DK.at a) all).Str → Prop)
  (d : (FK.XiPub × FK.S₁) × (EAll (DK.at a) all).Str)

/-- The key file in the plain form, at the description's own three folds. -/
abbrev plainK : PlainFile (chainsOf (ckP .two) (DK.at a) tFk tJk t3k)
    (Kc.conf.Rec × (oneExternalString (2 ^ (DK.at a).a) SgX).Str) :=
  plainOf tFk tJk t3k (atDesc FK T) Pl (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁ h₂
    h₃ M L₁ L₂ d

theorem out_of_acceptKD (rec : Kc.conf.Rec) (y : (oneExternalString (2 ^ (DK.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DK.at a) tFk tJk t3k).sh)
    (h : (wholeDesc (ckP .two) (DK.at a) tFk tJk t3k silK FK.run).accept rec y τ = true) :
    (reductionOfWholeFile (ckP .two) (DK.at a) tFk tJk t3k silK FK.run).out rec y τ = some () := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h
  cases u
  exact hu

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP runP eL N early
    late).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP runP eL N early
                                    late) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP runP eL N early
                                     late) P)

include d in
/-- **keySound_at_desc: `CompilerSoundnessConditionStatements.keySound` at a description's own decision, from one plain law a
block.** -/
theorem keySound_at_desc (hO : OfDesc FK T) (hf : (atDesc FK T).Fits)
    (fit : RowFit (DK.at a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc FK T).p₁ :: (atDesc FK T).l₁))
    (e₂ : EachLeads Pl.on₂ Pl.Q₂ 0 ((atDesc FK T).p₂ :: (atDesc FK T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc FK T).p₃ :: (atDesc FK T).l₃))
    (G : Glues (atDesc FK T) Pl M L₁ L₂)
    (tie : ∀ rec (y : (oneExternalString (2 ^ (DK.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DK.at a) tFk tJk t3k).sh) (s₁ : FK.S₁) (s₂ : FK.S₂)
      (s₃ : FK.S₃) (z : (EAll (DK.at a) all).Str),
      FK.okStart rec = true →
      silK rec ((chainsOf (ckP .two) (DK.at a) tFk tJk t3k).msgF τ).2
        ((chainsOf (ckP .two) (DK.at a) tFk tJk t3k).msgJ τ).2
        ((chainsOf (ckP .two) (DK.at a) tFk tJk t3k).msg3 τ).2 = true →
      FK.fin rec s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc FK T).in₁ rec, (y, fun _ => [])) → M (rec, y) ((FK.pub rec, s₁), z)) →
      Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none)
    (c₂ : ℝ≥0∞)
    (b₁ : Err.Below (errOwn (atDesc FK T).p₁ (atDesc FK T).l₁ (DK.at a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc FK T).p₂ (atDesc FK T).l₂ (DK.at a).ds₂ h₂) c₂)
    (hc : ((2 ^ Tl.W.depthReqT : ℕ) : ℝ≥0∞) * c₂ ≤ U.εs)
    (b₃ : Err.Below (errOwn (atDesc FK T).p₃ (atDesc FK T).l₃ (DK.at a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP
                                                               runP eL N early late) P Tl U) := by
  have decides : ∀ rec y (τ : Tr (chainsOf (ckP .two) (DK.at a) tFk tJk t3k).sh),
      (wholeDesc (ckP .two) (DK.at a) tFk tJk t3k silK FK.run).accept rec y τ = true →
      ((plainK Kc DK tFk tJk t3k FK all T Pl h₁ h₂ h₃ M L₁ L₂ d).links.all.out
        (rec, y) τ).isSome = true := by
    intro rec y τ ha
    have ho := out_of_acceptKD Kc DK tFk tJk t3k silK FK _ y τ ha
    have ho' := Sound.wholeMono (ckP .two) (DK.at a) _ _ _ _ tFk tJk t3k silK
      (fun _ _ _ _ => true) FK.run FK.run rec rec (fun _ _ _ _ => rfl) (fun _ _ _ h => h) y τ ho
    exact descDecides (ckP .two) (DK.at a) all _ X₁ X₂ W _ _ _ tFk tJk t3k FK T (fun _ _ => true)
      (fun _ _ => true) (fun _ _ => true) (fun _ _ _ _ => true)
      (idleSnd tFk tJk t3k (atDesc FK T) _ _ _ h₁ h₂ h₃) hO fit (fun _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl) rec rec y τ rfl
      (fun _ _ _ _ => rfl) ho'
  have b₂' : Err.Below (plainK Kc DK tFk tJk t3k FK all T Pl h₁ h₂ h₃ M L₁ L₂ d).links.ε₂ c₂ :=
    ⟨by simp, b₂⟩
  exact keySound_plainYes
    ((filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP runP eL N early late).withProvers P)
    (wholeDesc (ckP .two) (DK.at a) tFk tJk t3k silK FK.run)
    (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK FK.run silP runP eL N early late).annT
    rfl HEq.rfl (plainK Kc DK tFk tJk t3k FK all T Pl h₁ h₂ h₃ M L₁ L₂ d)
    (chainsOf_laws _ _ _ _ _)
    (fold_three_chains tFk tJk t3k _ _ _ h₁ h₂ h₃ d hf e₁ e₂ e₃ G) decides
    (fun rec y τ b ha hb hM => by
      have ho := out_of_acceptKD Kc DK tFk tJk t3k silK FK _ y τ ha
      obtain ⟨s₁, s₂, s₃, -, hstart, hr₁, -, -, -, hfin⟩ :=
        wholeGivesEnds (ckP .two) (DK.at a) _ _ _ _ tFk tJk t3k FK silK rec y τ ho
      have hsil := ((wholeIOR_out_iff (ckP .two) (DK.at a) tFk tJk t3k y τ silK FK.run rec).1
        ((congrArg Option.isSome ho).trans rfl)).2.2.2.1
      have hfirst := first_is tFk tJk t3k (atDesc FK T) (fun _ _ => true) (fun _ _ => true)
        (fun _ _ => true) fit rec y τ b hb
      rw [(runsAtDesc (ckP .two) (DK.at a) all _ X₁ X₂ W FK T hO).1, hr₁] at hfirst
      have hb1 : b = ((FK.pub rec, s₁), b.2) := Prod.ext (Option.some.inj hfirst).symm rfl
      rw [hb1] at hM
      exact tie rec y τ s₁ s₂ s₃ b.2 hstart hsil hfin hM)
    Tl.W.depthReqT
    (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₁⟩))
      (max_le (le_trans (mul_le_mul_right (worst_le b₂') _) hc)
        (worst_le (show Err.Below _ U.εs from ⟨by simp, b₃⟩))))

end VerifiableInference.OnPublicFiles

#print axioms TypedOracleCompiler.Joined.sound_of_plain
#print axioms TypedOracleCompiler.Joined.keySound_plainYes
#print axioms VerifiableInference.OnPublicFiles.keySound_at_desc
