-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/BothAtDescSteps.lean: the two steps that stand inline in the proof of
`proofSound_at_descB` (Johnson/Desc/Plain/BothAtDesc.lean), cut out as named lemmas: each ends at a
premise of `proofSound_plainJB` at a description's own plain file: the first token for token, the
second with its last term unfolded.

`proofSound_plainJB` asks, beside the three chains' laws, two facts on the decision: `decides` (a
yes of the decision gives an output of the three chains in a row) and `ties` (a yes, the first
chain's output and what M says of it give the relation of the top). `proofSound_at_descB` pays
both at P := `plainP …`, D := `wholeDesc … silP F.run`, inside its own proof, where nobody can call
them.
Whoever wants to END AT THESE TWO PREMISES, and not at `CompilerSoundnessConditionStatements.proofSound`, needs them by name. The
proofs are the inline lines, unturned. BothAtDesc.lean does not turn. Statements and proofs; no new
reasoning.
Main names (namespace `VerifiableInference.OnPublicFiles`):
  `decides_at_desc`: under `OfDesc F T`, `RowFit` and "F.pub does not feel `early`": a yes of
    `wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run` at (x, rec), y, τ gives an output of
    `(plainP …).links.all` at ((early x, rec), y), τ.
  `ties_of_tie`: under the same three and the premise `tie` of `proofSound_at_descB`, in its own
    words (okStart, silP, fin at s₁ s₂ s₃, and what M says at ((F.pub (x, rec), s₁), z), give
    "D y rec = none, or it is some i with Rno i x w₀"): the premise `ties` of `proofSound_plainJB`,
    its end written as the disjunction to which `relB` unfolds: "exact" or "show" ends at `ties`
    with it; a "rw" on `relB` will not find it.
  `proofSound_at_descB_bySteps`: a check that the two fit: `proofSound_at_descB`'s own statement,
    proved again by `proofSound_plainJB` with the two lemmas in the two places.
Limits: those of BothAtDesc.lean and AtDesc.lean. At `plainP` alone: nothing on the form with a
finish of its own. The premise `tie` is shown of no description here. Nothing on soundness.

-/
import Johnson.Desc.Plain.BothAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

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
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (F : FileDescription (Kc.conf.X × Kc.conf.Rec)) (all : List LeftT) {X₁ X₂ W κ : Type}
  (T : ThreeAt (ckP .two) (DP.at a) all F X₁ X₂ W)
  (Pl : PPlaces (DP.at a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at a) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at a) all).Str → κ)

/-- **A yes of a description's own decision gives an output of its three chains in a row.** The
premise `decides` of `proofSound_plainJB` at `plainP`. -/
theorem decides_at_desc (hO : OfDesc F T) (fit : RowFit (DP.at a) all all)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec)) :
    ∀ x rec y (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
      (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run).accept (x, rec) y τ = true →
      ((plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).links.all.out
        ((early x, rec), y) τ).isSome = true := by
  intro x rec y τ ha
  have ho := out_of_acceptP Kc DP tFp tJp t3p silP F _ y τ ha
  have ho' := Sound.wholeMono (ckP .two) (DP.at a) _ _ _ _ tFp tJp t3p silP
    (fun _ _ _ _ => true) F.run F.run (x, rec) (x, rec) (fun _ _ _ _ => rfl)
    (fun _ _ _ h => h) y τ ho
  exact descDecides (ckP .two) (DP.at a) all _ X₁ X₂ W _ _ _ tFp tJp t3p F T (fun _ _ => true)
    (fun _ _ => true) (fun _ _ => true) (fun _ _ _ _ => true)
    (idleSnd tFp tJp t3p (atDesc F T) _ _ _ h₁ h₂ h₃) hO fit (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl) (x, rec) (early x, rec) y τ
    (pubEarly x rec) (fun _ _ _ _ => rfl) ho'

/-- **From the premise `tie` of `proofSound_at_descB` to the premise `ties` of
`proofSound_plainJB`**, at `plainP`. The end is written as the disjunction to which the top's
relation unfolds. -/
theorem ties_of_tie (w₀ : Kc.conf.Cells) (hO : OfDesc F T) (fit : RowFit (DP.at a) all all)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at a) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F T).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w₀) :
    ∀ x rec y (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) b,
      (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run).accept (x, rec) y τ = true →
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((early x, rec), y)
        (Tr.fst (s := (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₁)
          (t := (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₂ ++
            (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₃) τ) = some b →
      ((plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).on₀ ((early x, rec), y) →
        (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).M ((early x, rec), y) b) →
      Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w₀ := by
  intro x rec y τ b ha hb hM
  have ho := out_of_acceptP Kc DP tFp tJp t3p silP F _ y τ ha
  obtain ⟨s₁, s₂, s₃, -, hstart, hr₁, -, -, -, hfin⟩ :=
    wholeGivesEnds (ckP .two) (DP.at a) _ _ _ _ tFp tJp t3p F silP (x, rec) y τ ho
  have hsil := ((wholeIOR_out_iff (ckP .two) (DP.at a) tFp tJp t3p y τ silP F.run (x, rec)).1
    ((congrArg Option.isSome ho).trans rfl)).2.2.2.1
  have hfirst := first_is tFp tJp t3p (atDesc F T) (fun _ _ => true) (fun _ _ => true)
    (fun _ _ => true) fit (early x, rec) y τ b hb
  rw [(runsAtDesc (ckP .two) (DP.at a) all _ X₁ X₂ W F T hO).1,
    descRun₁_reads F (x, rec) (early x, rec) (pubEarly x rec), hr₁] at hfirst
  have hb1 : b = ((F.pub (x, rec), s₁), b.2) :=
    Prod.ext (Option.some.inj hfirst).symm rfl
  rw [hb1] at hM
  exact tie x rec y τ s₁ s₂ s₃ b.2 hstart hsil hfin hM

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- A check that the two lemmas fit: the statement of `proofSound_at_descB`, by
`proofSound_plainJB` with the two in the two places. -/
theorem proofSound_at_descB_bySteps (w₀ : Kc.conf.Cells) (hO : OfDesc F T)
    (hf : (atDesc F T).Fits) (fit : RowFit (DP.at a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (F₁ : Kc.conf.Rec → (oneExternalString (2 ^ (DP.at a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at a) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F T).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at a).ds₂ h₂) U.εs)
    (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
                                                               F.run eL N early none) P Tl U) :=
  proofSound_plainJB
    ((filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early none).withProvers P)
    (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run) rfl Kc.conf.Rno w₀
    (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d)
    (k₁ := fun b => key 0 ((atDesc F T).in₂ b.1, b.2)) (k₂ := fun _ => ()) rfl
    (fold_three_chainsB tFp tJp t3p _ _ _ h₁ h₂ h₃ d key hf e₁ e₂ e₃ G) rfl F₁ oneKey
    (fun _ _ => ()) (fun _ _ _ _ => rfl)
    (decides_at_desc Kc DP tFp tJp t3p silP early F all T Pl h₁ h₂ h₃ M L₁ L₂ d hO fit pubEarly)
    (ties_of_tie Kc DP tFp tJp t3p silP early F all T Pl h₁ h₂ h₃ M L₁ L₂ d w₀ hO fit pubEarly
      tie)
    (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₁⟩))
      (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₂⟩))
        (worst_le (show Err.Below _ U.εs from ⟨by simp, b₃⟩))))

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.decides_at_desc
#print axioms VerifiableInference.OnPublicFiles.ties_of_tie
#print axioms VerifiableInference.OnPublicFiles.proofSound_at_descB_bySteps
