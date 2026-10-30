-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/BothAtDescFin.lean: `proofSound_at_descB` (Johnson/Desc/Plain/BothAtDesc.lean)
WITH THE ENDS' PART OF THE LAST TEST IN THE ROW.

Why. The filling `atDesc F T` lays no last test into the row; the description's decision has one
(`FileDescription.fin`). In `proofSound_at_descB` the last test's yes reaches `tie` alone, and there only
beside the FIRST chain's claim: where a description's soundness leans on what its last test says of
the second or third end, `Glues.g₃` could not be met: a limit of the rule's reach.
`atDescFin F g T`, `FinGives F g` and `runGivesRowAtFin` (Johnson/Desc/Sound/DescFin.lean) lay a
test g on the public part and the three ends into the row. Here that filling is taken up in the
plain form. `descDecidesFin`: `DescDecides` at that filling (by its `fileDecides` | `wholeMono` and
`runGivesRowAtFin`). `proofSound_at_descB_fin`: the premises of `proofSound_at_descB` read at
`atDescFin F g T`, and ONE MORE: `FinGives F g` (free at g := "yes always", where it is
`proofSound_at_descB`: `atDescFin_true` is by rfl). `Glues.g₃`'s premise "T.fin a.1 b.1 = true" now
reads g at the third chain's last record's own copy of the public part and of the two earlier ends.
The section's text is BothAtDesc.lean's, turned by a program (atDesc F T ↦ atDescFin F g T).
Nearest kin: `foldSlotsFin` (DescFin.lean): the knowledge form's twin.
Limits: those of BothAtDesc.lean and DescFin.lean. No member with a g that says no anywhere.

-/
import Johnson.Desc.Plain.BothAtDesc
import Johnson.Desc.Sound.DescFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- **Where the file's verifier with the description's own decision says yes, the three reductions
in a row put out**, at the filling with g, at every instance with the same public part. -/
theorem descDecidesFin (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ W TF TJ T3 : Type) (tF :
    TF)
    (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
    (T : ThreeAt C D all F X₁ X₂ W) (okF : Xi → TF → Bool) (okJ : F.XiPub × F.S₁ → TJ → Bool)
    (ok3 : F.XiPub × F.S₁ × F.S₂ → T3 → Bool) (silent : Xi → TF → TJ → T3 → Bool)
    (P : ((atDescFin F g T).row tF tJ t3 okF okJ ok3).Snd) (hO : OfDesc F T) (hg : FinGives F g)
    (hfit : RowFit D all all) (hF : ∀ x a b c, silent x a b c = true → okF x a = true)
    (hJ : ∀ x a b c v x₁, silent x a b c = true → (atDescFin F g T).run₁ x v = some x₁ →
      okJ x₁ b = true)
    (h3 : ∀ x a b c v v' x₁ x₂, silent x a b c = true → (atDescFin F g T).run₁ x v = some x₁ →
      (atDescFin F g T).run₂ x₁ v' = some x₂ → ok3 x₂ c = true)
    (x x' : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Iop.Tr (chainsOf C D tF tJ t3).sh)
    (hp : F.pub x' = F.pub x) (hs : ∀ a b c, silent x a b c = true → silent x' a b c = true)
    (h : (reductionOfWholeFile C D tF tJ t3 silent F.run).out x y τ = some ()) :
    ((((atDescFin F g T).row tF tJ t3 okF okJ ok3).links P).all.out (x', y) τ).isSome = true := by
  refine fileDecides C D all Xi _ _ _ _ _ F.Cl W TF TJ T3 tF tJ t3 (atDescFin F g T) okF okJ ok3
    silent P hfit hF hJ h3 x' y τ ?_
  refine wholeMono C D Xi TF TJ T3 tF tJ t3 silent silent F.run _ x x' hs ?_ y τ h
  intro v₁ v₂ v₃ hy
  have k := runGivesRowAtFin C D all Xi X₁ X₂ W F g T hO hg x v₁ v₂ v₃ hy
  have e : (atDescFin F g T).run₁ x' = (atDescFin F g T).run₁ x := by
    show (atDesc F T).run₁ x' = (atDesc F T).run₁ x
    rw [(runsAtDesc C D all Xi X₁ X₂ W F T hO).1, descRun₁_reads F x x' hp]
  unfold runRow at k ⊢
  rw [e]
  exact k

end VerifiableInference.Desc.Sound

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
  (T : ThreeAt (ckP .two) (DP.at a) all F X₁ X₂ W) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
  (Pl : PPlaces (DP.at a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDescFin F g T).p₁ (atDescFin F g T).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDescFin F g T).p₂ (atDescFin F g T).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDescFin F g T).p₃ (atDescFin F g T).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at a) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at a) all).Str → κ)

/-- The proof file in the plain form, at the description's own three folds, WITH THE ENDS' PART g OF
THE LAST TEST IN THE ROW. -/
abbrev plainPF : PlainFile (chainsOf (ckP .two) (DP.at a) tFp tJp t3p)
    ((Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str) :=
  plainOf tFp tJp t3p (atDescFin F g T) Pl (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁
      h₂
    h₃ M L₁ L₂ d

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- **`proofSound_at_descB` with the ends' part of the last test in the row**: `Glues.g₃` may now
lean on g's yes at the third chain's last record. -/
theorem proofSound_at_descB_fin (w₀ : Kc.conf.Cells) (hO : OfDesc F T) (hg : FinGives F g) (hf :
    (atDescFin F g T).Fits)
    (fit : RowFit (DP.at a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDescFin F g T).p₁ :: (atDescFin F g T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 ((atDescFin F g T).p₂ :: (atDescFin F g T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDescFin F g T).p₃ :: (atDescFin F g T).l₃))
    (G : Glues (atDescFin F g T) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (F₁ : Kc.conf.Rec → (oneExternalString (2 ^ (DP.at a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainPF Kc DP tFp tJp t3p F all T g Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDescFin F g T).in₂ b.1, b.2) = F₁ rec y)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at a) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDescFin F g T).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDescFin F g T).p₁ (atDescFin F g T).l₁ (DP.at a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDescFin F g T).p₂ (atDescFin F g T).l₂ (DP.at a).ds₂ h₂) U.εs)
    (b₃ : Err.Below (errOwn (atDescFin F g T).p₃ (atDescFin F g T).l₃ (DP.at a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
                                                               F.run eL N early none) P Tl U) := by
  have decides : ∀ x rec y (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
      (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run).accept (x, rec) y τ = true →
      ((plainPF Kc DP tFp tJp t3p F all T g Pl h₁ h₂ h₃ M L₁ L₂ d).links.all.out
        ((early x, rec), y) τ).isSome = true := by
    intro x rec y τ ha
    have ho := out_of_acceptP Kc DP tFp tJp t3p silP F _ y τ ha
    have ho' := Sound.wholeMono (ckP .two) (DP.at a) _ _ _ _ tFp tJp t3p silP
      (fun _ _ _ _ => true) F.run F.run (x, rec) (x, rec) (fun _ _ _ _ => rfl)
      (fun _ _ _ h => h) y τ ho
    exact descDecidesFin (ckP .two) (DP.at a) all _ X₁ X₂ W _ _ _ tFp tJp t3p F g T (fun _ _ =>
        true)
      (fun _ _ => true) (fun _ _ => true) (fun _ _ _ _ => true)
      (idleSnd tFp tJp t3p (atDescFin F g T) _ _ _ h₁ h₂ h₃) hO hg fit (fun _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl) (x, rec) (early x, rec) y τ
      (pubEarly x rec) (fun _ _ _ _ => rfl) ho'
  exact proofSound_plainJB
    ((filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early none).withProvers P)
    (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run) rfl Kc.conf.Rno w₀
    (plainPF Kc DP tFp tJp t3p F all T g Pl h₁ h₂ h₃ M L₁ L₂ d)
    (k₁ := fun b => key 0 ((atDescFin F g T).in₂ b.1, b.2)) (k₂ := fun _ => ()) rfl
    (fold_three_chainsB tFp tJp t3p _ _ _ h₁ h₂ h₃ d key hf e₁ e₂ e₃ G) rfl F₁ oneKey
    (fun _ _ => ()) (fun _ _ _ _ => rfl) decides
    (fun x rec y τ b ha hb hM => by
      have ho := out_of_acceptP Kc DP tFp tJp t3p silP F _ y τ ha
      obtain ⟨s₁, s₂, s₃, -, hstart, hr₁, -, -, -, hfin⟩ :=
        wholeGivesEnds (ckP .two) (DP.at a) _ _ _ _ tFp tJp t3p F silP (x, rec) y τ ho
      have hsil := ((wholeIOR_out_iff (ckP .two) (DP.at a) tFp tJp t3p y τ silP F.run (x, rec)).1
        ((congrArg Option.isSome ho).trans rfl)).2.2.2.1
      have hfirst := first_is tFp tJp t3p (atDescFin F g T) (fun _ _ => true) (fun _ _ => true)
        (fun _ _ => true) fit (early x, rec) y τ b hb
      have hfirst : (atDesc F T).run₁ (early x, rec) _ = some b.1 := hfirst
      rw [(runsAtDesc (ckP .two) (DP.at a) all _ X₁ X₂ W F T hO).1,
        descRun₁_reads F (x, rec) (early x, rec) (pubEarly x rec), hr₁] at hfirst
      have hb1 : b = ((F.pub (x, rec), s₁), b.2) :=
        Prod.ext (Option.some.inj hfirst).symm rfl
      rw [hb1] at hM
      exact tie x rec y τ s₁ s₂ s₃ b.2 hstart hsil hfin hM)
    (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₁⟩))
      (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₂⟩))
        (worst_le (show Err.Below _ U.εs from ⟨by simp, b₃⟩))))

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Desc.Sound.descDecidesFin
#print axioms VerifiableInference.OnPublicFiles.proofSound_at_descB_fin
