-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/AtDesc.lean: THE PROOF FILE's HYPOTHESIS OF THE TOP, `CompilerSoundnessConditionStatements.proofSound`, AT A
DESCRIPTION's OWN DECISION (runP := `FileDescription.run`, Johnson/Desc/Block.lean), FROM ONE PLAIN LAW A
BLOCK (`Leads`; the shared chain's blocks: `LeadsK`): no witness, no extractor.

Taken from Johnson/Desc/Sound/ (facts about the fold, each a theorem there): `atDesc`, `OfDesc`;
`runsAtDesc`, `descRun₁_reads`, `descDecides`, `wholeMono`, `wholeGivesEnds`.

  `all_eq`: the three decisions of `plainOf` in a row decide as the library's row.
  `first_is`: what the row's first stage hands on, on the first part of a transcript of the whole
    file, is the first run's value ON THE FILE's OWN FIRST VIEW.
  `proofSound_at_desc`: the theorem. ITS PREMISES:
    hO · hf · fit: the pieces hold F's own blocks; their stretches are the file's chains; the data
    fit.
    e₁ · e₂ · e₃: ONE LAW A BLOCK. G: three implications without a game, at the chains' ends.
    pubEarly: `early` keeps the public part. oneKey: what the first chain hands on has a key that is
    a function of the record and the stored table alone.
    tie: THE MEANING, AND THE THREE GAPS' HOME: handed, at the instance (x, rec) ITSELF and on the
    very transcript: the test on the instance has passed (`okStart`); the test on what the three
    silent rounds sent ON THAT TRANSCRIPT has passed (`silP`); the last test has passed AT THE THREE
    ENDS (`fin`); and "the first condition at the early part → M at (the public part, THE SAME FIRST
    END)":
    it owes: the stored table decodes to nothing, or the object's relation at x.
    b₁ · b₂ · b₃: every block's errors in a row are shares of at most εs: NO FACTOR N.

Limits. A rule: no block of the protocol meets a premise. All of the meaning sits in `tie`, M, and
the blocks' relations. A description that never says yes meets all for nothing. The witness map is
constant. Nothing on acceptance.

-/
import Johnson.Desc.Plain.FileChains
import Johnson.Flat.ProofOfRowProofs
import Johnson.Desc.Sound.DescDecidesProofs
import Johnson.TypedOracleCompiler.Joined.ProofLinksTop
import Johnson.EntryRec.AtFiles
import OnBytes.Maker.WholeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (steps)
open _root_.TypedOracleCompiler.Joined (PlainFile)
open VerifiableInference.Desc.Sound

section Row
variable {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Pl : PPlaces D all S₁ S₂ S₃)
  (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
  (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
  (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
  (M : Y × (oneExternalString (2 ^ D.a) SgX).Str → X₁ × (EAll D all).Str → Prop)
  (L₁ : X₁ × (EAll D all).Str → Prop) (L₂ : X₂ × (EAll D all).Str → Prop)
  (d : X₁ × (EAll D all).Str)

/-- Data for the library's `Row.links` that say nothing: what the three in a row put out does not
hang on them. -/
def idleSnd : (T.row tF tJ t3 okF okJ ok3).Snd where
  W₀ := Unit
  W₁ := Unit
  W₂ := Unit
  on₀ := fun _ => True
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := fun _ _ => True
  R₁ := fun _ _ => True
  R₂ := fun _ _ => True
  e₁ := fun _ _ _ => ()
  e₂ := fun _ _ _ => ()
  e₃ := fun _ _ _ => ()
  ε₁ := (0, errOwn T.p₁ T.l₁ D.ds₁ h₁)
  ε₂ := (0, errOwn T.p₂ T.l₂ D.ds₂ h₂)
  ε₃ := (0, errOwn T.p₃ T.l₃ D.ds₃ h₃)
  d₀ := ()
  d₁ := ()

/-- The three decisions of `plainOf` in a row are those of the library's list at the row. -/
theorem all_eq (a : Y × (oneExternalString (2 ^ D.a) SgX).Str) (τ : Iop.Tr (chainsOf C D tF tJ t3).sh) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).links.all.out a τ =
      ((T.row tF tJ t3 okF okJ ok3).links (idleSnd tF tJ t3 T okF okJ ok3 h₁ h₂ h₃)).all.out a τ :=
  rfl

/-- **What the row's first stage hands on is the first run's value on the file's own first view.**
-/
theorem first_is (fit : RowFit D all all) (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Iop.Tr (chainsOf C D tF tJ t3).sh) (b : X₁ × (EAll D all).Str)
    (hb : (T.row tF tJ t3 okF okJ ok3).S₁.ior.red.out (x, y)
      (Iop.Tr.fst (s := (chainsOf C D tF tJ t3).c₁)
        (t := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) τ) = some b) :
    T.run₁ x (view₁ C D tF tJ t3 y τ) = some b.1 := by
  have e : (T.row tF tJ t3 okF okJ ok3).S₁.ior.red.out (x, y)
      (Iop.Tr.fst (s := (chainsOf C D tF tJ t3).c₁)
        (t := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) τ) =
      ((if okF x ((chainsOf C D tF tJ t3).msgF τ).2 then
        (if sTests C (D.st₁ all) (imp₁ D all y) ((chainsOf C D tF tJ t3).tr₁ τ) then
          T.run₁ x (sView C (D.st₁ all) (imp₁ D all y) ((chainsOf C D tF tJ t3).tr₁ τ)) else none)
        else none).map fun xo => (xo, (T.row tF tJ t3 okF okJ ok3).S₁.ior.imp y
          (Iop.Tr.fst (s := (chainsOf C D tF tJ t3).c₁)
            (t := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) τ))) := rfl
  rw [e, sView₁ C D all all y _ ((chainsOf C D tF tJ t3).tr₂ τ) ((chainsOf C D tF tJ t3).tr₃ τ)
    fit] at hb
  obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 hb
  split at hx
  · split at hx
    · exact hx
    · cases hx
  · cases hx

end Row
end VerifiableInference.Desc.Plain

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

/-- The proof file in the plain form, at the description's own three folds; no test on the silent
rounds stands in the row. -/
abbrev plainP : PlainFile (chainsOf (ckP .two) (DP.at a) tFp tJp t3p)
    ((Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str) :=
  plainOf tFp tJp t3p (atDesc F T) Pl (fun _ _ => true) (fun _ _ => true) (fun _ _ => true) h₁ h₂
    h₃ M L₁ L₂ d

/-- The verifier's yes in the description's form is the reduction's: the library's `out_of_accept`
(Johnson/Flat/ProofOfRowProofs.lean) at the description's own run. -/
theorem out_of_acceptP (b : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh)
    (h : (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run).accept b y τ = true) :
    (reductionOfWholeFile (ckP .two) (DP.at a) tFp tJp t3p silP F.run).out b y τ = some () :=
  out_of_accept Kc DP tFp tJp t3p silP F.run b y τ h

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- **`CompilerSoundnessConditionStatements.proofSound` at a description's own decision, from one plain law a block.** -/
theorem proofSound_at_desc (w₀ : Kc.conf.Cells) (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (fit : RowFit (DP.at a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsK key Pl.on₂ Pl.Q₂ 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
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
                                                               F.run eL N early none) P Tl U) := by
  have decides : ∀ x rec y (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
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
  exact proofSound_plainJ
    ((filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early none).withProvers P)
    (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run) rfl Kc.conf.Rno w₀
    (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d)
    (k₁ := fun b => key 0 ((atDesc F T).in₂ b.1, b.2)) (k₂ := fun _ => ()) rfl
    (fold_three_chainsK tFp tJp t3p _ _ _ h₁ h₂ h₃ d key hf e₁ e₂ e₃ G) rfl F₁ oneKey
    (fun _ _ => ()) (fun _ _ _ _ => rfl) decides
    (fun x rec y τ b ha hb hM => by
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
      exact tie x rec y τ s₁ s₂ s₃ b.2 hstart hsil hfin hM)
    (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₁⟩))
      (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₂⟩))
        (worst_le (show Err.Below _ U.εs from ⟨by simp, b₃⟩))))

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Desc.Plain.first_is
#print axioms VerifiableInference.OnPublicFiles.proofSound_at_desc
