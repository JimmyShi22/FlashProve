-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfRowProofs.lean: the proofs of the six statements of
Johnson/Flat/ProofOfRow.lean.

Theorems with their proofs; each has the statement's name with a small first letter. What is said,
under which premises, and the limits: that file's head. NO VALUE OF THAT FRAME HAS RUN ON A REAL
PROOF. How. `wholeMono`: the whole's output written out (`wholeIOR_out_eq`,
OnBytes/Maker/RowWhole.lean). `knowsJComap`: the first link's bad sets and keys read through the
map; the other four fields are unturned. `rowDecides`: `wholeMono`, `rowOf_of_whole`, `Row.all_out`.
`batIs`: by unfolding. `proofSoundOfRowNamed`: `sndB_of_file_links`
(OnBytes/TypedOracleCompiler/Joined/MidLinks.lean). `proofSoundOfRow`: `proofSound_top_links`
(Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean) and `worst_le`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ProofOfRow

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

theorem wholeMono : WholeMono := by
  intro C D TF TJ T3 tF tJ t3 Y silent run run' x x' h y τ ho
  rw [wholeIOR_out_eq] at ho ⊢
  split at ho
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨p₁, p₂⟩, p₃⟩, f₁⟩, f₂⟩, f₃⟩, c⟩, _⟩, hr⟩ := hc
    rw [if_pos]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨p₁, p₂⟩, p₃⟩, f₁⟩, f₂⟩, f₃⟩, c⟩, trivial⟩, h _ _ _ hr⟩
  · cases ho

theorem knowsJComap : KnowsJComap := by
  intro G Y Y' E C N κ₁ κ₂ k₁ k₂ f h
  have key : ∀ a : Fin N → Option (Y' × E.Str), IOR.SameKey (Prod.snd : Y' × E.Str → E.Str) a →
      IOR.SameKey (Prod.snd : Y × E.Str → E.Str) fun j => (a j).map fun b => (f b.1, b.2) := by
    intro a ha j j' x x' hx hx'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hx'
    exact ha j j' b b' hb hb'
  refine ⟨⟨?_, ?_⟩, h.l₂, h.l₃, fun a τ b ha hb => h.hands₁ (f a.1, a.2) τ b ha hb, h.hands₂⟩
  · obtain ⟨bad, h1, h2⟩ := h.l₁.know
    refine ⟨fun a => bad (f a.1, a.2), fun a τ b w ha hτ hb hw => h1 (f a.1, a.2) τ b w ha hτ hb hw,
      fun a ha => ?_⟩
    refine cast (congrArg (JWithin N _ _ _) (funext fun j => ?_)) (h2 _ (key a ha))
    cases a j <;> rfl
  · intro a ha τ
    refine cast (congrArg (IOR.SameKey k₁) (funext fun j => ?_)) (h.l₁.adm _ (key a ha) τ)
    cases a j <;> rfl

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
  (run₁ : Kc.conf.X × Kc.conf.Rec → PQ.View → Option X₁) (run₂ : X₁ → PQ.View → Option X₂)
  (run₃ : X₂ → PQ.View → Bool)
  (S : (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd)

theorem rowDecides : RowDecides Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S := by
  intro fit gives kept x rec y τ h
  have h1 := wholeMono (ckP .two) (DP.at a) _ _ _ tFp tJp t3p _ silP runP
    (runRow run₁ run₂ run₃) (x, rec) (early x, rec)
    (fun v₁ v₂ v₃ hv => by
      have g := gives _ _ _ _ hv
      unfold runRow at g ⊢
      rw [kept]
      exact g) y τ h
  have h2 := rowOf_of_whole (ckP .two) (DP.at a) tFp tJp t3p L₁ L₂ (fun _ _ => true)
    (fun _ _ => true) (fun _ _ => true) run₁ run₂ run₃ (fun _ _ _ _ => true) fit
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    (early x, rec) y τ h1
  rw [Row.all_out]
  exact h2

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
    none).Provers)
  (T : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
                                     none) P)

theorem batIs : BatIs Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early P := by
  exact rfl

variable {κ₁ κ₂ : Type} (k₁ : X₁ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₁.Str → κ₁)
  (k₂ : X₂ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₂.Str → κ₂)
  (toW : S.W₀ → Kc.conf.Cells)

/-- The verifier's yes in the description's form is the reduction's. -/
theorem out_of_accept (b : Kc.conf.X × Kc.conf.Rec) (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh)
    (h : (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP runP).accept b y τ = true) :
    (reductionOfWholeFile (ckP .two) (DP.at a) tFp tJp t3p silP runP).out b y τ = some () := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h
  cases u
  exact hu

theorem proofSoundOfRowNamed :
    ProofSoundOfRowNamed Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early L₁ L₂ run₁
      run₂ run₃ S P U k₁ k₂ toW := by
  intro fit gives kept knows ties b₁ b₂ b₃
  refine ⟨Err.Below.app b₁ (Err.Below.app b₂ b₃), fun rec => ?_⟩
  exact sndB_of_file_links
    ((filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early none).withProvers P)
    (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP runP) Kc.conf.Rno
    (witP Kc DP tFp tJp t3p early L₁ L₂ run₁ run₂ run₃ S toW) N early knows
    (fun x rec y τ ha =>
      (congrArg Option.isSome (rowDecides Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S
        fit gives kept x rec y τ (out_of_accept Kc DP tFp tJp t3p silP runP _ y τ ha))).trans rfl)
    (fun x rec y τ ha hr =>
      ties x rec y τ (out_of_accept Kc DP tFp tJp t3p silP runP _ y τ ha) hr) rec

theorem proofSoundOfRow :
    ProofSoundOfRow Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early L₁ L₂ run₁
      run₂ run₃ S P T U k₁ k₂ toW := by
  intro fit gives kept knows ties b₁ b₂ b₃
  exact proofSound_top_links (KJ := linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S)
    (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early none) P T U
    (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP runP)
    (batIs Kc DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early P) toW rfl knows
    (fun x rec y τ ha =>
      (congrArg Option.isSome (rowDecides Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S
        fit gives kept x rec y τ (out_of_accept Kc DP tFp tJp t3p silP runP _ y τ ha))).trans rfl)
    (fun x rec y τ ha hr =>
      ties x rec y τ (out_of_accept Kc DP tFp tJp t3p silP runP _ y τ ha) hr)
    (max_le (worst_le b₁) (max_le (worst_le b₂) (worst_le b₃)))

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.wholeMono
#print axioms VerifiableInference.OnPublicFiles.knowsJComap
#print axioms VerifiableInference.OnPublicFiles.rowDecides
#print axioms VerifiableInference.OnPublicFiles.batIs
#print axioms VerifiableInference.OnPublicFiles.proofSoundOfRowNamed
#print axioms VerifiableInference.OnPublicFiles.proofSoundOfRow
