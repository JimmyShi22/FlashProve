-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/CarrySWhole.lean: a reading of a whole file as data (`reductionOfWholeFile`,
OnBytes/Maker/Whole.lean) as a typed protocol, from three lists of maps, one for each hash chain.



A key file and a proof file as data are `reductionOfWholeFile` over the rounds `chainsOf`: the front, the first
chain's written rounds, the joining round, the shared chain's, the seam, the last chain's. Given for
each chain how its written rounds are read as typed rounds (`Maps`, OnBytes/Flat/CarrySMaps.lean),
here is the reading of the whole (`CarryS.file`, OnBytes/Flat/CarrySFile.lean) with what is asked of
a reading but for the typed verifier's yes: the written counts bear the typed ones; they are small
as shares; and WHERE THE FILE's VERIFIER SAYS YES THE TRANSCRIPT HAS AN IMAGE, which is named.

Main names:
  `Maps.pass_of_passT`: where all tests of work of a chain pass, those of the rounds read pass.
  `CarryS.tr_file'`: `tr_file` at any transcript of the whole, through its three parts.
  `wholeMap D tF tJ t3 M₁ M₂ M₃`: the reading. `wholeErr`: the written counts. `wholeView`: the
    image.
  `fits_whole`: from `Maps.OK` of the three.
  `below_whole`, `below_whole_pow`: from `Maps.Held εs`, from `Maps.HeldN k` of the three;
    `below_whole_one`: the same in the form with the shared rounds' counts taken once
    (`Err.timesShared 1`): a file that stands alone under its binding tree.
  `tr_whole`: where the three chains' tests of work pass, the image is `wholeView`.
  `tr_whole_of_out`: where the file's verifier says yes, the image is `wholeView`.

Limits: that the typed verifier says yes at `wholeView` is not shown. No map is made here and none
is shown to be as asked. `Maps` go round by round, each map blind to the rounds before: so
`wholeMap` cannot lay what went out in an earlier round as a later typed round's oracle, though a
`CarryS` can (`CarryS.fileD`, `CarryS.step`). The front, the joining round and the seam bear the
count 0: a skipped round's verifier message is in no image, so whether the prover has lost does not
hang on it (`CarryS.doomed`). Shared rounds' counts taken N > 1 times:
OnBytes/Flat/CarrySFileN.lean.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Flat.CarrySFile
import OnBytes.Flat.CarrySNum
import OnBytes.Maker.Whole
import Johnson.TypedOracleCompiler.RecCompile.Bcs

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob Run Run.PQ OnBytes.Maker OnBytes.Slice
open _root_.Compile.Joined (Chains)
open scoped ENNReal

/-- Where all tests of work of a chain pass, those of the rounds that are read pass. -/
theorem Maps.pass_of_passT : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s')
    (τ : Tr (uLT (ckP .two) ds)), passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true →
    M.pass τ = true
  | _, _, .nil, _, _ => rfl
  | _, _, .step _ rest, (_, _, τ), h =>
      Bool.and_eq_true_iff.2 ⟨(Bool.and_eq_true_iff.1 h).1,
        pass_of_passT rest τ (Bool.and_eq_true_iff.1 h).2⟩
  | _, _, .skip _ rest, (_, _, τ), h => pass_of_passT rest τ (Bool.and_eq_true_iff.1 h).2

/-- A transcript of the whole is made of its parts. -/
theorem tr_parts (G : Chains) (τ : Tr G.sh) :
    τ = ((τ.1, τ.2.1, Tr.app (G.tr₁ τ) (((G.trJ τ).1, (G.trJ τ).2.1, Tr.app (G.tr₂ τ)
      (((Tr.snd (s := G.s₂) (G.trJ τ).2.2).1, (Tr.snd (s := G.s₂) (G.trJ τ).2.2).2.1, G.tr₃ τ) :
        Tr G.sh₃)) : Tr G.shJ)) : Tr G.sh) := by
  obtain ⟨mF, cF, σ⟩ := τ
  show (mF, cF, σ) = (mF, cF, Tr.app (Tr.fst σ) _)
  refine congrArg (fun z => (mF, cF, z)) ?_
  refine (Tr.app_fst_snd (s := G.s₁) σ).symm.trans (congrArg (Tr.app (Tr.fst σ)) ?_)
  exact congrArg
    (fun z => (((Tr.snd (s := G.s₁) σ : Tr G.shJ).1, (Tr.snd (s := G.s₁) σ : Tr G.shJ).2.1, z) :
      Tr G.shJ))
    (Tr.app_fst_snd (s := G.s₂) (Tr.snd (s := G.s₁) σ : Tr G.shJ).2.2).symm

/-- The image of any transcript of the whole, through its three parts. -/
theorem CarryS.tr_file' {G : Chains} {s₁' s₂' s₃' : Shape} (F₁ : CarryS G.s₁ s₁')
    (F₂ : CarryS G.s₂ s₂') (F₃ : CarryS G.s₃ s₃') (τ : Tr G.sh) :
    (CarryS.file G F₁ F₂ F₃).tr τ =
      (F₁.tr (G.tr₁ τ)).bind fun a => (F₂.tr (G.tr₂ τ)).bind fun b => (F₃.tr (G.tr₃ τ)).map fun c =>
        Tr.app a (Tr.app b c) :=
  (congrArg (CarryS.file G F₁ F₂ F₃).tr (tr_parts G τ)).trans
    (CarryS.tr_file F₁ F₂ F₃ _ _ _ _ _ _ _ _ _)

section Whole
variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {s₁' s₂' s₃' : Shape}
  (M₁ : Maps D.ds₁ s₁') (M₂ : Maps D.ds₂ s₂') (M₃ : Maps D.ds₃ s₃')

/-- The reading of the whole file. -/
def wholeMap : CarryS (chainsOf (ckP .two) D tF tJ t3).sh (s₁' ++ (s₂' ++ s₃')) :=
  CarryS.file (chainsOf (ckP .two) D tF tJ t3) M₁.carry M₂.carry M₃.carry

/-- The written counts of the whole file. -/
def wholeErr (δ₁ : Err s₁') (δ₂ : Err s₂') (δ₃ : Err s₃') :
    Err (chainsOf (ckP .two) D tF tJ t3).sh :=
  errFile (chainsOf (ckP .two) D tF tJ t3) (M₁.err δ₁) (M₂.err δ₂) (M₃.err δ₃)

/-- The image of a transcript of the whole file. -/
def wholeView (τ : Tr (chainsOf (ckP .two) D tF tJ t3).sh) : Tr (s₁' ++ (s₂' ++ s₃')) :=
  Tr.app (M₁.view ((chainsOf (ckP .two) D tF tJ t3).tr₁ τ))
    (Tr.app (M₂.view ((chainsOf (ckP .two) D tF tJ t3).tr₂ τ))
      (M₃.view ((chainsOf (ckP .two) D tF tJ t3).tr₃ τ)))

variable {M₁ M₂ M₃}

/-- The written counts bear the typed ones. -/
theorem fits_whole (h₁ : M₁.OK) (h₂ : M₂.OK) (h₃ : M₃.OK) (δ₁ : Err s₁') (δ₂ : Err s₂')
    (δ₃ : Err s₃') :
    (wholeMap D tF tJ t3 M₁ M₂ M₃).Fits (Err.app δ₁ (Err.app δ₂ δ₃))
      (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃) :=
  CarryS.fits_file (M₁.fits h₁ δ₁) (M₂.fits h₂ δ₂) (M₃.fits h₃ δ₃)

/-- The written counts are shares of at most εs. -/
theorem below_whole (h₁ : M₁.OK) (h₂ : M₂.OK) (h₃ : M₃.OK) {δ₁ : Err s₁'} {δ₂ : Err s₂'}
    {δ₃ : Err s₃'} {εs : ℝ≥0∞} (b₁ : M₁.Held εs δ₁) (b₂ : M₂.Held εs δ₂) (b₃ : M₃.Held εs δ₃) :
    Err.Below (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃) εs :=
  below_file (M₁.below_err h₁ δ₁ b₁) (M₂.below_err h₂ δ₂ b₂) (M₃.below_err h₃ δ₃ b₃)

/-- The same at 2^-k, from comparisons of natural numbers. -/
theorem below_whole_pow (h₁ : M₁.OK) (h₂ : M₂.OK) (h₃ : M₃.OK) {δ₁ : Err s₁'} {δ₂ : Err s₂'}
    {δ₃ : Err s₃'} {k : ℕ} (b₁ : M₁.HeldN k δ₁) (b₂ : M₂.HeldN k δ₂) (b₃ : M₃.HeldN k δ₃) :
    Err.Below (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃) ((2 : ℝ≥0∞)⁻¹ ^ k) :=
  below_whole D tF tJ t3 h₁ h₂ h₃ (M₁.held_of_nat δ₁ b₁) (M₂.held_of_nat δ₂ b₂)
    (M₃.held_of_nat δ₃ b₃)

/-- The same in the form with the shared rounds' counts taken once. -/
theorem below_whole_one (h₁ : M₁.OK) (h₂ : M₂.OK) (h₃ : M₃.OK) {δ₁ : Err s₁'} {δ₂ : Err s₂'}
    {δ₃ : Err s₃'} {εs : ℝ≥0∞} (b₁ : M₁.Held εs δ₁) (b₂ : M₂.Held εs δ₂) (b₃ : M₃.Held εs δ₃) :
    Err.Below (Err.timesShared 1 (chainsOf (ckP .two) D tF tJ t3).ann
      (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃)) εs := by
  rw [TypedOracleCompiler.Compile.Batch.timesShared_one]
  exact below_whole D tF tJ t3 h₁ h₂ h₃ b₁ b₂ b₃

variable (M₁ M₂ M₃)

/-- Where the three chains' tests of work pass, the image is `wholeView`. -/
theorem tr_whole (τ : Tr (chainsOf (ckP .two) D tF tJ t3).sh)
    (p₁ : passT (ckP .two) D.ds₁ (rhoT (ckP .two) D.ds₁
      ((chainsOf (ckP .two) D tF tJ t3).tr₁ τ)) = true)
    (p₂ : passT (ckP .two) D.ds₂ (rhoT (ckP .two) D.ds₂
      ((chainsOf (ckP .two) D tF tJ t3).tr₂ τ)) = true)
    (p₃ : passT (ckP .two) D.ds₃ (rhoT (ckP .two) D.ds₃
      ((chainsOf (ckP .two) D tF tJ t3).tr₃ τ)) = true) :
    (wholeMap D tF tJ t3 M₁ M₂ M₃).tr τ = some (wholeView D tF tJ t3 M₁ M₂ M₃ τ) := by
  unfold wholeMap
  rw [CarryS.tr_file', M₁.tr_of_pass _ (M₁.pass_of_passT _ p₁),
    M₂.tr_of_pass _ (M₂.pass_of_passT _ p₂), M₃.tr_of_pass _ (M₃.pass_of_passT _ p₃)]
  rfl

/-- **Where the file's verifier says yes, the transcript has the image `wholeView`.** -/
theorem tr_whole_of_out {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
    (run : Xi → View → View → View → Bool) (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) D tF tJ t3).sh)
    (h : (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).out x y τ = some ()) :
    (wholeMap D tF tJ t3 M₁ M₂ M₃).tr τ = some (wholeView D tF tJ t3 M₁ M₂ M₃ τ) := by
  have h2 := (Option.ite_none_right_eq_some.1 h).1
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨p₁, p₂⟩, p₃⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h2
  exact tr_whole D tF tJ t3 M₁ M₂ M₃ τ p₁ p₂ p₃

end Whole

end OnBytes.Flat
