-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySFile.lean: the maps from the written rounds of a whole file, three hash chains
joined by seals, to the rounds of a typed protocol, from the maps of the three chains.



A file's written rounds are: the front round, the first chain's rounds, the joining round, the
shared chain's rounds, the seam, the last chain's rounds (`Chains`, Compile/Joined/Types.lean). A
typed protocol has none of the front, the joining round and the seam. Here the three chains' maps
(`CarryS`, OnBytes/Flat/CarrySkip.lean) are put in a row, with these three rounds skipped, and what
a reading of a whole file asks is had from the three chains' shares of it.

Main names:
  `CarryS.fileD G F₁ F₂ F₃ : CarryS G.sh (s₁' ++ (s₂' ++ s₃'))`: each chain's maps may read all that
    was written before the chain. `CarryS.file`: the case in which they read nothing of it.
  `errFile G ε₁ ε₂ ε₃`: the written counts of the whole: 0 at the three skipped rounds.
  `tr_fileD`, `tr_file`: the image of a transcript: the three images in a row, of the three chains'
    parts.
  `fits_fileD`, `fits_file`: the written counts bear the typed ones.
  `below_file`: each entry is a share of at most εs, if each chain's is.
The same with the shared rounds' counts taken N times: OnBytes/Flat/CarrySFileN.lean.

Limits: what the three skipped rounds send is in no image: a typed verifier reads it only as far as
the later maps lay it into their rounds. A chain's own rounds that the typed protocol lacks, such as
a sealing round, are skipped inside that chain's maps, not here. No protocol occurs here.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Flat.CarrySApp
import Compile.Joined.Types

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob OnBytes.Slice
open _root_.Compile.Joined (Chains)
open scoped ENNReal

variable (G : Chains) {s₁' s₂' s₃' : Shape}

/-- The three chains' maps in a row; the front, the joining round and the seam are skipped. Each
chain's maps may read all that was written before the chain. -/
def CarryS.fileD (F₁ : G.rF.Msg → G.rF.Chal → CarryS G.s₁ s₁')
    (F₂ : G.rF.Msg → G.rF.Chal → Tr G.s₁ → G.rJ.Msg → G.rJ.Chal → CarryS G.s₂ s₂')
    (F₃ : G.rF.Msg → G.rF.Chal → Tr G.s₁ → G.rJ.Msg → G.rJ.Chal → Tr G.s₂ → G.r3.Msg →
      G.r3.Chal → CarryS G.s₃ s₃') :
    CarryS G.sh (s₁' ++ (s₂' ++ s₃')) :=
  .skip fun mF cF => (F₁ mF cF).app fun τ₁ => .skip fun mJ cJ =>
    (F₂ mF cF τ₁ mJ cJ).app fun τ₂ => .skip fun m3 c3 => F₃ mF cF τ₁ mJ cJ τ₂ m3 c3

/-- The same where no chain's maps read what was written before it. -/
def CarryS.file (F₁ : CarryS G.s₁ s₁') (F₂ : CarryS G.s₂ s₂') (F₃ : CarryS G.s₃ s₃') :
    CarryS G.sh (s₁' ++ (s₂' ++ s₃')) :=
  CarryS.fileD G (fun _ _ => F₁) (fun _ _ _ _ _ => F₂) fun _ _ _ _ _ _ _ _ => F₃

/-- The written counts of the whole. -/
def errFile (ε₁ : Err G.s₁) (ε₂ : Err G.s₂) (ε₃ : Err G.s₃) : Err G.sh :=
  (0, Err.app ε₁ ((0, Err.app ε₂ ((0, ε₃) : Err G.sh₃)) : Err G.shJ))

variable {G}

/-- The image of a transcript of the whole. -/
theorem CarryS.tr_fileD (F₁ : G.rF.Msg → G.rF.Chal → CarryS G.s₁ s₁')
    (F₂ : G.rF.Msg → G.rF.Chal → Tr G.s₁ → G.rJ.Msg → G.rJ.Chal → CarryS G.s₂ s₂')
    (F₃ : G.rF.Msg → G.rF.Chal → Tr G.s₁ → G.rJ.Msg → G.rJ.Chal → Tr G.s₂ → G.r3.Msg →
      G.r3.Chal → CarryS G.s₃ s₃')
    (mF : G.rF.Msg) (cF : G.rF.Chal) (τ₁ : Tr G.s₁) (mJ : G.rJ.Msg) (cJ : G.rJ.Chal) (τ₂ : Tr G.s₂)
    (m3 : G.r3.Msg) (c3 : G.r3.Chal) (τ₃ : Tr G.s₃) :
    (CarryS.fileD G F₁ F₂ F₃).tr
        ((mF, cF, Tr.app τ₁ ((mJ, cJ, Tr.app τ₂ ((m3, c3, τ₃) : Tr G.sh₃)) : Tr G.shJ)) : Tr G.sh) =
      ((F₁ mF cF).tr τ₁).bind fun a => ((F₂ mF cF τ₁ mJ cJ).tr τ₂).bind fun b =>
        ((F₃ mF cF τ₁ mJ cJ τ₂ m3 c3).tr τ₃).map fun c => Tr.app a (Tr.app b c) := by
  show ((F₁ mF cF).app fun τ₁ => .skip fun mJ cJ =>
      (F₂ mF cF τ₁ mJ cJ).app fun τ₂ => .skip fun m3 c3 => F₃ mF cF τ₁ mJ cJ τ₂ m3 c3).tr
    (Tr.app τ₁ ((mJ, cJ, Tr.app τ₂ ((m3, c3, τ₃) : Tr G.sh₃)) : Tr G.shJ)) = _
  rw [CarryS.tr_app]
  show ((F₁ mF cF).tr τ₁).bind (fun a => (((F₂ mF cF τ₁ mJ cJ).app fun τ₂ => .skip fun m3 c3 =>
      F₃ mF cF τ₁ mJ cJ τ₂ m3 c3).tr
    (Tr.app τ₂ ((m3, c3, τ₃) : Tr G.sh₃))).map fun σ' => Tr.app a σ') = _
  rw [CarryS.tr_app]
  show ((F₁ mF cF).tr τ₁).bind (fun a => (((F₂ mF cF τ₁ mJ cJ).tr τ₂).bind fun b =>
    ((F₃ mF cF τ₁ mJ cJ τ₂ m3 c3).tr τ₃).map fun c => Tr.app b c).map fun σ' => Tr.app a σ') = _
  cases (F₁ mF cF).tr τ₁ with
  | none => rfl
  | some a =>
    cases (F₂ mF cF τ₁ mJ cJ).tr τ₂ with
    | none => rfl
    | some b =>
      cases (F₃ mF cF τ₁ mJ cJ τ₂ m3 c3).tr τ₃ with
      | none => rfl
      | some c => rfl

theorem CarryS.tr_file (F₁ : CarryS G.s₁ s₁') (F₂ : CarryS G.s₂ s₂') (F₃ : CarryS G.s₃ s₃')
    (mF : G.rF.Msg) (cF : G.rF.Chal) (τ₁ : Tr G.s₁) (mJ : G.rJ.Msg) (cJ : G.rJ.Chal) (τ₂ : Tr G.s₂)
    (m3 : G.r3.Msg) (c3 : G.r3.Chal) (τ₃ : Tr G.s₃) :
    (CarryS.file G F₁ F₂ F₃).tr
        ((mF, cF, Tr.app τ₁ ((mJ, cJ, Tr.app τ₂ ((m3, c3, τ₃) : Tr G.sh₃)) : Tr G.shJ)) : Tr G.sh) =
      (F₁.tr τ₁).bind fun a => (F₂.tr τ₂).bind fun b => (F₃.tr τ₃).map fun c =>
        Tr.app a (Tr.app b c) :=
  CarryS.tr_fileD _ _ _ mF cF τ₁ mJ cJ τ₂ m3 c3 τ₃

/-- The written counts bear the typed ones. -/
theorem CarryS.fits_fileD {F₁ : G.rF.Msg → G.rF.Chal → CarryS G.s₁ s₁'}
    {F₂ : G.rF.Msg → G.rF.Chal → Tr G.s₁ → G.rJ.Msg → G.rJ.Chal → CarryS G.s₂ s₂'}
    {F₃ : G.rF.Msg → G.rF.Chal → Tr G.s₁ → G.rJ.Msg → G.rJ.Chal → Tr G.s₂ → G.r3.Msg →
      G.r3.Chal → CarryS G.s₃ s₃'}
    {δ₁ : Err s₁'} {δ₂ : Err s₂'} {δ₃ : Err s₃'} {ε₁ : Err G.s₁} {ε₂ : Err G.s₂} {ε₃ : Err G.s₃}
    (h₁ : ∀ mF cF, (F₁ mF cF).Fits δ₁ ε₁)
    (h₂ : ∀ mF cF τ₁ mJ cJ, (F₂ mF cF τ₁ mJ cJ).Fits δ₂ ε₂)
    (h₃ : ∀ mF cF τ₁ mJ cJ τ₂ m3 c3, (F₃ mF cF τ₁ mJ cJ τ₂ m3 c3).Fits δ₃ ε₃) :
    (CarryS.fileD G F₁ F₂ F₃).Fits (Err.app δ₁ (Err.app δ₂ δ₃)) (errFile G ε₁ ε₂ ε₃) :=
  fun mF cF => CarryS.Fits.app (h₁ mF cF) fun τ₁ => fun mJ cJ =>
    CarryS.Fits.app (h₂ mF cF τ₁ mJ cJ) fun τ₂ => fun m3 c3 => h₃ mF cF τ₁ mJ cJ τ₂ m3 c3

theorem CarryS.fits_file {F₁ : CarryS G.s₁ s₁'} {F₂ : CarryS G.s₂ s₂'} {F₃ : CarryS G.s₃ s₃'}
    {δ₁ : Err s₁'} {δ₂ : Err s₂'} {δ₃ : Err s₃'} {ε₁ : Err G.s₁} {ε₂ : Err G.s₂} {ε₃ : Err G.s₃}
    (h₁ : F₁.Fits δ₁ ε₁) (h₂ : F₂.Fits δ₂ ε₂) (h₃ : F₃.Fits δ₃ ε₃) :
    (CarryS.file G F₁ F₂ F₃).Fits (Err.app δ₁ (Err.app δ₂ δ₃)) (errFile G ε₁ ε₂ ε₃) :=
  CarryS.fits_fileD (fun _ _ => h₁) (fun _ _ _ _ _ => h₂) fun _ _ _ _ _ _ _ _ => h₃

/-- Each entry of the whole is a share of at most εs, if each chain's is. -/
theorem below_file {ε₁ : Err G.s₁} {ε₂ : Err G.s₂} {ε₃ : Err G.s₃} {εs : ℝ≥0∞}
    (h₁ : Err.Below ε₁ εs) (h₂ : Err.Below ε₂ εs) (h₃ : Err.Below ε₃ εs) :
    Err.Below (errFile G ε₁ ε₂ ε₃) εs :=
  ⟨by rw [Nat.cast_zero]; exact zero_le _,
    Err.Below.app h₁ (s := G.s₁) (t := G.shJ) ⟨by rw [Nat.cast_zero]; exact zero_le _,
      Err.Below.app h₂ (s := G.s₂) (t := G.sh₃) ⟨by rw [Nat.cast_zero]; exact zero_le _, h₃⟩⟩⟩

end OnBytes.Flat
