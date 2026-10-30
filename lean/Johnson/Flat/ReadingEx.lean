-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadingEx.lean: the reading's law with the sampler's bias priced by what a round draws.

`Maps.Held` (OnBytes/Flat/CarrySMaps.lean) prices the bias at a factor 1 + 2^-128 for each of the
round's hash blocks. At a bound εs with no room that is too coarse: at a round that draws matrix
entries alone, at a price of just 2^-128 and thousands of blocks, `Held (2^-128)` is false, though
such a round has no bias at all. The finer price is landed one floor below (`below_round_div_ex`,
OnBytes/Slice/RatesEx.lean): three factors for each element of the extension field that the round
draws (`Run.exAll`), none for a position, a matrix entry or a sealing.
  `Maps.HeldEx εs`: `Held` with that power. `Maps.below_err_ex`: then the written counts are shares
  of at most εs. `HeldEx.app`, `heldEx_skips`.
  `Maps.ReadingEx`: what a kind of block owes for the reading of its stretch: maps as asked, every
  round read, `HeldEx`. `ReadingEx.app`.
  `readingLaw_of_ex`, `readingLaw_of_readingsEx`: the same law `ReadingLaw`
  (Johnson/Flat/ReadingLaw.lean) from the finer premises; so all that spends the law
  (`ReadingLaw.sound`, `.feeds`, `.knowsJ`) is served as it lies.

Limits. That `Held` gives `HeldEx` (that the power is at most the number of blocks) is not shown.
All limits of Johnson/Flat/ReadingLaw.lean hold here too: no map is made at any data.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ReadingLinks
import OnBytes.Slice.RatesEx

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Flat
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Maker OnBytes.Slice

namespace Maps

/-- At each step the typed count is a share of at most c of the round's typed values, and c, with
the
sampler's bias BY WHAT THE ROUND DRAWS and the gain from the test bits, is at most εs. -/
def HeldEx (εs : ℝ≥0∞) : {ds : List RDT} → {s' : Shape} → Maps ds s' → Err s' → Prop
  | _, _, .nil, _ => True
  | _, _, .step (d := d) _ rest, (e, ε) =>
      (∃ c : ℝ≥0∞, (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) ∧
        kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work) ≤ εs) ∧
      rest.HeldEx εs ε
  | _, _, .skip _ rest, ε => rest.HeldEx εs ε

/-- Then the written counts are shares of at most εs. -/
theorem below_err_ex {εs : ℝ≥0∞} : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s'), M.OK →
    ∀ ε : Err s', M.HeldEx εs ε → Err.Below (M.err ε) εs
  | _, _, .nil, _, _, _ => trivial
  | _, _, .step (d := d) _ rest, h, (e, ε), hh => by
      obtain ⟨⟨c, h1, h2⟩, h3⟩ := hh
      exact ⟨(below_round_div_ex (toRD d) h.1.log e c h1).trans (mul_le_mul' h2 le_rfl),
        below_err_ex rest h.2 ε h3⟩
  | _, _, .skip _ rest, h, ε, hh =>
      ⟨by rw [Nat.cast_zero]; exact zero_le _, below_err_ex rest h ε hh⟩

theorem HeldEx.app {εs : ℝ≥0∞} : ∀ {ds es : List RDT} {s' t' : Shape} {M : Maps ds s'}
    {N : Maps es t'} {ε : Err s'} {δ : Err t'}, M.HeldEx εs ε → N.HeldEx εs δ →
    (M.app N).HeldEx εs (Err.app ε δ)
  | _, _, _, _, .nil, _, _, _, _, hN => hN
  | _, _, _, _, .step _ rest, _, (_, _), _, hM, hN => ⟨hM.1, HeldEx.app (M := rest) hM.2 hN⟩
  | _, _, _, _, .skip _ rest, _, _, _, hM, hN => HeldEx.app (M := rest) hM hN

theorem heldEx_skips (εs : ℝ≥0∞) : ∀ ds : List RDT, (skips ds).HeldEx εs ()
  | [] => trivial
  | _ :: ds => heldEx_skips εs ds

/-- What a kind owes for the reading of its stretch, at the finer price. -/
structure ReadingEx {ds : List RDT} {s' : Shape} (M : Maps ds s') (δ : Err s') (εs : ℝ≥0∞) :
    Prop where
  ok : M.OK
  reads : M.ReadsAll
  held : M.HeldEx εs δ

theorem ReadingEx.app {ds es : List RDT} {s' t' : Shape} {M : Maps ds s'} {N : Maps es t'}
    {δ : Err s'} {η : Err t'} {εs : ℝ≥0∞} (hM : M.ReadingEx δ εs) (hN : N.ReadingEx η εs) :
    (M.app N).ReadingEx (Err.app δ η) εs :=
  ⟨OK.app hM.ok hN.ok, ReadsAll.app hM.reads hN.reads, HeldEx.app hM.held hN.held⟩

end Maps

section
variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {s₁' s₂' s₃' : Shape}
  {M₁ : Maps D.ds₁ s₁'} {M₂ : Maps D.ds₂ s₂'} {M₃ : Maps D.ds₃ s₃'}
  {δ₁ : Err s₁'} {δ₂ : Err s₂'} {δ₃ : Err s₃'} {εs : ℝ≥0∞} {N : ℕ}

/-- **The reading's law, from the finer premises.** -/
theorem readingLaw_of_ex (ok₁ : M₁.OK) (ok₂ : M₂.OK) (ok₃ : M₃.OK) (held₁ : M₁.HeldEx εs δ₁)
    (held₂ : M₂.HeldEx εs (Err.times N δ₂)) (held₃ : M₃.HeldEx εs δ₃) :
    ReadingLaw D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N where
  image := fun silent run x y τ h => tr_whole_of_out D tF tJ t3 M₁ M₂ M₃ silent run x y τ h
  fits := fits_whole D tF tJ t3 ok₁ ok₂ ok₃ δ₁ δ₂ δ₃
  below := below_file_shared (chainsOf_laws (ckP .two) D tF tJ t3) N (M₁.below_err_ex ok₁ δ₁ held₁)
    (by rw [Maps.times_err]; exact M₂.below_err_ex ok₂ _ held₂) (M₃.below_err_ex ok₃ δ₃ held₃)
  chain₁ := ⟨M₁.fits ok₁ δ₁, M₁.below_err_ex ok₁ δ₁ held₁⟩
  chain₂ := ⟨M₂.fits ok₂ _, M₂.below_err_ex ok₂ _ held₂⟩
  chain₃ := ⟨M₃.fits ok₃ δ₃, M₃.below_err_ex ok₃ δ₃ held₃⟩

/-- The same from the three chains' bundles. -/
theorem readingLaw_of_readingsEx (h₁ : M₁.ReadingEx δ₁ εs) (h₂ : M₂.ReadingEx (Err.times N δ₂) εs)
    (h₃ : M₃.ReadingEx δ₃ εs) : ReadingLaw D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃ εs N :=
  readingLaw_of_ex D tF tJ t3 h₁.ok h₂.ok h₃.ok h₁.held h₂.held h₃.held

end

end OnBytes.Flat

#print axioms OnBytes.Flat.Maps.below_err_ex
#print axioms OnBytes.Flat.Maps.ReadingEx.app
#print axioms OnBytes.Flat.readingLaw_of_ex
#print axioms OnBytes.Flat.readingLaw_of_readingsEx
