-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedSig.lean: FOUR STATEMENTS THAT ARE OWED, EACH WRITTEN AS A DEFINITION OF
A Prop: no proof stands here. They are what kind K13's block (M:3) and W's commitment (M:4) still
owe at the table of joints for the letters "held", "shown", "no collision" and "pin" as other
files have filled them (`meaningSig`, Johnson/Desc/Sound/BordersFill.lean, over
Johnson/Desc/Sound/MeaningSig.lean), and for a public test of another layer that rides past the
two.
  `OwedSeed3`: over a step of kind K13's block the sample that the record holds of ANY tenant is
    the same (`smpSeed`, Johnson/Desc/SmpRows.lean: it reads the book's places, the code table,
    and of the tenant's message whether it is sampled, its shape and its sample rows).
  `OwedSeed4`: over a step of W's commitment the sample of a tenant WHOSE SAMPLE IS HELD IN FRONT is
    the same, where the book has a place for every message.
  `OwedPinsStay`: KIND-FREE: two records at which the members at a seat have one sample, and two
    strings with one column at the seat's tree, have one "shown", one "no collision" and one "pin"
    at that seat.
  `OwedKeeps wB`: a test wB on the record rides over both steps.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Sending Mem SitsAt pinJT noCollJT shownJT)

/-- **OWED.** Kind K13's block leaves every tenant's sample. -/
def OwedSeed3 : Prop :=
  ∀ {Pp Cl : Type} (P : Where) (x x' : Pp × S) (j t : ℕ), StepM3 Cl P x x' →
    smpSeed x'.2.st x'.2.book j t = smpSeed x.2.st x.2.book j t

/-- **OWED.** W's commitment leaves the sample of a tenant whose sample is held in front. -/
def OwedSeed4 : Prop :=
  ∀ {Pp Cl : Type} (P : Where) (P' : K1.Par) (x x' : Pp × S) (j t : ℕ), StepM4 Cl P P' x x' →
    x.2.book.place.size = x.2.st.oracles.size → smpHeld x.2.st x.2.book j t = true →
    smpSeed x'.2.st x'.2.book j t = smpSeed x.2.st x.2.book j t

/-- **OWED.** Kind-free: one sample at the seat's members, one column at the seat's tree: one
"shown", one "no collision", one "pin". -/
def OwedPinsStay : Prop :=
  ∀ {A Xi Cells Tok : Type} (cs : Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (a a' : A) (y y' : Strs), (∀ z, y'.col j z = y.col j z) →
    (∀ m ∈ ms, SitsAt m j t → smp a' m.1 m.2 = smp a m.1 m.2) →
    (shownJT cs G ms j t y ↔ shownJT cs G ms j t y') ∧
      (noCollJT cs G smp ms j t a y ↔ noCollJT cs G smp ms j t a' y') ∧
      ∀ w : Desc.Wit Cells Tok MsgT,
        pinJT cs G arr smp ms j t a y w ↔ pinJT cs G arr smp ms j t a' y' w

/-- **OWED**, of a test wB on the record: it rides over both steps. -/
def OwedKeeps (wB : S → Bool) : Prop :=
  (∀ {Pp Cl : Type} (P : Where) (x x' : Pp × S), StepM3 Cl P x x' → wB x.2 = true →
      wB x'.2 = true) ∧
    ∀ {Pp Cl : Type} (P : Where) (P' : K1.Par) (x x' : Pp × S), StepM4 Cl P P' x x' →
      wB x.2 = true → wB x'.2 = true

end VerifiableInference.Desc.K13.Law
