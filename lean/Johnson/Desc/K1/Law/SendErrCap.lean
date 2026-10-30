-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SendErrCap.lean: THE WRITTEN ERRORS OF A SENDING's TWO ROUNDS, AT A COUNT e OF
BAD SEEDS, ARE AT MOST THE CAP (Err.cap 128, Iop/ErrCap.lean), WHERE ONE COMPARISON OF NATURAL
NUMBERS HOLDS OF e.

  capB P e k        THE PREMISE ON e, as a test with code: with b the hash blocks of the round of
                    the seeds at the place's own entry, V the number of its seeds and w the place's
                    bits of work: (2^128 + 1)^b e 2^k ≤ (2^128)^b V 2^w. It is powB
                    (Johnson/Desc/K1/Law/PowB.lean) with the count a letter.
  capB_mono         it bears every smaller count · capB_port: powB is capB at eNat.
  sendErr_below     a yes: Err.Below of (seedMaps d₁ d₂ P.coordinates).err (e, ()) at 2^-k.
  sendErr_le_cap    **a yes at 128: these errors are at most the cap.**
  sendErr_le_cap_port   so at e := errPort P rad, from powB P rad 128.
PREMISES BESIDE IT: d₁.entry = seedEntry P · d₁.kind = .seeds · P.seeds = 1 (one seed: the maps'
condition is had by seed_draws, which asks it). AT WHICH PLACES THERE IS ONE SEED IS NOT SAID HERE:
it is a premise, to be had place by place (PaidAt, Johnson/Desc/K1/Law/RoundsLit.lean, bears it).
WORK IS COUNTED: the comparison's right side bears 2 ^ P.work.
What is not claimed. That the test says yes at a place. That e bounds a place's bad seeds. Nothing
on soundness.

-/
import Johnson.Desc.K1.Law.PowB
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open scoped ENNReal

/-- **The premise on the count.** -/
def capB (P : Par) (e k : Nat) : Bool :=
  decide ((2 ^ 128 + 1) ^ (bsRound .two (seedEntry P) .seeds).b * e * 2 ^ k ≤
    (2 ^ 128) ^ (bsRound .two (seedEntry P) .seeds).b * allSeeds qN P.coordinates * 2 ^ P.work)

theorem capB_mono {P : Par} {e e' k : Nat} (h : e' ≤ e) (hb : capB P e k = true) :
    capB P e' k = true := by
  unfold capB at hb ⊢
  rw [decide_eq_true_eq] at hb ⊢
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)) hb

/-- powB is the test at the computed bound on the place's bad seeds. -/
theorem capB_port (P : Par) (rad : Nat → Nat) (k : Nat) : capB P (eNat P rad) k = powB P rad k :=
  rfl

theorem capB_cmp (P : Par) (e k : Nat) (h : capB P e k = true) (d₁ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) :
    (2 ^ 128 + 1) ^ (bsRound .two d₁.entry d₁.kind).b * e * 2 ^ k ≤
      (2 ^ 128) ^ (bsRound .two d₁.entry d₁.kind).b *
        Fintype.card ((Fin P.coordinates → GE) × GEˣ) * 2 ^ d₁.entry.work := by
  have h' := of_decide_eq_true h
  rw [he₁, hk₁, card_seed, card_GE]
  exact h'

/-- A yes gives the written errors at most 2^-k. -/
theorem sendErr_below (P : Par) (h1 : P.seeds = 1) (e k : Nat) (h : capB P e k = true)
    (d₁ d₂ : RDT) (he : d₁.entry = seedEntry P) (hk : d₁.kind = .seeds) :
    Err.Below ((seedMaps d₁ d₂ P.coordinates).err ((e, ()) : Nat × Unit)) ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws P h1 d₁ he hk
  refine Maps.below_pow (seedMaps d₁ d₂ P.coordinates) (seedMaps_ok d₂ a1 a2 a3 a4 a5)
    ((e, ()) : Nat × Unit) ⟨⟨e, Fintype.card ((Fin P.coordinates → GE) × GEˣ),
      seeds_pos P.coordinates, ?_, capB_cmp P e k h d₁ he hk⟩, trivial⟩
  rw [nVals_seed P h1 d₁ he hk]

/-- **A yes at 128: the written errors are at most the cap.** -/
theorem sendErr_le_cap (P : Par) (h1 : P.seeds = 1) (e : Nat) (h : capB P e 128 = true)
    (d₁ d₂ : RDT) (he : d₁.entry = seedEntry P) (hk : d₁.kind = .seeds) :
    Iop.Err.le ((seedMaps d₁ d₂ P.coordinates).err ((e, ()) : Nat × Unit))
      (Iop.Err.cap 128 (uLT (ckP .two) [d₁, d₂])) :=
  Err.le_cap_of_below_inv 128 _ (sendErr_below P h1 e 128 h d₁ d₂ he hk)

/-- So at the bound on the place's bad seeds. -/
theorem sendErr_le_cap_port (P : Par) (h1 : P.seeds = 1) (rad : Nat → Nat)
    (h : powB P rad 128 = true) (d₁ d₂ : RDT) (he : d₁.entry = seedEntry P)
    (hk : d₁.kind = .seeds) :
    Iop.Err.le ((seedMaps d₁ d₂ P.coordinates).err ((errPort P rad, ()) : Nat × Unit))
      (Iop.Err.cap 128 (uLT (ckP .two) [d₁, d₂])) := by
  rw [errPort_eNat P h1]
  exact sendErr_le_cap P h1 _ h d₁ d₂ he hk

-- the test can say no: at a place without work, a count as large as the number of the seeds
example (P : Par) (hw : P.work = 0) : capB P (allSeeds qN P.coordinates + 1) 128 = false := by
  unfold capB
  rw [decide_eq_false_iff_not, hw]
  intro h
  have hb : (2 ^ 128) ^ (bsRound .two (seedEntry P) .seeds).b ≤
      (2 ^ 128 + 1) ^ (bsRound .two (seedEntry P) .seeds).b :=
    Nat.pow_le_pow_left (Nat.le_succ _) _
  have hp : 0 < (2 ^ 128) ^ (bsRound .two (seedEntry P) .seeds).b := pow_pos (by decide) _
  have h2 : (2 ^ 128) ^ (bsRound .two (seedEntry P) .seeds).b *
      (allSeeds qN P.coordinates + 1) ≤
      (2 ^ 128 + 1) ^ (bsRound .two (seedEntry P) .seeds).b *
        (allSeeds qN P.coordinates + 1) * 2 ^ 128 :=
    Nat.le_trans (Nat.mul_le_mul_right _ hb) (Nat.le_mul_of_pos_right _ (by decide))
  have h3 := Nat.le_trans h2 h
  rw [pow_zero, Nat.mul_one] at h3
  exact absurd (Nat.le_of_mul_le_mul_left h3 hp) (by omega)

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.capB_mono
#print axioms VerifiableInference.Desc.K1.sendErr_below
#print axioms VerifiableInference.Desc.K1.sendErr_le_cap
#print axioms VerifiableInference.Desc.K1.sendErr_le_cap_port
