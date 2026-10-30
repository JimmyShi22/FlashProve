-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendBelow.lean: THEOREMS. **The errors of the piece of a sending (sendPiece at e := errPort P rad), as shares of the WRITTEN challenges, are at most 2 ^ -128, by two Booleans that have code.**
  dsOf_seedRound   the draws of the round of seeds at one seed
  nVals_seed       the number of its typed values
  card_seeds       the number of the place's joint seeds at one seed: the same number
  blocksOf         the hash blocks that the round of seeds draws from
  belowB           THE SECOND TEST: the sampler's bias over these blocks, times 2 ^ -K, divided by two to the place's bits of work, is at most 2 ^ -128: one comparison of natural numbers
  below_send       **at one seed (P.seeds = 1) and a first written round that is the round of seeds (SeedRound P d₁): shareB K P rad = true → belowB K P = true → Err.Below ((seedMaps d₁ d₂ P.coordinates).err (errPort P rad, ())) (2⁻¹ ^ 128)**:
                   by the library's Maps.below_err, share_le and rate_pow
What is not claimed. That the two tests say yes anywhere: a matter of evaluation. Nothing on soundness.

-/
import Johnson.RunOne.KeySendErr
import OnBytes.Slice.RatesNum
import OnBytes.Flat.CarrySMaps

set_option autoImplicit false

namespace Johnson.RunOne.KeySendErr

open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat Johnson.Pack Cb Cb.Ood Prob Iop Run
open Johnson.RunOne.KeySendGood
open VerifiableInference.Desc.K1 (Par Seeds errPort seedEntry seedMaps seedMaps_ok)
open scoped ENNReal

theorem dsOf_seedRound (P : Par) (h1 : P.seeds = 1) (d : RDT) (h : SeedRound P d) :
    Fmt.dsOf d.entry d.kind = List.replicate P.coordinates Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0] := by
  refine dsOf_one_seed d.entry d.kind P.coordinates ?_ ?_ ?_ ?_ h.kind
  · rw [h.entry]; rfl
  · rw [h.entry]; rfl
  · rw [h.entry]; show P.seeds * (P.coordinates + 1) = _; rw [h1, Nat.one_mul]
  · rw [h.entry]; exact h1

theorem nVals_seed : ∀ c : Nat, nVals (List.replicate c Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0]) = qE ^ c * (qE - 1)
  | 0 => by
      show (qE - 1) * (4 ^ 0 * 1) = qE ^ 0 * (qE - 1)
      simp
  | c + 1 => by
      show qE * nVals (List.replicate c Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0]) = qE ^ (c + 1) * (qE - 1)
      rw [nVals_seed c, pow_succ, ← mul_assoc, mul_comm qE (qE ^ c)]

theorem card_seeds (P : Par) (h1 : P.seeds = 1) : Fintype.card (Seeds P) = qE ^ P.coordinates * (qE - 1) := by
  have gen : ∀ n : Nat, n = 1 → Fintype.card (Fin n → (Fin P.coordinates → GE) × GEˣ) = qE ^ P.coordinates * (qE - 1) := by
    intro n h
    subst h
    exact own_card P.coordinates
  exact gen P.seeds h1

def blocksOf (P : Par) : Nat := Fmt.blocksFor (Fmt.wordsAtMost (seedEntry P) .seeds)

def belowB (K : Nat) (P : Par) : Bool :=
  decide ((2 ^ 128 + 1) ^ blocksOf P * 1 * 2 ^ 128 ≤ (2 ^ 128) ^ blocksOf P * 2 ^ K * 2 ^ P.work)

theorem blocks_eq (P : Par) (d : RDT) (h : SeedRound P d) (hl : d.entry.logN ≤ 64) : (bsRound .two d.entry d.kind).b = blocksOf P := by
  rw [(Run.planDraws_law .two d.entry d.kind hl).2, h.entry]
  unfold blocksOf Fmt.wordsAtMost
  rw [if_neg h.kind, if_neg (by decide)]

/-- **The written counts of a sending's piece are shares of at most 2 ^ -128.** -/
theorem below_send (K : Nat) (P : Par) (rad : Nat → Nat) (h1 : P.seeds = 1) (d₁ d₂ : RDT) (hd : SeedRound P d₁) (hs : shareB K P rad = true) (hb : belowB K P = true) :
    Err.Below ((seedMaps d₁ d₂ P.coordinates).err ((errPort P rad, ()) : Nat × Unit)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨hp, hE, hP, hz, hl⟩ := five_of_seedRound P h1 d₁ hd
  refine Maps.below_err _ (seedMaps_ok d₂ hp hE hP hz hl) _ ⟨⟨((1 : ℕ) : ℝ≥0∞) / ((2 ^ K : ℕ) : ℝ≥0∞), ?_, ?_⟩, trivial⟩
  · refine share_le _ 1 (2 ^ K) _ (by positivity) ?_
    rw [one_mul, card_vals_all, dsOf_seedRound P h1 d₁ hd, nVals_seed, ← card_seeds P h1]
    exact errPort_share K P rad hs
  · rw [blocks_eq P d₁ hd hl, hd.entry]
    exact rate_pow (blocksOf P) 1 (2 ^ K) P.work 128 (by positivity) (of_decide_eq_true hb)

end Johnson.RunOne.KeySendErr

#print axioms Johnson.RunOne.KeySendErr.nVals_seed
#print axioms Johnson.RunOne.KeySendErr.card_seeds
#print axioms Johnson.RunOne.KeySendErr.blocks_eq
#print axioms Johnson.RunOne.KeySendErr.below_send
