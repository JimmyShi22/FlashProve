-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPrice.lean: THE SMALLNESS TEST, ITS FIRST HALF: THE ROUND'S LOST SET
AGAINST THE ROUND'S NUMBER OF WRITTEN VERIFIER MESSAGES, AT 128 COMBINATIONS.

`hear_lost` (Johnson/Desc/First/K8/LawLost.lean) bounds the round's lost set by a number e of
written verifier messages: at least the proved block's count times the sampler's own number.
Johnson/Flat/NoRoomSmall.lean shows of a written round that draws matrix entries alone, without
work: at 128 combinations that product is a share of at most 2 ^ -128 of the round's written
verifier messages. Here the kind's declared round is shown to be such a round, and the two are
joined. The round has no work: so the price is the one with the work not counted.
  `entriesOnly`: the kind's declared round draws columns x 128 matrix entries and nothing else,
    without work.
  `hear_price`: the proved block's count, at the kind's round, is a share of at most 2 ^ -128
    (`RoundBelow`, OnBytes/Slice/ManyErr.lean).
  `bad_draw_below`: the same of the typed values whose matrix, BY THE READING THAT THE KIND'S LAW
    USES (`matOf`), leads from messages without cells to digits that meet all clauses
    (`small_round_below`, Johnson/Flat/NoRoomSmallCount.lean).
  `hear_lost_128`: THE TWO JOINED: at the least error that `hear_lost` allows: the round's lost set
    is a share of at most 2 ^ -128 of the round's written verifier messages.
Statements and proofs; nothing is counted anew.
Limits: those of LawLost.lean (the caller and the letters are parameters; no caller is named) and of
the two files named. That a place has 128 combinations is a premise.

-/
import Johnson.Desc.First.K8.LawLost
import Johnson.Flat.NoRoomSmallCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.K8

open Iop Prob Cb.Pv.Tail OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Tail KObj
  VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound VerifiableInference.Number

section
variable {p : Par} {s : Size} (hf : Fits p s) (hτ : p.tau = 128)

include hf hτ in
/-- The kind's declared round draws columns x 128 matrix entries and nothing else, without work. -/
theorem entriesOnly : EntriesOnly (rd p) (s.columns * 128) := by
  have h := onlyTrits hf
  rw [hf.tau, hτ] at h
  exact ⟨h, rfl, Nat.zero_le _⟩

include hf hτ in
/-- **The proved block's count is a share of at most 2 ^ -128 of the round's written verifier
messages.** -/
theorem hear_price :
    RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rw [card_dr_div s (hf.tau.trans hτ)]
  exact no_room_small s.columns (rd p) (entriesOnly hf hτ)

include hτ in
/-- The typed values whose matrix, by the reading of the kind's law, leads from messages without
cells to digits that meet all clauses. -/
theorem bad_draw_below {K : Type} [CommRing K] (Λ : Letters K s) (hs : s.OK) (x : Λ.X) (y : Λ.E.Str)
    (msg : Λ.M) :
    RoundBelow (cnt fun v => BadDraw Λ x y msg (matOf s (rd p) (onlyTrits hf) v)) (rd p)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  small_round_below Λ hs (hf.tau.trans hτ) (entriesOnly hf hτ) _
    (matOf_inj s (rd p) (onlyTrits hf)) x y msg

end

section
variable {S Cl W : Type} {F : Frame} {seat : Seat S} {p : Par} {base : ℕ} {d : TailCallerOn}

/-- The least error that `hear_lost` allows: the proved block's count times the sampler's own
number. -/
def leastErr (p : Par) (d : TailCallerOn) : ℕ :=
  (Fintype.card (Dr d.c.s) / 2 ^ d.c.s.tau) * (Run.bsRound .two (rdt p).entry (rdt p).kind).w

/-- **At 128 combinations the round's lost set is a share of at most 2 ^ -128 of the round's written
verifier messages.** -/
theorem hear_lost_128 (Q : Reads Cl W F seat p base (leastErr p d) d) (hf : Fits p d.c.s)
    (hOK : d.c.s.OK)
    (hτ : p.tau = 128) (a : S × F.E.Str) (ha : Q.onA a)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) :
    ((cnt (fun c : (roundT (Run.ckP .two) (rdt p)).up.Chal => ¬ Q.Fine a m c) : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 128 * (Fintype.card (wRound (rd p)).Chal : ℝ≥0∞) := by
  have h1 := hear_lost Q hf hOK (Nat.le_refl _) a ha m
  have h2 : ((leastErr p d : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 128 * (Fintype.card (wRound (rd p)).Chal : ℝ≥0∞) := hear_price hf hτ
  exact le_trans (by exact_mod_cast h1) h2

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hear_lost_128
#print axioms VerifiableInference.Desc.First.K8.hear_price
#print axioms VerifiableInference.Desc.First.K8.bad_draw_below
