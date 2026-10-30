-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecChain.lean: the rounds after the batching at the full-size files of the setting
"record with work", as a chain of five stages with the error counts of the Johnson letters.

The like of OnBytes/Slice/SmallRecChain.lean, whose head describes the makers and the letters, at
the full size; its text was made from that file's by a program that swaps names and numbers and
writes five stages for three. The chain: four steps, each a fold and a code switch, and the base
case, at the stages `frSg1` to `frSg5` and the rounds `frRd 6` to `frRd 40`
(OnBytes/Slice/FullRecSz.lean), at the radii 8,342,420, 1,569,886, 98,104, 6,044 and 13,370, and at
the letters `Sg.lstJ`, `Sg.flC`, `Sg.flZ`, `Sg.flZ` (OnBytes/Slice/ManyHoldsJoh.lean).

Main definitions.
 `frChain5` to `frChain2`   the base case; the chains from the later stages on.
 `frChain`    the chain, with the first stage spelled as the stage of the link's group.
Main theorems.
 `fr_chain_rds`    the batching's round and the chain's rounds are the description's 36 rounds after
                   the fifth. `fr_ds_chain`: all 41 rounds.
 `fr_chain_len`, `fr_chain_rad`   the chain has four code switches; the five stages' radii.
 `fr_chain_plain`  its error counts are those of the letters (`Chain.PlainAt`).
 `fr_chain_joh`    its stages, radii and rounds meet `Chain.JohAt`.
 `fr_chain_holds`  UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a hypothesis, which
   this file does not prove): each of its nine blocks is taken off.

Not claimed. THIS IS NO PROOF OF SOUNDNESS. Nothing on the sizes of the error counts: `bchksBound`
is evaluated nowhere here, and with large counts `fr_chain_holds` is true for free. Nothing on the
link's five rounds or the batching. Nothing on a decision, a program or a file: that the program
reads the trees as the standard readings do is not shown here (OnBytes/Slice/FullRecBlkPub.lean:
`fr_chain_pub`; FullRecYes.lean).

-/
import OnBytes.Slice.FullRecCodes

set_option autoImplicit false

namespace OnBytes.Slice
open Cb _root_.Run

/-- The base case, at the radius 13,370. -/
noncomputable def frChain5 : Chain frSg5 :=
  .lastAt Sg.lstJ Sg.flC Sg.flZ frSg5 13370 (frRd 39) (frRd 40)

/-- The chain from the fourth stage on: that stage's fold at the radius 6,044, the switch to the
last stage, and what follows. -/
noncomputable def frChain4 : Chain frSg4 :=
  .stepEndAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ frSg4 frSg5 fr_fit45 6044 (frRd 32) (frRd 33)
    (frRd 37) (frRd 38) frChain5

/-- The chain from the third stage on: that stage's fold at the radius 98,104, the switch to the
fourth stage, and what follows. -/
noncomputable def frChain3 : Chain frSg3 :=
  .stepMidAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ frSg3 frSg4 fr_fit34 98104 (frRd 25) (frRd 26)
    (frRd 30) (frRd 31) frChain4

/-- The chain from the second stage on: that stage's fold at the radius 1,569,886, the switch to the
third stage, and what follows. -/
noncomputable def frChain2 : Chain frSg2 :=
  .stepMidAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ frSg2 frSg3 fr_fit23 1569886 (frRd 17) (frRd 18)
    (frRd 23) (frRd 24) frChain3

/-- **The chain of the full-size files of the setting "record with work"**, from the stage of the
link's group on, at the radius 8,342,420. -/
noncomputable def frChain (eM e0 e1 eU : ℕ) : Chain ((frSz eM e0 e1 eU).sg 97) :=
  .stepMidAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ _ frSg2 (fr_fit12g eM e0 e1 eU) 8342420 (frRd 6) (frRd 7)
    (frRd 15) (frRd 16) frChain2

/-- The batching's round and the chain's rounds are the description's 36 rounds after the fifth. -/
theorem fr_chain_rds (eM e0 e1 eU : ℕ) :
    frRd 5 :: (frChain eM e0 e1 eU).rds = frD.ds.drop 5 := by
  have haR : frPar.aR = 7 := by decide +kernel
  rw [fr_tail]
  show frRd 5 :: ((frRd 6 :: List.replicate (0 + (frPar.aR + 1)) (frRd 7)) ++ _) = _
  rw [haR]
  rfl

/-- The description's 41 rounds: the link's five, the batching's, the chain's. -/
theorem fr_ds_chain (eM e0 e1 eU : ℕ) : frD.ds =
    frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: (frChain eM e0 e1 eU).rds := by
  rw [fr_chain_rds]
  exact fr_ds_eq

/-- The chain has four code switches. -/
theorem fr_chain_len (eM e0 e1 eU : ℕ) : (frChain eM e0 e1 eU).len = 4 := rfl

/-- The five stages' radii. -/
theorem fr_chain_rad (eM e0 e1 eU : ℕ) : (frChain eM e0 e1 eU).rad = 8342420 ∧
    frChain2.rad = 1569886 ∧ frChain3.rad = 98104 ∧ frChain4.rad = 6044 ∧ frChain5.rad = 13370 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The chain's error counts are those of the letters. -/
theorem fr_chain_plain (eM e0 e1 eU : ℕ) :
    (frChain eM e0 e1 eU).PlainAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ :=
  Chain.plainAt_stepMidAt _ _ _ _ _ _ _ _ _ _ _ _ _ <|
  Chain.plainAt_stepMidAt _ _ _ _ _ _ _ _ _ _ _ _ _ <|
  Chain.plainAt_stepMidAt _ _ _ _ _ _ _ _ _ _ _ _ _ <|
  Chain.plainAt_stepEndAt _ _ _ _ _ _ _ _ _ _ _ _ _ <|
  Chain.plainAt_lastAt _ _ _ _ _ _ _ _

/-- The chain's stages, radii and rounds are as `Chain.JohAt` asks. -/
theorem fr_chain_joh (eM e0 e1 eU : ℕ) : (frChain eM e0 e1 eU).JohAt :=
  ⟨fr_sg_J eM e0 e1 eU, fr_fold1, fr_rounds12g eM e0 e1 eU, frSg2_J, fr_fold2, fr_rounds23, frSg3_J,
    fr_fold3, fr_rounds34, frSg4_J, fr_fold4, fr_rounds45, frSg5_J, ⟨_, _, fr_lambda⟩, ⟨_, fr_rB⟩⟩

/-- **Under `Cb.BCHKS46At` each block of the chain is taken off**, at radii beyond half the stages'
distances (`fr_beyond`). -/
theorem fr_chain_holds (hA : BCHKS46At GF GE) (eM e0 e1 eU : ℕ) : (frChain eM e0 e1 eU).Holds :=
  Chain.holds_joh hA _ (fr_chain_plain eM e0 e1 eU) (fr_chain_joh eM e0 e1 eU)

end OnBytes.Slice
