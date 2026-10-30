-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecChain.lean: the rounds after the batching at the small files of the setting
"record with work", as a chain of three stages with the error counts of the Johnson letters.

OnBytes/Slice/ManyDefs.lean defines a chain of any number of stages;
OnBytes/Slice/ManyAtLetters.lean has three makers of chains with the standard readings and the error
counts of four letters. This file writes out the chain of this setting: two steps, each a fold and a
code switch, and the base case, at the stages `srSg1` to `srSg3` and the rounds `srRd 6` to
`srRd 23` (OnBytes/Slice/SmallRecSz.lean), at the radii 65,304, 10,490 and 10,490, and at the
letters of OnBytes/Slice/ManyHoldsJoh.lean: the Johnson bound's list (`Sg.lstJ`), and the integer
parts of `bchksBound` for the main rows (`Sg.flC`) and for both tables of mask rows (`Sg.flZ`).

Main definitions.
 `srChain3`, `srChain2`   the base case; the chain from the second stage on.
 `srChain`    the chain, with the first stage spelled as the stage of the link's group.
Main theorems.
 `sr_chain_rds`    the batching's round and the chain's rounds are the description's 19 rounds after
                   the fifth. `sr_ds_chain`: all 24 rounds.
 `sr_chain_len`, `sr_chain_rad`   the chain has two code switches; the three stages' radii.
 `sr_chain_plain`  its error counts are those of the letters (`Chain.PlainAt`).
 `sr_chain_joh`    its stages, radii and rounds meet `Chain.JohAt`.
 `sr_chain_holds`  UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a hypothesis, which
   this file does not prove): each of its five blocks is taken off.

Not claimed. THIS IS NO PROOF OF SOUNDNESS. Nothing on the sizes of the error counts: `bchksBound`
is evaluated nowhere here, and with large counts `sr_chain_holds` is true for free. Nothing on the
link's five rounds or the batching. Nothing on a decision, a program or a file: that the program
reads the trees as the standard readings do is not shown here (OnBytes/Slice/SmallRecBlkPub.lean:
`sr_chain_pub`; SmallRecYes.lean).

-/
import OnBytes.Slice.SmallRecCodes

set_option autoImplicit false

namespace OnBytes.Slice
open Cb _root_.Run

/-- The base case, at the radius 10,490. -/
noncomputable def srChain3 : Chain srSg3 :=
  .lastAt Sg.lstJ Sg.flC Sg.flZ srSg3 10490 (srRd 22) (srRd 23)

/-- The chain from the second stage on: the second stage's fold at the radius 10,490, the switch to
the last stage, the base case. -/
noncomputable def srChain2 : Chain srSg2 :=
  .stepEndAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ srSg2 srSg3 sr_fit23 10490 (srRd 15) (srRd 16) (srRd 20)
    (srRd 21) srChain3

/-- **The chain of the small files of the setting "record with work"**, from the stage of the
link's group on, at the radius 65,304. -/
noncomputable def srChain (eM e0 e1 eU : ℕ) : Chain ((srSz eM e0 e1 eU).sg 97) :=
  .stepMidAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ _ srSg2 (sr_fit12g eM e0 e1 eU) 65304 (srRd 6) (srRd 7)
    (srRd 13) (srRd 14) srChain2

/-- The batching's round and the chain's rounds are the description's 19 rounds after the fifth. -/
theorem sr_chain_rds (eM e0 e1 eU : ℕ) :
    srRd 5 :: (srChain eM e0 e1 eU).rds = srD.ds.drop 5 := by
  have haR : srPar.aR = 5 := by decide +kernel
  rw [sr_tail]
  show srRd 5 :: ((srRd 6 :: List.replicate (0 + (srPar.aR + 1)) (srRd 7)) ++ _) = _
  rw [haR]
  rfl

/-- The description's 24 rounds: the link's five, the batching's, the chain's. -/
theorem sr_ds_chain (eM e0 e1 eU : ℕ) : srD.ds =
    srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: (srChain eM e0 e1 eU).rds := by
  rw [sr_chain_rds]
  exact sr_ds_eq

/-- The chain has two code switches. -/
theorem sr_chain_len (eM e0 e1 eU : ℕ) : (srChain eM e0 e1 eU).len = 2 := rfl

/-- The three stages' radii: 65,304, 10,490 and 10,490. -/
theorem sr_chain_rad (eM e0 e1 eU : ℕ) : (srChain eM e0 e1 eU).rad = 65304 ∧
    srChain2.rad = 10490 ∧ srChain3.rad = 10490 := ⟨rfl, rfl, rfl⟩

/-- The chain's error counts are those of the letters. -/
theorem sr_chain_plain (eM e0 e1 eU : ℕ) :
    (srChain eM e0 e1 eU).PlainAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ :=
  Chain.plainAt_stepMidAt _ _ _ _ _ _ _ _ _ _ _ _ _ <|
  Chain.plainAt_stepEndAt _ _ _ _ _ _ _ _ _ _ _ _ _ <|
  Chain.plainAt_lastAt _ _ _ _ _ _ _ _

/-- The chain's stages, radii and rounds are as `Chain.JohAt` asks. -/
theorem sr_chain_joh (eM e0 e1 eU : ℕ) : (srChain eM e0 e1 eU).JohAt :=
  ⟨sr_sg_J eM e0 e1 eU, sr_fold1, sr_rounds12g eM e0 e1 eU, srSg2_J, sr_fold2, sr_rounds23,
    srSg3_J, ⟨_, _, sr_lambda⟩, ⟨_, sr_rB⟩⟩

/-- **Under `Cb.BCHKS46At` each block of the chain is taken off**, at radii beyond half the stages'
distances (`sr_beyond`). -/
theorem sr_chain_holds (hA : BCHKS46At GF GE) (eM e0 e1 eU : ℕ) : (srChain eM e0 e1 eU).Holds :=
  Chain.holds_joh hA _ (sr_chain_plain eM e0 e1 eU) (sr_chain_joh eM e0 e1 eU)

end OnBytes.Slice
