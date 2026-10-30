-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecBlkPub.lean: the public facts that the statement "the program's yes gives the
yes in the field" asks of a chain, its rounds, its trees and the link's group, at the full-size
files of the setting "record with work".

OnBytes/Slice/ManyBlk.lean follows a run of the program's stages along a chain of any number of
stages, and OnBytes/Slice/ManyView.lean says what the view of the written link shows. They ask
public facts on codes, sizes, rounds and trees.
This file's text was made by a program.
The chain is `frChain` (OnBytes/Slice/FullRecChain.lean), the
program's stages are `frSt1` to `frSt5` (OnBytes/Slice/FullRecBlkSizes.lean), the codes those of the
typed parameter bytes (`Params.recordRead`). The tables' radii play no part: they are parameters.

Main theorems.
 `fr_stepPub12` and its like, `fr_stepPub12g`   the four steps (`StepPub`).
 `fr_stepOwn2` and its like, `fr_lastOwn5`   the four trees that the code switches send.
 `fr_lastPub5`      the base case.
 `fr_chain2_pub`, `fr_chain_pub`   `Chain.Pub` of the chain from the second stage on, and of the
                    whole chain and the program's five stages.
 `fr_headTrees`, `fr_chain_trees`, `fr_chain_few`   which rounds send a tree; the trees' keys lie
                    below 2 ^ 16.
 `fr_groupFacts_par`   the link's group: what the reading of its columns asks.
Not claimed. Nothing on a key, a record or its rows. That the link's steps keep what the joint
before the first fold asks. Nothing for other parameter bytes. Nothing on soundness.

-/
import OnBytes.Slice.BlkLinkSeat
import OnBytes.Slice.ManyBlk
import OnBytes.Slice.ManyView
import OnBytes.Slice.FullRecBlkSizes
import OnBytes.Slice.FullRecChain

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (recordRead)

/-! ## The steps -/

/-- The first fold and the first code switch. -/
theorem fr_stepPub12 :
    StepPub recordRead.codes frSg1 frSg2 frSt1 frSt2 frSg1.Z.l (frRd 15)
      (frRd 16) :=
  ⟨fr_stageCodes1, rfl, fr_mask.1, fr_base.2.1, fr_mask.2.1, fr_small.1.1, fr_rounds12, fr_bits2⟩

/-- The same, with the first stage as the stage of the link's group. -/
theorem fr_stepPub12g (eM e0 e1 eU : ℕ) :
    StepPub recordRead.codes ((frSz eM e0 e1 eU).sg 97) frSg2 frSt1 frSt2
      ((frSz eM e0 e1 eU).sg 97).Z.l (frRd 15) (frRd 16) := by
  rw [fr_sg]
  exact fr_stepPub12

/-- The second fold and the second code switch. -/
theorem fr_stepPub23 :
    StepPub recordRead.codes frSg2 frSg3 frSt2 frSt3 frSg2.Z.l (frRd 23)
      (frRd 24) :=
  ⟨fr_stageCodes2, rfl, fr_mask.2.1, fr_base.2.2.1, fr_mask.2.2.1, fr_small.2.1.1, fr_rounds23,
    fr_bits3⟩

/-- The third fold and the third code switch. -/
theorem fr_stepPub34 :
    StepPub recordRead.codes frSg3 frSg4 frSt3 frSt4 frSg3.Z.l (frRd 30)
      (frRd 31) :=
  ⟨fr_stageCodes3, rfl, fr_mask.2.2.1, fr_base.2.2.2.1, fr_mask.2.2.2.1, fr_small.2.2.1.1,
    fr_rounds34, fr_bits4⟩

/-- The fourth fold and the fourth code switch. -/
theorem fr_stepPub45 :
    StepPub recordRead.codes frSg4 frSg5 frSt4 frSt5 frSg4.Z.l (frRd 37)
      (frRd 38) :=
  ⟨fr_stageCodes4, rfl, fr_mask.2.2.2.1, fr_base.2.2.2.2, fr_mask.2.2.2.2, fr_small.2.2.2.1.1,
    fr_rounds45, fr_bits5⟩

/-! ## The trees that the code switches send -/

/-- The second stage's tree. -/
theorem fr_stepOwn2 : StepOwn recordRead.codes frSg2 frSt2 (frRd 15) :=
  ⟨by decide, fr_widths.2.1, fr_oneTree2⟩

/-- The third stage's tree. -/
theorem fr_stepOwn3 : StepOwn recordRead.codes frSg3 frSt3 (frRd 23) :=
  ⟨by decide, fr_widths.2.2.1, fr_oneTree3⟩

/-- The fourth stage's tree. -/
theorem fr_stepOwn4 : StepOwn recordRead.codes frSg4 frSt4 (frRd 30) :=
  ⟨by decide, fr_widths.2.2.2.1, fr_oneTree4⟩

/-- The fifth stage's tree. -/
theorem fr_lastOwn5 : LastOwn recordRead.codes frSg5 frSt5 (frRd 37) where
  h0 := rfl
  g0 := rfl
  w := fr_widths.2.2.2.2
  n := fr_pos37
  lay := by
    intro lay h
    have h6 : layTrees recordRead.codes frSent5 = some lay := h
    rw [fr_layTrees5] at h6
    obtain rfl := Option.some.inj h6
    exact ⟨_, rfl, rfl, by decide, rfl, rfl⟩

/-! ## The base case -/

/-- The base case, with the standard readings. -/
theorem fr_lastPub5 : LastPub recordRead.codes frSg5 frSt5 (frRd 39) (frRd 40)
    (fun m => lst (sentW (frRd 39) m) 0) (fun m => shownW frSg5 (sentW (frRd 40) m)) :=
  ⟨fr_stageCodes5, by decide, by decide, ⟨_, fr_rB⟩, fun _ => rfl, fun _ => rfl⟩

/-! ## Along the chain -/

/-- The public facts on the chain from the second stage on and the program's later stages. -/
theorem fr_chain2_pub :
    frChain2.Pub recordRead.codes frSt2 [frSt3, frSt4, frSt5] :=
  ⟨frSt3, _, rfl, fr_stepPub23, fr_stepOwn3, fun _ => ⟨rfl, rfl⟩,
    frSt4, _, rfl, fr_stepPub34, fr_stepOwn4, fun _ => ⟨rfl, rfl⟩,
    frSt5, _, rfl, fr_stepPub45, fr_lastOwn5, fun _ => ⟨rfl, rfl⟩,
    rfl, fr_lastPub5⟩

/-- **The public facts on the whole chain** and the program's five stages, with the first stage
spelled as the stage of the link's group. -/
theorem fr_chain_pub (eM e0 e1 eU : ℕ) :
    (frChain eM e0 e1 eU).Pub recordRead.codes frSt1 frRest :=
  ⟨frSt2, _, rfl, fr_stepPub12g eM e0 e1 eU, fr_stepOwn2, fun _ => ⟨rfl, rfl⟩, fr_chain2_pub⟩

/-! ## Which rounds send a tree -/

/-- Of the link's five rounds and the batching's round, the second alone sends a tree. -/
theorem fr_headTrees : HeadTrees (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5) :=
  ⟨fr_tree_none 0 (by decide), fr_tree_some 1 (by decide), fr_tree_none 2 (by decide),
    fr_tree_none 3 (by decide), fr_tree_none 4 (by decide), fr_tree_none 5 (by decide)⟩

/-- The first round of each code switch sends a tree, and no other round of a fold or a code switch
does. -/
theorem fr_chain_trees (eM e0 e1 eU : ℕ) : (frChain eM e0 e1 eU).Trees :=
  ⟨fr_tree_none 6 (by decide), fr_tree_none 7 (by decide),
    fr_tree_some 15 (by decide), fr_tree_none 16 (by decide),
    fr_tree_none 17 (by decide), fr_tree_none 18 (by decide),
    fr_tree_some 23 (by decide), fr_tree_none 24 (by decide),
    fr_tree_none 25 (by decide), fr_tree_none 26 (by decide),
    fr_tree_some 30 (by decide), fr_tree_none 31 (by decide),
    fr_tree_none 32 (by decide), fr_tree_none 33 (by decide),
    fr_tree_some 37 (by decide), fr_tree_none 38 (by decide),
    trivial⟩

/-- The keys of the group's tree and of the code switches' trees lie below 2 ^ 16. -/
theorem fr_chain_few (eM e0 e1 eU : ℕ) : 1 + (frChain eM e0 e1 eU).len ≤ 2 ^ 16 := by
  show 1 + 4 ≤ 2 ^ 16
  norm_num

/-! ## The link's group -/

/-- The link's group: the public facts that the reading of its columns asks for, at the record of
sizes. -/
theorem fr_groupFacts_par :
    PQ.colW (frRd 1).tree = Fmt.M2.widthOf frPar.mems 1 ∧
    frPar.mems = [frPar.mem, frPar.mem] ∧
    frPar.mem.overE = true ∧ frPar.mem.masks = 0 ∧
    (Fmt.M2.starts [frPar.mem, frPar.mem]).1 =
      [some 0, some (2 ^ ceilLog2 recordRead.link.rows)] ∧
    frPar.mem.rows ≤ 2 ^ ceilLog2 recordRead.link.rows ∧
    2 ^ ceilLog2 recordRead.link.rows + frPar.mem.rows ≤
      2 ^ Fmt.M2.kOf [frPar.mem, frPar.mem] ∧
    (rowShape recordRead.link).mainRows = frPar.mem.rows ∧
    (rowShape recordRead.link).mainDeg = 3 ∧ (rowShape recordRead.link).maskRows = 0 ∧
    (maskShape recordRead.link).mainRows = 0 ∧
    0 < (maskShape recordRead.link).maskRows := by
  refine ⟨fr_width1, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OnBytes.Slice
