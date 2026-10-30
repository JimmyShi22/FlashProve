-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecBlkPub.lean: the public facts that the statement "the program's yes gives the
yes in the field" asks of a chain, its rounds, its trees and the link's group, at the small files of
the setting "record with work".

OnBytes/Slice/ManyBlk.lean follows a run of the program's stages along a chain of any number of
stages, and OnBytes/Slice/ManyView.lean says what the view of the written link shows. They ask
public facts on codes, sizes, rounds and trees.
This file's text was made by a program.
The chain is `srChain` (OnBytes/Slice/SmallRecChain.lean), the
program's stages are `srSt1` to `srSt3` (OnBytes/Slice/SmallRecBlkSizes.lean), the codes those of
the typed parameter bytes (`Params.smallRecordRead`). The tables' radii play no part: they are
parameters.

Main theorems.
 `sr_stepPub12` and its like, `sr_stepPub12g`   the two steps (`StepPub`).
 `sr_stepOwn2` and its like, `sr_lastOwn3`   the two trees that the code switches send.
 `sr_lastPub3`      the base case.
 `sr_chain2_pub`, `sr_chain_pub`   `Chain.Pub` of the chain from the second stage on, and of the
                    whole chain and the program's three stages.
 `sr_headTrees`, `sr_chain_trees`, `sr_chain_few`   which rounds send a tree; the trees' keys lie
                    below 2 ^ 16.
 `sr_groupFacts_par`   the link's group: what the reading of its columns asks.
Not claimed. Nothing on a key, a record or its rows. That the link's steps keep what the joint
before the first fold asks. Nothing for other parameter bytes. Nothing on soundness.

-/
import OnBytes.Slice.BlkLinkSeat
import OnBytes.Slice.ManyBlk
import OnBytes.Slice.ManyView
import OnBytes.Slice.SmallRecBlkSizes
import OnBytes.Slice.SmallRecChain

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (smallRecordRead)

/-! ## The steps -/

/-- The first fold and the first code switch. -/
theorem sr_stepPub12 :
    StepPub smallRecordRead.codes srSg1 srSg2 srSt1 srSt2 srSg1.Z.l (srRd 13)
      (srRd 14) :=
  ⟨sr_stageCodes1, rfl, sr_mask.1, sr_base.2.1, sr_mask.2.1, sr_small.1.1, sr_rounds12, sr_bits2⟩

/-- The same, with the first stage as the stage of the link's group. -/
theorem sr_stepPub12g (eM e0 e1 eU : ℕ) :
    StepPub smallRecordRead.codes ((srSz eM e0 e1 eU).sg 97) srSg2 srSt1 srSt2
      ((srSz eM e0 e1 eU).sg 97).Z.l (srRd 13) (srRd 14) := by
  rw [sr_sg]
  exact sr_stepPub12

/-- The second fold and the second code switch. -/
theorem sr_stepPub23 :
    StepPub smallRecordRead.codes srSg2 srSg3 srSt2 srSt3 srSg2.Z.l (srRd 20)
      (srRd 21) :=
  ⟨sr_stageCodes2, rfl, sr_mask.2.1, sr_base.2.2, sr_mask.2.2, sr_small.2.1.1, sr_rounds23,
    sr_bits3⟩

/-! ## The trees that the code switches send -/

/-- The second stage's tree. -/
theorem sr_stepOwn2 : StepOwn smallRecordRead.codes srSg2 srSt2 (srRd 13) :=
  ⟨by decide, sr_widths.2.1, sr_oneTree2⟩

/-- The third stage's tree. -/
theorem sr_lastOwn3 : LastOwn smallRecordRead.codes srSg3 srSt3 (srRd 20) where
  h0 := rfl
  g0 := rfl
  w := sr_widths.2.2
  n := sr_pos20
  lay := by
    intro lay h
    have h6 : layTrees smallRecordRead.codes srSent3 = some lay := h
    rw [sr_layTrees3] at h6
    obtain rfl := Option.some.inj h6
    exact ⟨_, rfl, rfl, by decide, rfl, rfl⟩

/-! ## The base case -/

/-- The base case, with the standard readings. -/
theorem sr_lastPub3 : LastPub smallRecordRead.codes srSg3 srSt3 (srRd 22) (srRd 23)
    (fun m => lst (sentW (srRd 22) m) 0) (fun m => shownW srSg3 (sentW (srRd 23) m)) :=
  ⟨sr_stageCodes3, by decide, by decide, ⟨_, sr_rB⟩, fun _ => rfl, fun _ => rfl⟩

/-! ## Along the chain -/

/-- The public facts on the chain from the second stage on and the program's later stages. -/
theorem sr_chain2_pub :
    srChain2.Pub smallRecordRead.codes srSt2 [srSt3] :=
  ⟨srSt3, _, rfl, sr_stepPub23, sr_lastOwn3, fun _ => ⟨rfl, rfl⟩,
    rfl, sr_lastPub3⟩

/-- **The public facts on the whole chain** and the program's three stages, with the first stage
spelled as the stage of the link's group. -/
theorem sr_chain_pub (eM e0 e1 eU : ℕ) :
    (srChain eM e0 e1 eU).Pub smallRecordRead.codes srSt1 srRest :=
  ⟨srSt2, _, rfl, sr_stepPub12g eM e0 e1 eU, sr_stepOwn2, fun _ => ⟨rfl, rfl⟩, sr_chain2_pub⟩

/-! ## Which rounds send a tree -/

/-- Of the link's five rounds and the batching's round, the second alone sends a tree. -/
theorem sr_headTrees : HeadTrees (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5) :=
  ⟨sr_tree_none 0 (by decide), sr_tree_some.1, sr_tree_none 2 (by decide),
    sr_tree_none 3 (by decide), sr_tree_none 4 (by decide), sr_tree_none 5 (by decide)⟩

/-- The first round of each code switch sends a tree, and no other round of a fold or a code switch
does. -/
theorem sr_chain_trees (eM e0 e1 eU : ℕ) : (srChain eM e0 e1 eU).Trees :=
  ⟨sr_tree_none 6 (by decide), sr_tree_none 7 (by decide),
    sr_tree_some.2.1, sr_tree_none 14 (by decide),
    sr_tree_none 15 (by decide), sr_tree_none 16 (by decide),
    sr_tree_some.2.2, sr_tree_none 21 (by decide),
    trivial⟩

/-- The keys of the group's tree and of the code switches' trees lie below 2 ^ 16. -/
theorem sr_chain_few (eM e0 e1 eU : ℕ) : 1 + (srChain eM e0 e1 eU).len ≤ 2 ^ 16 := by
  show 1 + 2 ≤ 2 ^ 16
  norm_num

/-! ## The link's group -/

/-- The link's group: the public facts that the reading of its columns asks for, at the record of
sizes. -/
theorem sr_groupFacts_par :
    PQ.colW (srRd 1).tree = Fmt.M2.widthOf srPar.mems 1 ∧
    srPar.mems = [srPar.mem, srPar.mem] ∧
    srPar.mem.overE = true ∧ srPar.mem.masks = 0 ∧
    (Fmt.M2.starts [srPar.mem, srPar.mem]).1 =
      [some 0, some (2 ^ ceilLog2 smallRecordRead.link.rows)] ∧
    srPar.mem.rows ≤ 2 ^ ceilLog2 smallRecordRead.link.rows ∧
    2 ^ ceilLog2 smallRecordRead.link.rows + srPar.mem.rows ≤
      2 ^ Fmt.M2.kOf [srPar.mem, srPar.mem] ∧
    (rowShape smallRecordRead.link).mainRows = srPar.mem.rows ∧
    (rowShape smallRecordRead.link).mainDeg = 3 ∧ (rowShape smallRecordRead.link).maskRows = 0 ∧
    (maskShape smallRecordRead.link).mainRows = 0 ∧
    0 < (maskShape smallRecordRead.link).maskRows := by
  refine ⟨sr_width1, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OnBytes.Slice
