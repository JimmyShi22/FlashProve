-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Eval/RunIsTerm.lean: IT SERVES THE EVALUATION ALONE: NO THEOREM ON THE COMMITTER
IMPORTS IT. One name that joins the links from what the evaluating programs compute to the value of
the algorithm `twinID` at the shape and table that ran. What stands in the commit field of the
description (Johnson/Bind/Cpp/Defs.lean) is the same Lean definition, at another shape and table.
Calls alone.

The links, in their order.
  (0) From a program with its prints (the evaluating programs and their steps; not all of them are
      in this library) to the chain of steps `fastSteps` at the hash `Fmt.HF`: A READING OF THE
      PROGRAM'S TEXT. No theorem speaks of input and output. (A program may keep answers that it has
      made at the same seeds: `answers_kept`, Johnson/Bind/TwinFastSteps.lean.)
  (1) `fastSteps` is the committer at the fast encoder (`commitFastW_steps`, the same file).
  (2) That is the committer, at shapes with a ≤ 32 and l + r ≤ 2^a (`commitFastW_is_commitW`,
      Johnson/Bind/TwinFastProof.lean).
  (3) `Fmt.HF` is the format's own hash (`Fmt.HF_eq`, Fmt/Rules5Fast.lean): so that is `commit`.
  (4) `commit`'s ID, read as a digest, is the value of the algorithm `twinID` at the hash function
      on bit strings that the format's realised oracle spells, where `Fits`
      (`evaluate_twinID_oBits`, Johnson/Bind/Eval/TwinAtOracle.lean).
Main names (namespace `Bind.Eval`).
  `steps_are_commit`: (1) to (3).
  **`runIsTerm`**: (1) to (4): the ID that the chain of steps gives is `twinID`'s value at that one
    hash function.
  `runIsTerm_small`, `runIsTerm_full`: at the small stored example's shape and at the full size's,
    at three public files of at most 2^31 bytes together: both shapes meet all premises.
Limits. Link (0) stays a reading; and a run is compiled code: that it gives the term's value rests
on Lean's compiler and runtime too, which the kernel does not check. One hash function, named;
nothing on an oracle that is sampled at random. It ties what is run in Lean to a value of `twinID`:
nothing on any program outside Lean. WHAT WAS RUN STANDS AT THE SMALL STORED EXAMPLE'S SHAPE: there
`twinID` stands in no commit field, and this library has for it no tie, no binding of the commitment
and no correctness of extraction (the general law on the tie, Johnson/Bind/CoreTie.lean, has no
instance at a small size). The theorems on the committer stand at the full size's shape, where
nothing has been run.

-/
import Johnson.Bind.Eval.TwinAtOracle
import Johnson.Bind.TwinFastSteps
import Johnson.Bind.TwinFastShapes
import Fmt.Rules5Fast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Eval
open Bind.Twin

/-- **The chain of steps at `Fmt.HF` gives what `commit` gives**, at shapes with a ≤ 32 and
l + r ≤ 2^a. -/
theorem steps_are_commit (S : Shape) (ha : S.a ≤ 32) (hS : S.l + S.r ≤ 2 ^ S.a)
    (files : List ByteArray) (T : Table) :
    fastSteps Fmt.HF S (Id.run (Fmt.configDigestW (m := Id) Fmt.HF files)) T =
      commit S files T := by
  have e : Fmt.HF = Fmt.formatHash := Fmt.HF_eq
  rw [e, ← commitFastW_steps Fmt.formatHash S files T,
    commitFastW_is_commitW (m := Id) Fmt.formatHash S ha hS files T]
  rfl

/-- **THE ID THAT THE CHAIN OF STEPS GIVES IS THE ALGORITHM'S VALUE AT ONE HASH FUNCTION.** -/
theorem runIsTerm (S : Shape) (ha : S.a ≤ 32) (hS : S.l + S.r ≤ 2 ^ S.a) (pol lay KL : ByteArray)
    (T : Table) (fits : Fits S [pol, lay, KL]) :
    _root_.Run.bytesToDig
        (fastSteps Fmt.HF S (Id.run (Fmt.configDigestW (m := Id) Fmt.HF [pol, lay, KL])) T).id =
      (twinID S pol lay KL T).evaluate (_root_.Run.oBits ()) := by
  rw [steps_are_commit S ha hS [pol, lay, KL] T, evaluate_twinID_oBits S pol lay KL T fits]

/-! ### The two shapes meet the premises -/

/-- The small stored example's shape: a ≤ 32. -/
theorem small_a : Anchor.shape.a ≤ 32 := by
  show 23 ≤ 32
  decide

/-- The small stored example's shape: l + r ≤ 2^a. -/
theorem small_room : Anchor.shape.l + Anchor.shape.r ≤ 2 ^ Anchor.shape.a := by
  show 524288 + 65535 ≤ 2 ^ 23
  decide

/-- The small stored example's shape: every call lies in the hash's domain. -/
theorem small_fits (files : List ByteArray) (hf : (Fmt.configBytes files).size ≤ 2 ^ 32 - 144) :
    Fits Anchor.shape files := fits_small files hf

/-- The full size's shape: a ≤ 32. -/
theorem full_a : fullShape.a ≤ 32 := by
  show 32 ≤ 32
  decide

/-- The full size's shape: l + r ≤ 2^a. -/
theorem full_room : fullShape.l + fullShape.r ≤ 2 ^ fullShape.a := by
  show 402653184 + 44040191 ≤ 2 ^ 32
  decide

/-- The full size's shape: every call lies in the hash's domain. -/
theorem full_fits (files : List ByteArray) (hf : (Fmt.configBytes files).size ≤ 2 ^ 32 - 144) :
    Fits fullShape files := fits_full files hf

/- Lean compares the two shapes by their names from here on. -/
attribute [local irreducible] Anchor.shape fullShape

/-- At the small stored example's shape. -/
theorem runIsTerm_small (pol lay KL : ByteArray) (T : Table)
    (h : pol.size + lay.size + KL.size ≤ 2 ^ 31) :
    _root_.Run.bytesToDig (fastSteps Fmt.HF Anchor.shape
        (Id.run (Fmt.configDigestW (m := Id) Fmt.HF [pol, lay, KL])) T).id =
      (twinID Anchor.shape pol lay KL T).evaluate (_root_.Run.oBits ()) :=
  runIsTerm Anchor.shape small_a small_room pol lay KL T
    (small_fits _ (files_three pol lay KL h))

/-- At the full size's shape. Nothing has been run there. -/
theorem runIsTerm_full (pol lay KL : ByteArray) (T : Table)
    (h : pol.size + lay.size + KL.size ≤ 2 ^ 31) :
    _root_.Run.bytesToDig (fastSteps Fmt.HF fullShape
        (Id.run (Fmt.configDigestW (m := Id) Fmt.HF [pol, lay, KL])) T).id =
      (twinID fullShape pol lay KL T).evaluate (_root_.Run.oBits ()) :=
  runIsTerm fullShape full_a full_room pol lay KL T (full_fits _ (files_three pol lay KL h))

end Bind.Eval

#print axioms Bind.Eval.steps_are_commit
#print axioms Bind.Eval.runIsTerm
#print axioms Bind.Eval.small_a
#print axioms Bind.Eval.small_room
#print axioms Bind.Eval.small_fits
#print axioms Bind.Eval.full_a
#print axioms Bind.Eval.full_room
#print axioms Bind.Eval.full_fits
#print axioms Bind.Eval.runIsTerm_small
#print axioms Bind.Eval.runIsTerm_full
