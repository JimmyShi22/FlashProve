-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedJoin.lean: the lists of read leaves that are right for the forests
are right for the strict format.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Two files say parts of the verifier of OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean again along lists of
leaves. ListedForests.lean asks of the lists of read leaves that each is the rising list of the
leaves at which a read position stands (LeavesOK). ListedStrict.lean asks that a leaf at which a
position stands is in its tree's list just where the position is read (ReadsOK). Both speak of the
trees that the wiring lists alone (those that have a depth). The first gives the second, at every
wiring: no law of the wire records is asked.

Main theorem. readsOK_of_leavesOK: LeavesOK s A W isRead rd → ReadsOK s A W isRead rd.

Limits. The converse is not claimed: ReadsOK lets a list be unsorted or hold a number twice,
LeavesOK does not. Nothing on where such lists come from. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedStrict
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedForests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {lam K : ℕ}

/-- **The lists that are right for the forests are right for the strict format.** -/
theorem readsOK_of_leavesOK :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (isRead : OPos s → Bool)
      (rd : List (List (List ℕ) × List (List ℕ))),
      LeavesOK s A W isRead rd → ReadsOK s A W isRead rd
  | [], _, _, _, _, _ => trivial
  | _ :: s, (_, A), (w, W), isRead, rd, h => by
    have h' : LeavesT w.posAt0 (fun p => isRead (.inl p)) 0 w.depth0 (rd.headD ([], [])).1 ∧
        LeavesT w.posAtJ (fun p => isRead (.inl p)) 0 w.depthJ (rd.headD ([], [])).2 ∧
        LeavesOK s A W (fun p => isRead (.inr p)) rd.tail := h
    exact ⟨fun _ hk _ _ hj hp => leavesT_contains_getD h'.1 hk hj hp,
      fun _ hk _ _ hj hp => leavesT_contains_getD h'.2.1 hk hj hp,
      readsOK_of_leavesOK s A W _ rd.tail h'.2.2⟩

end TypedOracleCompiler.Compile.Batch
