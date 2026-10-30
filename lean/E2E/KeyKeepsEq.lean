-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyKeepsEq.lean: WHAT THE STEP OF A SUB-PROTOCOL OF THE KEY FILE LEAVES OF THE VERIFIER's STATE
(the letter `keeps` of a thread, Johnson/Desc/ProofFile/Honest/Thread/Thr.lean): THE CLAUSES, at the
sixteen sub-protocols that belong to no kind: AN EQUATION ON THE WHOLE STATE: at eleven outright; at
five up to values that are bound by "there are". Definitions alone, off the library's texts of these
decisions. Their payers: E2E/KeyKeeps.lean, E2E/KeyKeepsLayer.lean; at the key file's own threads:
E2E/KeyKeepsAt.lean; what rides past: E2E/KeyRides.lean.

  `LayerKeeps`: a lookup's layer: the open ledger is turned; one list of rows and one list of claims
      on keys are appended; all else is as it was
  `eq₁ one other`, `eq₂ other`, `eq₃ other`: by the sub-protocol's number in its chain: the state is
      left as it was (nine) · the open lookup's ledger, what was heard and the homes are struck
      (two) · the caller's: of the statement's part the messages' ledgers alone may have turned
      (which, and how, is not said), and what was opened is not fenced; a fresh ledger is opened
      (two) · the layers (two) · the lookups' rows are laid onto the ranges' group (one). other: a
      letter: the clause at every other number: the kinds' sub-protocols

In the library's own words: `clr` (Johnson/RunOne/KeyTen.lean) · `withCall`, `CallGround`,
`ForkReady` (Johnson/RunOne/KeyCaller.lean) · `withD`, `RowsGround` (Johnson/RunOne/KeyThree.lean).

Limits. Definitions: nothing is shown here. THE CLAUSES GO BY THE SUB-PROTOCOL's NUMBER, not by its
place's kind. The numbers are those of a key file with two lookups, a message with W, and a place
for each of the shared chain's two tests. The proof file's first chain bears a mark of failure,
which its clauses ask to be unset; the key file's states bear none: nothing of the sort is asked.
That an item which is open across such a sub-protocol says behind it what it said in front is not
treated here.

-/
import Johnson.RunOne.KeyCaller
import Johnson.RunOne.KeyThree
import Johnson.RunOne.KeyTen
import Johnson.RunOne.KeyRows23At

set_option autoImplicit false

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (St₂ St₃)

/-- **What a layer's yes leaves.** -/
def LayerKeeps (s s' : FirstState) : Prop :=
  ∃ F' rows keys, s' =
    { s with base := { s.base with fork := some F', rows := s.base.rows ++ [rows],
                                   keys := s.base.keys ++ [keys] } }

/-- **The first chain's.** -/
def eq₁ (one : OnBytes.Params.OneTime) (other : Nat → FirstState → FirstState → Prop) :
    Nat → FirstState → FirstState → Prop
  | 2 | 6 | 8 | 12 | 18 => fun s s' => s' = s
  | 7 | 13 => fun s s' => s' = clr s
  | 5 | 11 => LayerKeeps
  | 3 => fun s s' => ∃ d' Fk hm, s' = withCall s d' Fk hm ∧ CallGround s d' ∧
      ForkReady (slots₁ one 0) Fk hm
  | 9 => fun s s' => ∃ d' Fk hm, s' = withCall s d' Fk hm ∧ CallGround s d' ∧
      ForkReady (slots₁ one 1) Fk hm
  | 14 => fun s s' => ∃ d', s' = withD s d' ∧ RowsGround s d' ∧ s.base.rows.length = 2
  | b => other b

/-- **The shared chain's.** -/
def eq₂ (other : Nat → St₂ → St₂ → Prop) : Nat → St₂ → St₂ → Prop
  | 0 | 11 => fun s s' => s' = s
  | b => other b

/-- **The last chain's.** -/
def eq₃ (other : Nat → St₃ → St₃ → Prop) : Nat → St₃ → St₃ → Prop
  | 1 | 3 => fun s s' => s' = s
  | b => other b

end AtPublicFiles.KeyThread
