-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Tidy/Still.lean: the blocks that leave the statement as it is keep every reflexive
relation on statements: a chain's last block, whichever the chain; the two quiet steps behind the
layers' and the head's links; the block that ties the taken trees' sources. Statements with
their proofs, in the form `Decides (By R st)` (Johnson/Desc/FoldKeeps.lean,
Johnson/Desc/GroundKeeps.lean).
Main names: `chainEnd_same`, `chainEnd_still`, `firstEnd_still`, `end₃_still`, `layers_still`,
`head_still`, `takenSources_still`.

What is not claimed. Nothing on what these blocks test. Nothing on soundness.

-/
import Johnson.Desc.GroundKeeps
import Johnson.Desc.FoldKeeps
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.K13.FirstEnd
import Johnson.Desc.Third.Law.Keeps
import Johnson.Desc.Third.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps
open OnBytes
open VerifiableInference.Desc.Ground (By)

variable {T Cl : Type}

/-- A chain's last block leaves the record as it is. -/
theorem chainEnd_same (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : T → ChainEnd.Clauses) {s s' : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (ChainEnd.chainEnd chain piece sealed inFront asks : Block T Cl).decide s rs gs = .ok s') :
    s' = s := by
  have h' : (ChainEnd.refuse (asks s)).map (fun _ => s) = .ok s' := h
  cases hr : ChainEnd.refuse (asks s) with
  | error e =>
    rw [hr] at h'
    cases h'
  | ok u =>
    rw [hr] at h'
    exact (Except.ok.inj h').symm

variable {R : Statement → Statement → Prop} (hr : ∀ A, R A A)
include hr

theorem chainEnd_still (st : T → Statement) (chain piece : Nat) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (asks : T → ChainEnd.Clauses) :
    Decides (By R st) (ChainEnd.chainEnd chain piece sealed inFront asks : Block T Cl) := by
  intro s rs gs s' h
  rw [chainEnd_same chain piece sealed inFront asks h]
  exact hr _

/-- The first chain's last block. -/
theorem firstEnd_still (piece : Nat) (front : List (Block First.S Cl)) :
    Decides (By R fun s : First.S => s.st) (First.firstEnd piece front) :=
  chainEnd_still hr _ _ _ _ _ _

/-- The third chain's last block. -/
theorem end₃_still (inFront : List (Block Third.S₃ Cl)) :
    Decides (By R fun s : Third.S₃ => s.st) (Third.end₃ inFront) :=
  chainEnd_still hr _ _ _ _ _ _

/-- The quiet step at a layers' link. -/
theorem layers_still (P : K8.ReadsQuiet.PG) :
    Decides (By R fun s : First.S => s.st) (K8.ReadsQuiet.layers P) := by
  intro s rs gs s' h
  show R s.st s'.st
  rw [(K8.ReadsQuiet.layers_frame h).2.2.1]
  exact hr _

/-- The quiet step at the head's link. -/
theorem head_still (P : K8.ReadsQuiet.PH) :
    Decides (By R fun s : First.S => s.st) (K8.ReadsQuiet.head P) := by
  intro s rs gs s' h
  show R s.st s'.st
  rw [(K8.ReadsQuiet.head_frame h).2.2.1]
  exact hr _

/-- The block that ties the taken trees' sources. -/
theorem takenSources_still (own : Block Third.S₃ Cl) :
    Decides (By R fun s : Third.S₃ => s.st) (Third.takenSources own) := by
  intro s rs gs s' h
  rw [Third.Law.takenSources_same own s s' rs gs h]
  exact hr _

end VerifiableInference.Desc.Keeps
