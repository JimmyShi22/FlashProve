-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Seat/Core.lean: the proximity test's three seats (Johnson/Desc/K12/Seat.lean: the
tests on G_u and on G_omega at the shared chain; Seat/Own.lean: the request's own test at the last
chain) hand the statement, the book of trees and the count of roots to the kind's record as they
are, and lay these three back as they are. So a relation on the three (Johnson/Desc/CoreKeeps.lean:
Core) that the kind's block keeps at its own record T12 is kept by the seated block at the chain's
record. Theorems; R is any relation: nothing is asked of it.

  coreT, coreS₃        the three, off the kind's record and off the last chain's.
  onGu_keeps · onGomega_keeps · onOwn_keeps.
What is not claimed. THAT THE KIND's BLOCK KEEPS ANYTHING AT T12: that is the kind's files' to show.
Nothing on soundness or on hiding.

-/
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.BlockKeeps
import Johnson.Desc.CoreKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Seat
open OnBytes OnBytes.Params Desc.Plain Desc.K14
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Ground (Core coreOf ByC)
open VerifiableInference.Desc.Keeps (Decides)

/-- The three, off the record inside a proximity test. -/
def coreT (t : T12) : Core := ⟨t.st, t.book, t.roots⟩

/-- The three, off the last chain's record. -/
def coreS₃ (s : S₃) : Core := ⟨s.st, s.book, s.roots⟩

variable {R : Core → Core → Prop}

theorem inside_keeps (g : Lin → Nat) (mask : Lin → Option Nat) (b : Block T12 Unit)
    (hb : Decides (ByC R coreT) b) :
    Decides (ByC R fun d : St => coreOf d) (Block.inside (enter g mask) b leave) :=
  Keeps.inside_decides _ (ByC R coreT) _ b _
    (fun s t t' s' he hq hl => by
      cases he
      cases hl
      exact hq) hb

/-- **The test on G_u.** -/
theorem onGu_keeps (b : Block T12 Unit) (hb : Decides (ByC R coreT) b) :
    Decides (ByC R fun d : St => coreOf d) (onGu b) := inside_keeps _ _ b hb

/-- **The test on G_omega.** -/
theorem onGomega_keeps (b : Block T12 Unit) (hb : Decides (ByC R coreT) b) :
    Decides (ByC R fun d : St => coreOf d) (onGomega b) := inside_keeps _ _ b hb

/-- **The request's own test.** -/
theorem onOwn_keeps {Cl : Type} (b : Block T12 Cl) (hb : Decides (ByC R coreT) b) :
    Decides (ByC R coreS₃) (onOwn b) :=
  Keeps.inside_decides _ (ByC R coreT) _ b _
    (fun s t t' s' he hq hl => by
      cases he
      cases hl
      exact hq) hb

end VerifiableInference.Desc.K12.Seat
