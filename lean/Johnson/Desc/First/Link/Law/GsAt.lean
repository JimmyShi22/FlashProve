-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/GsAt.lean: THE GROUPS' NUMBER, MEMBERS AND KEPT MEMBERS ARE AS THEY WERE
BEHIND AN ACCEPTING STEP OF EACH OF A LINK's FOUR LAST SUB-PROTOCOLS OF THE BATCHING KIND AND THE
FRAME (our files call a sub-protocol a block): the batching, the frame's sub-protocol behind it, the
one equation, the shutting. The relation is the one that the code switch's condition asks of
whatever stands between two switches. A definition and theorems.

What is said.
  `GS`, `GS.refl`, `gs_of_eq`, `gs_push` LIE IN THE LIGHT FILE GsDef.lean.
    Here: `gs_of_rb`: `Rb` (RbDef.lean: the statement is as it was) gives GS. `gs_of_lays`:
    `EqLays` (EqLays.lean) gives GS. `gs_batch`, `gs_behind`, `gs_eq`, `gs_shut`: **GS at an
    accepting step of each of the four.**

Limits. At the batching and behind it the runs' share is a premise, in the form of `TwoBlocks`
(LinkAtSort.lean). The rows of a group may grow: GS does not read them. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.GsDef
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.EqLays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.First (S)

theorem gs_of_rb {s s' : S} (R : Rb s s') : GS s.st s'.st := gs_of_eq R.st

theorem gs_of_lays {s s' : S} {g : ℕ} {row : OnBytes.Row} (E : EqLays s s' g row) :
    GS s.st s'.st := gs_push _ _ g row E.groups

/-- **At the batching.** -/
theorem gs_batch (L : Link S Claim) (pp : Where) (T : TwoBlocks L pp) (ft : ℕ) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) : GS s.st s'.st :=
  gs_of_rb (T.1 ft s rs cols s' k h).1

/-- **At the frame's sub-protocol behind the batching.** -/
theorem gs_behind (L : Link S Claim) (pp : Where) (T : TwoBlocks L pp) (ft : ℕ) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) : GS s.st s'.st :=
  gs_of_rb (T.2 ft s rs cols s' k h).1

/-- **At the one equation.** -/
theorem gs_eq {Cl : Type} (pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₃.step ft s rs cols = .ok (s', k)) : GS s.st s'.st := by
  obtain ⟨_, _, _, _, _, E⟩ := eq_lays pw b₃ hb₃ ft s rs cols s' k h
  exact gs_of_lays E

/-- **At the shutting.** -/
theorem gs_shut {Cl : Type} (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₅.step ft s rs cols = .ok (s', k)) : GS s.st s'.st :=
  gs_of_rb (rb_shutB pw piece b₅ hb₅ ft s rs cols s' k h).1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.gs_batch
#print axioms VerifiableInference.Desc.LinkJoin.gs_behind
#print axioms VerifiableInference.Desc.LinkJoin.gs_eq
#print axioms VerifiableInference.Desc.LinkJoin.gs_shut
