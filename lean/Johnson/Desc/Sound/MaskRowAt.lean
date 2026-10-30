-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MaskRowAt.lean: a segment's mask row off the witness, as a term: the pair with the
verifier's state, the witness, an entry's number ↦ a field element. The companion of `cellsAt`
(Johnson/Desc/Sound/CellsAt.lean).

  `maskRowAt cs arr ms N m a w j`
      where the verifier's state `a.2` has an open segment's part `p` (`K9.segAt?`): entry `j` of the mask row of
      `dataQ (N.group m) p` (Johnson/Desc/Sound/FormsQ.lean) off the witness's tables at the seats
      (`seatTab`, Johnson/Desc/Sound/BordersFill.lean); 0 where the state has no such part.
  `maskRowAt_of_part`, `maskRowAt_none`   the two arms.
  `maskRowAt_congr`   two witnesses whose tables agree at the seats of `N.group m` give one mask row.

Why this accessor. It is the mask row as the sentences "forms" read it: the sentence "weights" at the
head's segment is meant to read the same row, so that no equation between two readers is owed. The
choice of the term is its owner's (whoever composes the layer `fillP1`); this file types it.

The name. `maskRowAt`, not `maskAt`: Johnson/Desc/Sound/FormsQ.lean has a lemma `maskAt_eq` in this
namespace, on another function.

Limits. Which segment's number `m` is the head's is the caller's matter. At a seat that is no
member's `seatTab` is the zero message. Nothing on soundness.

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (Numbers)

variable {P Cells Tok : Type}

/-- **Segment m's mask row, off the witness.** -/
noncomputable def maskRowAt (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (a : P × First.S) (w : Wit Cells Tok MsgT) (j : ℕ) : Cb.Gl.E :=
  ((K9.segAt? a.2).map fun a9 => (dataQ (N.group m) a9 (seatTab cs arr ms w)).mask j).getD 0

/-- At a state with an open segment's part. -/
theorem maskRowAt_of_part (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (a : P × First.S) (w : Wit Cells Tok MsgT) (j : ℕ) (p : K9.Part) (h : K9.segAt? a.2 = some p) :
    maskRowAt cs arr ms N m a w j = (dataQ (N.group m) p (seatTab cs arr ms w)).mask j := by
  simp only [maskRowAt, h, Option.map_some, Option.getD_some]

/-- At a state without one: 0. -/
theorem maskRowAt_none (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (a : P × First.S) (w : Wit Cells Tok MsgT) (j : ℕ) (h : K9.segAt? a.2 = none) :
    maskRowAt cs arr ms N m a w j = 0 := by
  simp only [maskRowAt, h, Option.map_none, Option.getD_none]

/-- Two witnesses whose tables agree at the seats of segment m's own list give one mask row. -/
theorem maskRowAt_congr (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (a : P × First.S) (w w' : Wit Cells Tok MsgT)
    (h : ∀ x ∈ N.group m, seatTab cs arr ms w x = seatTab cs arr ms w' x) (j : ℕ) :
    maskRowAt cs arr ms N m a w j = maskRowAt cs arr ms N m a w' j := by
  unfold maskRowAt
  cases K9.segAt? a.2 with
  | none => rfl
  | some p =>
    show (dataQ (N.group m) p (seatTab cs arr ms w)).mask j =
      (dataQ (N.group m) p (seatTab cs arr ms w')).mask j
    rw [dataQ_congr (N.group m) p _ _ h]

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.maskRowAt_of_part
#print axioms VerifiableInference.Desc.Sound.maskRowAt_none
#print axioms VerifiableInference.Desc.Sound.maskRowAt_congr
