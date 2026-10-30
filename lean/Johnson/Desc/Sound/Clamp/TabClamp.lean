-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/Clamp/TabClamp.lean: an entry of a table of the witness (`tabQ`,
Johnson/Desc/Sound/FormsQ.lean) is the same at the reader that is clamped to each oracle message's
own ranges (`LinkJoin.rdC`, Johnson/Desc/First/Link/Law/ClampPin.lean) and at the reader that is not
(`seatTab`), wherever the entry lies inside the ranges of the member that sits at the message's
seat. One statement and its proof; no definition.

  `tabQ_clamp`  tabQ own st book (rdC cs arr ms w) o part J = tabQ own st book (seatTab cs arr ms w)
                o part J
Why: as CellAgree.lean: it is the agreement at single entries that `dataQ_cell_agree` and
`dataQ_mask_agree` ask.
Limits. That an entry which the layout reads lies inside the member's ranges is not said here. Where
no member sits at the seat both readers give 0. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.ClampPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model

/-- **Inside the member's ranges the two readers give a table's entry one value.** -/
theorem tabQ_clamp {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (own : List (ℕ × ℕ)) (st : OnBytes.Statement) (book : OnBytes.TreeBook)
    (w : Wit Cells Tok MsgT) (o J : ℕ) (part : OnBytes.Part)
    (h : ∀ x y, K9.seatAt own book o = some x →
      (ms.find? fun y => decide (seatOf y = x)) = some y →
      InMsg cs (y.1.l.get y.2).1 (part == .mask) (J % 2 ^ st.rowBits o part)
        (J / 2 ^ st.rowBits o part)) :
    tabQ own st book (LinkJoin.rdC cs arr ms w) o part J =
      tabQ own st book (seatTab cs arr ms w) o part J := by
  unfold tabQ
  cases e : K9.seatAt own book o with
  | none => rfl
  | some x =>
    dsimp only
    cases e2 : ms.find? fun y => decide (seatOf y = x) with
    | some y => exact LinkJoin.rdC_inside cs arr ms w x y e2 _ _ _ (h x y e e2)
    | none =>
      unfold LinkJoin.rdC seatTab
      rw [e2]

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tabQ_clamp
