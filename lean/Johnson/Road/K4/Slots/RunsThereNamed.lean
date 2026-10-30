-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Slots/RunsThereNamed.lean: RunsThere.lean's STATEMENT ON THE RUN "front" WITH ITS
THREE PREMISES ON WHAT THE LOOKUP RETURNED PAID OUT OF ONE RECORD OF THE LOOKUP's OWN:
`Fo.Tp.PadNames g F` (Johnson/Top/H/Keep/PadNamed.lean: every slot that a row of the lookup's, the
slot of its bits' shown value, or its leaves' start form names is filled in the ledger F behind the
lookup's hearing), AT THE LEDGER FROM WHICH K4's HEARING STARTS. Statements and proofs: calls.

  `of_slot`: a form that is one slot names that slot.
  `named_filled`: what is `Named F` names slots alone that are filled in every ledger Gr that keeps
    what is filled in F.
  **`front_there_named`**: F sized; K4's hearing returns (o, G, u) from F; Gr keeps what is filled
    in G and is sized; `PadNames o.H.fo F`; `formsFrontWith rows P g o Gr` returns (fs, F₁), at
    either form of the run: every slot that a form of fs names is filled in F₁.

Limits. `PadNames` AT K4's OWN o.H.fo AND AT THE LEDGER F IS A PREMISE: the lookup's law has it of
the record and the ledger that ITS hearing returns (`pad_named`): that these are what K4 was handed
is not said here. Of `PadNames` the halves on slots alone are spent; its field cEnd not at all
("back" needs no such premise: `back_there`). One direction, from returns. Nothing on soundness.

-/
import Johnson.Road.K4.Slots.RunsThere
import Johnson.Top.H.Keep.PadNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Sized Filled)
open _root_.Fo.Tp (PadNames Named In)

/-- A form that is one slot names that slot. -/
theorem of_slot {S : ℕ → Prop} {j : ℕ} (h : SlotsIn S (Aff.slot j)) : S j :=
  h (j, oneE) (by simp [Aff.slot])

/-- What is named at F is filled wherever what is filled in F is. -/
theorem named_filled {F Gr : Fork} (hk : ∀ j, Filled F j → Filled Gr j) {f : Aff}
    (h : Named F f) : SlotsIn (Filled Gr) f :=
  slotsIn_mono (fun j hj => hk j hj.2) h.2

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G Gr F₁ : Fork}
  {t0 u : Tape} {fs : Array Aff}

/-- **Behind the run "front", at either form, every slot that its forms name is filled: under the
lookup's own record at the ledger from which K4's hearing starts.** -/
theorem front_there_named (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hG : ∀ j, Filled G j → Filled Gr j) (sG : Sized Gr) (N : PadNames o.H.fo F) {rows : Bool}
    (hr : formsFrontWith rows P g o Gr = some (fs, F₁)) :
    ∀ f ∈ fs.toList, SlotsIn (Filled F₁) f := by
  have hL := hearFl_later (P := P) (hp := hp) (g := g) (fo := fo) h
  have hk : ∀ j, Filled F j → Filled Gr j := fun j hj => hG j (hL.keep j hj).1
  exact front_there hF h hG sG hr (fun _ f hf => named_filled hk (N.rows f hf))
    (hk _ (of_slot N.sBit.2).2) (named_filled hk N.start)

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.front_there_named
