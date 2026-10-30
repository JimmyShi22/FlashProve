-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/ClampPin.lean: A READER OF THE WITNESS AT WHICH THE LINK LAW's PREMISE
hpin («two witnesses with the context name one table»: LinkOwes.lean, `OwesLetters`) FOLLOWS FROM
THE TABLE's PINS. Definitions and theorems.

Why. hpin asks an equation of functions: the two witnesses' tables agree AT EVERY INDEX. The table's
accessor (`tabQ`, Johnson/Desc/Sound/FormsQ.lean) reads its reader at every index; the witness's
table at a seat (`seatTab`, Johnson/Desc/Sound/BordersFill.lean) is the witness's own function, at
every row and place; a pin fixes a member's message inside its ranges alone (`pinAt_one`,
Johnson/Desc/Sound/MeaningSig.lean: an equation of typed messages). So at the reader `seatTab` the
pins do not give hpin: `pins_blind` says it in Lean: a witness that is turned outside the members'
ranges stays pinned. The law's reader is a free letter. Here it is the member's TYPED message, read
back as a table, 0 outside the ranges: the library's own term for that (`toMsgT`,
Johnson/Desc/Sound/World.lean), at the member that sits at the seat.

What is said.
  `rdC cs arr ms w x`: **the reader**: `toMsgT` of the typed message (`msgsOf`) of the member of ms
    that sits at the seat x; the zero table at a seat that is no member's. `rdC_inside`: **inside
    the member's ranges (`InMsg`) it is `seatTab`** (by `msgs_forth`). `rdC_outside`: outside them
    it is 0. `rdC_pin`: two witnesses that are pinned at a seat have one value of the reader there.
    `hpin_at`: **hpin, at `tabAt own (rdC cs arr ms w)` and the context `ctxPins`**, where every
    seat of own is a tenant of one of the segment's three moments. `pins_blind`: two witnesses with
    the same typed messages at the members of ms are pinned together.

Limits. The law's relations at this reader (the runs' forms are worth 0; the one sum is 0; the
equation's row holds) are NOT YET held against the composed meaning's sentences, which read
`seatTab`: that wants «what these sentences read lies inside the members' ranges». «Every seat of
own is a tenant of one of the three moments» is a premise on the plan's numbers. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.PinsBack
import Johnson.Desc.First.Batch.Law.AtTable
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker Cb
open Johnson.Pack
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Meaning Numbers)

variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)

/-- **THE READER**: the typed message of the member of ms that sits at the seat, as a table. -/
noncomputable def rdC (w : Wit Cells Tok MsgT) (x : ℕ × ℕ) : MsgT :=
  match ms.find? fun y => decide (seatOf y = x) with
  | some y => toMsgT cs y.1.l y.2 (msgsOf cs y.1.l y.1.seat arr w y.2)
  | none => fun _ _ _ => 0

/-- **Inside the member's ranges it is seatTab.** -/
theorem rdC_inside (w : Wit Cells Tok MsgT) (x : ℕ × ℕ) (y : Mem)
    (hy : (ms.find? fun y => decide (seatOf y = x)) = some y) (mask : Bool) (row place : ℕ)
    (h : InMsg cs (y.1.l.get y.2).1 mask row place) :
    rdC cs arr ms w x mask row place = seatTab cs arr ms w x mask row place := by
  unfold rdC seatTab
  rw [hy]
  exact (msgs_forth cs y.1.l y.1.seat arr w y.2 mask row place h).symm

/-- Outside them it is 0. -/
theorem rdC_outside (w : Wit Cells Tok MsgT) (x : ℕ × ℕ) (y : Mem)
    (hy : (ms.find? fun y => decide (seatOf y = x)) = some y) (mask : Bool) (row place : ℕ)
    (h : ¬ InMsg cs (y.1.l.get y.2).1 mask row place) :
    rdC cs arr ms w x mask row place = 0 := by
  unfold rdC
  rw [hy]
  show toMsgT cs y.1.l y.2 _ mask row place = 0
  unfold InMsg at h
  unfold toMsgT
  cases mask
  · rw [if_neg (by decide)] at h
    rw [if_neg (by decide), dif_neg h]
  · rw [if_pos rfl] at h
    rw [if_pos rfl, dif_neg h]

variable {P Xi : Type} (G : FileDescription Xi)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- Two witnesses that are pinned at a seat have one value of the reader there. -/
theorem rdC_pin (x : ℕ × ℕ) (a : P × S) (y : Strs) (w w' : Wit Cells Tok MsgT)
    (h : pinJT cs G arr smp ms x.1 x.2 a y w) (h' : pinJT cs G arr smp ms x.1 x.2 a y w') :
    rdC cs arr ms w x = rdC cs arr ms w' x := by
  unfold rdC
  cases e : ms.find? fun y => decide (seatOf y = x) with
  | none => rfl
  | some v =>
    have hv : v ∈ ms := List.mem_of_find?_eq_some e
    have hs : SitsAt v x.1 x.2 := by
      have h1 := List.find?_some e
      have h0 : seatOf v = x := by simpa using h1
      exact h0
    show toMsgT cs v.1.l v.2 (msgsOf cs v.1.l v.1.seat arr w v.2) =
      toMsgT cs v.1.l v.2 (msgsOf cs v.1.l v.1.seat arr w' v.2)
    rw [pinAt_one cs G arr smp v a y w w' (h.2 v hv hs) (h'.2 v hv hs)]

variable {F : Frame}

/-- **hpin, AT THE READER rdC AND THE CONTEXT ctxPins.** -/
theorem hpin_at (Nm : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
    (hP : Mg.pin = pinJT cs G arr smp ms) (z : P) (m : ℕ) (own : List (ℕ × ℕ))
    (hown : ∀ x ∈ own, ∃ t < 3, x ∈ Nm.sent m t) (a : S × F.E.Str) (w w' : Wit Cells Tok MsgT)
    (h : ctxPins Nm Mg z m a w) (h' : ctxPins Nm Mg z m a w') :
    tabAt own (rdC cs arr ms w) a.1 = tabAt own (rdC cs arr ms w') a.1 := by
  have e : ∀ x ∈ own, rdC cs arr ms w x = rdC cs arr ms w' x := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hown x hx
    have h1 := h t ht x hxt
    have h2 := h' t ht x hxt
    rw [hP] at h1 h2
    exact rdC_pin cs arr ms G smp x _ _ w w' h1 h2
  unfold tabAt
  cases K9.atS.get? a.1 with
  | none => rfl
  | some q => exact tabQ_congr own q.d.st q.d.book _ _ e

/-- **THE PINS ARE BLIND OUTSIDE THE RANGES**: two witnesses with the same typed messages at the
members of ms are pinned together. -/
theorem pins_blind (j t : ℕ) (a : P × S) (y : Strs) (w w' : Wit Cells Tok MsgT)
    (e : ∀ x ∈ ms, msgsOf cs x.1.l x.1.seat arr w' x.2 = msgsOf cs x.1.l x.1.seat arr w x.2)
    (h : pinJT cs G arr smp ms j t a y w) : pinJT cs G arr smp ms j t a y w' := by
  refine ⟨h.1, fun x hx hs => ?_⟩
  obtain ⟨v, hv, h2, h3⟩ := h.2 x hx hs
  exact ⟨v, hv, h2, by rw [e x hx]; exact h3⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rdC_inside
#print axioms VerifiableInference.Desc.LinkJoin.rdC_outside
#print axioms VerifiableInference.Desc.LinkJoin.rdC_pin
#print axioms VerifiableInference.Desc.LinkJoin.hpin_at
#print axioms VerifiableInference.Desc.LinkJoin.pins_blind
