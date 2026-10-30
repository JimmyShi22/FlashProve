-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadAt.lean: THE MESSAGES AS ONE SEGMENT READS THEM OFF A WITNESS. Five
definitions and three lemmas. No protocol's soundness is said.

Why. A message that is sent again is sent with another pad: the witness holds one component for all
copies outside the pads, and a pad a copy (`Wit.pad`, Johnson/Desc/Msg.lean). What a segment's pins
fix are the tables of ITS OWN group's copies. So whoever reads, for segment k, "the message with the
number n" reads it through the one accessor at the seat of segment k's own copy.
  `readAt cs arr ms N k w`: number ↦ table: `seatTab` (BordersFill.lean) at the tenant x of
    `N.group k` with arr x = n. Where the group has no such tenant: the zero message, which nothing
    pins.
  `namedOnce arr N k n`: a Bool: the group has just one tenant with that number.
  `SeatsNamed arr N s seat`: every number that a segment's seats name, within its sizes, is so.
  `GroupsSeated ms N`: every tenant of every group is a member's seat: else `seatTab` reads the
    zero message.
  `readAt_of_named` (proved): under the test the reader is the accessor at THE tenant with that
    number: whoever proves a law never sees the search.
THE TWO CONDITIONS ARE ON PUBLIC LETTERS ALONE; NEITHER HAS RUN AT A PLAN. Whoever lays `readAt`
under a relation takes both as premises (Johnson/P5J/MeansQ.lean's hidAtSeat has them as arguments).

  `OffPad`, `readAt_offPad`: at a place that is no pad's place of the segment's own copy the reader
    gives the one component that all copies share: so two segments' readings agree there
    (`readAt_agree`).

Limits. At a pad's place two segments' readings part. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersFill
import Cb.Pv.Tail.InLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers)

/-- **The messages as segment k reads them off a witness.** -/
def readAt {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
    (k : ℕ) (w : Wit Cells Tok MsgT) : ℕ → MsgT :=
  fun n => match (N.group k).find? fun x => arr x.1 x.2 == n with
    | some x => seatTab cs arr ms w x
    | none => fun _ _ _ => 0

/-- A TEST ON THE PLAN's NUMBERS: segment k's group has just one tenant with the number n. -/
def namedOnce (arr : ℕ → ℕ → ℕ) (N : Numbers) (k n : ℕ) : Bool :=
  ((N.group k).filter fun x => arr x.1 x.2 == n).length == 1

/-- Every number that a segment's seats name, within its sizes, has just one tenant in that
segment's own group. -/
def SeatsNamed (arr : ℕ → ℕ → ℕ) (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) : Prop :=
  ∀ k (μ : Fin (s k).NM) (r c : ℕ), r < Alg.symRows ((s k).m μ) → c < (s k).k μ →
    namedOnce arr N k (seat k μ r c).1 = true

/-- Every tenant of every segment's group is the seat of a member of ms. -/
def GroupsSeated (ms : List Mem) (N : Numbers) : Prop :=
  ∀ k, ∀ x ∈ N.group k, ∃ y ∈ ms, seatOf y = x

/-- **Under the test the reader is the accessor at THE tenant with that number.** -/
theorem readAt_of_named {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (N : Numbers) (k n : ℕ) (w : Wit Cells Tok MsgT) (h : namedOnce arr N k n = true) :
    ∃ x, ((N.group k).filter fun x => arr x.1 x.2 == n) = [x] ∧
      readAt cs arr ms N k w n = seatTab cs arr ms w x := by
  unfold namedOnce at h
  have hl : ((N.group k).filter fun x => arr x.1 x.2 == n).length = 1 := eq_of_beq h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl
  refine ⟨x, hx, ?_⟩
  have hf : ((N.group k).find? fun x => arr x.1 x.2 == n) = some x := by
    rw [← List.head?_filter, hx]
    rfl
  unfold readAt
  rw [hf]

/-- The main row r's place p of the message with the number n is no pad's place of segment k's own
copy: of whichever member of ms sits in the group with that number. A condition on public letters
alone. -/
def OffPad (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (k n r p : ℕ) :
    Prop :=
  ∀ y ∈ ms, seatOf y ∈ N.group k → numOf arr y = n → padB cs (y.1.l.get y.2).1 false r p = false

/-- **OUTSIDE THE PADS EVERY SEGMENT READS THE ONE COMPONENT THAT ALL COPIES SHARE**: so two
segments' readings of one message agree there. -/
theorem readAt_offPad {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (N : Numbers) (k n r p : ℕ) (w : Wit Cells Tok MsgT) (hn : namedOnce arr N k n = true)
    (hg : GroupsSeated ms N) (ho : OffPad cs arr ms N k n r p) :
    readAt cs arr ms N k w n false r p = w.msg n false r p := by
  obtain ⟨x, hx, e⟩ := readAt_of_named cs arr ms N k n w hn
  rw [e]
  have hm : x ∈ (N.group k).filter fun x => arr x.1 x.2 == n := by
    rw [hx]
    exact List.mem_singleton.2 rfl
  have hm' := List.mem_filter.1 hm
  have hxn : arr x.1 x.2 = n := eq_of_beq hm'.2
  obtain ⟨y, hy, hs⟩ := hg k x hm'.1
  unfold seatTab
  cases hf : ms.find? fun y => decide (seatOf y = x) with
  | none => exact absurd (decide_eq_true hs) (by simpa using List.find?_eq_none.1 hf y hy)
  | some y' =>
    have hd' : decide (seatOf y' = x) = true :=
      List.find?_some (p := fun y => decide (seatOf y = x)) hf
    have hs' : seatOf y' = x := of_decide_eq_true hd'
    have hn' : numOf arr y' = n := by
      show arr (seatOf y').1 (seatOf y').2 = n
      rw [hs', hxn]
    have hp := ho y' (List.mem_of_find?_eq_some hf) (hs' ▸ hm'.1) hn'
    show (memTab cs arr w y') false r p = w.msg n false r p
    unfold memTab Wit.tab
    rw [if_neg (by rw [hp]; exact Bool.false_ne_true), hn']

/-- **Two segments' readings of one message agree** at a place that is no pad's place of either's
own copy. -/
theorem readAt_agree {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (N : Numbers) (k k' n r p : ℕ) (w : Wit Cells Tok MsgT) (hn : namedOnce arr N k n = true)
    (hn' : namedOnce arr N k' n = true) (hg : GroupsSeated ms N)
    (ho : OffPad cs arr ms N k n r p) (ho' : OffPad cs arr ms N k' n r p) :
    readAt cs arr ms N k w n false r p = readAt cs arr ms N k' w n false r p :=
  (readAt_offPad cs arr ms N k n r p w hn hg ho).trans
    (readAt_offPad cs arr ms N k' n r p w hn' hg ho').symm

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readAt_of_named
#print axioms VerifiableInference.Desc.Sound.readAt_offPad
#print axioms VerifiableInference.Desc.Sound.readAt_agree
