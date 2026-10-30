-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PublicAtJoined.lean: the kind "the code switch" (K2): THE LOT's
PUBLIC TEST ON A FILLING (`publicOk`, Honest/K2/Sim.lean) AT THE JOINED FILLING (`withSwitchData`,
Honest/K2/OwnData.lean): WHAT OF IT IS ASKED OF THE DATA OF THE SWITCHES' OWN MESSAGES, WHICH DOES
NOT HANG ON THE PUBLIC INSTANCE, AND WHAT OF THE OTHER LOT's DATA. Three statements with their
proofs: joins; no definition.

  `arraysLaidLight_lays`   the light test on one message reads of a filling its field `lays` at that
                           message's address alone
  `arraysLaidLight_with`   so at the joined filling it is the test at the switches' own data where
                           the address has a seat, and at the other lot's data elsewhere
  `publicOk_with`          THE SPLIT

THE PREMISES OF `publicOk_with`, ALL OF THEM. (1) OF EACH OWN MESSAGE OF EACH SEGMENT OF THE LIST
segs (the lot's caller lays the segments in front of the switch there): it has an address, and the
light test (`arraysLaidLight`, Honest/K2/Law/LaidLight.lean) says yes there: AT THE SWITCHES' OWN
DATA if the address has a seat of a switch's, AT THE OTHER LOT's DATA AT THE PUBLIC INSTANCE if not.
(2) OF EACH OWN MESSAGE OF THE SWITCH's OWN SENDING: its address has a seat; the light test says yes
at the switches' own data; that data is ready there at no challenge. General in the other lot's
data, the place and the segments.

Why: the debt "it plays" at the frame's thread asks `publicOk` at one input's public instance. At a
filling of this form all of (2), and of (1) what stands at an earlier switch's address, is a test
with code that does not read the instance x: it reads S, Z, G, the layout and the place; what reads
x is the other lot's data.

By: `publicOk_of_light` (Honest/K2/Law/LaidLight.lean) · `with_own_lays`, `with_own_ready`
(Honest/K2/OwnData.lean) · `with_else_lays` (Honest/K2/Law/OwnDataApart.lean).

Limits. ONE WAY ALONE, AS THE LIGHT TEST IS: its no means nothing. THE PREMISES ARE SHOWN AT NO
PLACE AND NO FILLING HERE. Which addresses have a seat is not said (`switchSeat_own`,
`switchSeat_none`, Honest/K2/Law/OwnDataApart.lean, say it of a switch's own addresses and of
senders of another kind). Nothing on what the closing leaves. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LaidLight
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnDataApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace (Sz)

variable {Xi : Type}

/-- The light test on one message reads of a filling its field `lays` at the address alone. -/
theorem arraysLaidLight_lays {D D' : RowData} {a : MsgAddr} (h : D.lays a = D'.lays a)
    (lay : OnBytes.Params.ReqLayout) (codes : OnBytes.Codes) (s : OnBytes.OracleShape)
    (seg m : Nat) :
    arraysLaidLight D lay codes s seg m a = arraysLaidLight D' lay codes s seg m a := by
  unfold arraysLaidLight
  rw [h]

/-- At the joined filling: the switches' own data where the address has a seat, the other lot's
elsewhere. -/
theorem arraysLaidLight_with (S : Sz) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground)
    (x : Xi) (lay : OnBytes.Params.ReqLayout) (codes : OnBytes.Codes) (s : OnBytes.OracleShape)
    (seg m : Nat) (a : MsgAddr) :
    arraysLaidLight (withSwitchData S D Z G x) lay codes s seg m a =
      arraysLaidLight (if (switchSeat Z G a).isSome = true then switchData S Z G else D Z G x) lay
        codes s seg m a := by
  by_cases h : (switchSeat Z G a).isSome = true
  · rw [if_pos h]
    exact arraysLaidLight_lays (with_own_lays S D Z G x a h) lay codes s seg m
  · rw [if_neg h]
    exact arraysLaidLight_lays (with_else_lays S D Z G x a (by simpa using h)) lay codes s seg m

/-- **THE SPLIT.** -/
theorem publicOk_with (S : Sz) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi)
    (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace) (segs : List SegmentPub)
    (h1 : ∀ y ∈ segs.zipIdx, ∀ s ∈ (y.1.ownShapes (y.2 == 0)).zipIdx,
      ∃ a, p.addrs y.2 s.2 = some a ∧
        arraysLaidLight (if (switchSeat Z G a).isSome = true then switchData S Z G else D Z G x)
          lay y.1.sizes.codes s.1 y.2 s.2 a = true)
    (h2 : ∀ n ∈ (p.others.toList.take (p.others.size - 1)).zipIdx,
      (switchSeat Z G (p.ownAddr n.2)).isSome = true ∧
        arraysLaidLight (switchData S Z G) lay p.sizes.codes n.1.shape p.link n.2
          (p.ownAddr n.2) = true ∧
        (switchData S Z G).readyAt [] (p.ownAddr n.2) = true) :
    publicOk (withSwitchData S D Z G) lay p segs x = true := by
  refine publicOk_of_light _ lay p segs x ?_
  unfold ownLaidLight
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun y hy => List.all_eq_true.2 fun s hs => ?_, fun n hn => ?_⟩
  · obtain ⟨a, ea, ha⟩ := h1 y hy s hs
    rw [ea]
    show arraysLaidLight (withSwitchData S D Z G x) lay y.1.sizes.codes s.1 y.2 s.2 a = true
    rw [arraysLaidLight_with]
    exact ha
  · obtain ⟨hs, hl, hr⟩ := h2 n hn
    rw [Bool.and_eq_true, arraysLaidLight_with, if_pos hs, with_own_ready S D Z G x [] _ hs]
    exact ⟨hl, hr⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.arraysLaidLight_lays
#print axioms ProofFile.Honest.K2.Law.arraysLaidLight_with
#print axioms ProofFile.Honest.K2.Law.publicOk_with
