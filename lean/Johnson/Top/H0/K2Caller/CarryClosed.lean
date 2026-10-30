-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/CarryClosed.lean: the code switch: «carry», THE ITEM OF
THE TABLE OF JOINTS THAT THE SWITCH CLOSES, AS A CLOSED TERM OVER THE PUBLIC PARAMETERS AND THE
LAYOUT FILE: no letter is left.

WHY THE WAY IN. The item is open not only at the border
in front of the switch that spends it: it is asked at every border from behind the closing's second
block (its maker) on. A SENTENCE THAT READS the walk's copy of the state of the calls
(s.check), which is stale inside a link, IS FALSE IN FRONT OF «cleared». ONE THAT
takes the live copy back AS IT IS: between the closing's second block and «the segment is
shut» that copy still says «a link is under way», and the head's and the finish's own first steps
read that flag and refuse: IT IS FALSE THERE AT THE TWO ITEMS THAT ARE SPENT AT THE HEAD
AND AT THE FINISH. A run on a stored small set has both: the first way
in goes through at 12 of the 20 borders at which the table has the item open, the second at 18. THE
CURE: the way in.
  rest         the state between the links that a state inside a link will be left as: the live copy
               of the state of the calls taken back WITH ITS FLAG «a link is under way» LAID FALSE
               (what the shutting does), «between» (what «cleared» does); outside a link: the state
               itself
  doorZ        THE WAY IN, BY THE SORT OF THE PLACE AT WHICH THE ITEM IS SPENT (the three lines of
               K2's text): at a link: rest · at the head: a state that stands in
               the head's front, unopened: itself; opened: nothing; else the head's own first step
               K2.headFrontQ at rest · at the finish: K2.finishFrontQ at rest
  carryAtZ     CarryK2.lean's carryK2 at: ProofFile.rowAtK2 | ProofFile.pAtK2 (ProofFile/CarryAt.lean) · doorZ ·
               K2Hears/OrcStrs.lean's orcY at ProofFile.allAt | ProofFile.keyAt · SmpK2.lean's smpK2
               carryAtZ_iff what it says at a segment
  rest_out     outside a link rest turns nothing
  doorZ_at_switch  AT THE BORDER AT WHICH THE ITEM IS SPENT THE WAY IN IS THE FIRST VERSION's
               (ProofFile.doorAtK2): outside a link, and at the head where the state stands in the head's
               front
WHAT THE WAY IN, THE FRONT's MAKER AND THE READING OF THE COLUMNS READ OF A STATE, TO THE END, BY
READING: where it stands («here») · the live copy's flag and its frame · the statement · the mark ·
the book · the roots. WHAT THE STEPS OF THE SPAN TURN OF THESE: the shutting: the flag · «cleared»:
«here», the walk's copy, and, where it leaves a row, one message's ledger in the statement · «laid»:
nothing · the step that enters the head: what the way in itself does in front of it.
LIMITS. DEFINITIONS, AN UNFOLDING AND ONE LAW ON THE WAY IN. THAT THE SENTENCE HOLDS AT AN EARLIER
BORDER OF THE SPAN WHEREVER IT HOLDS AT A LATER ONE IS NOT SHOWN HERE: it is each sub-protocol's own
tie's to show. K2.headFrontQ takes the smallness test's plan: here the blank one {}:
CarryReads.lean's doorZ_head: it costs nothing. THE SENTENCE ITSELF HAS BEEN EVALUATED NOWHERE.
WHETHER IT CAN BE MET IS NOT SHOWN. It reads nothing of the witness and nothing of the statement's
public part. The held samples' seeds are chosen, not computed. No soundness is claimed.

-/
import Johnson.Top.H0.K2Caller.SmpK2
import Johnson.Top.H0.K2Hears.OrcStrs
import Johnson.Desc.ProofFile.CarryAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Strs)

/-- **The state between the links that a state inside a link will be left as**, as to the state of
the calls and where the chain stands. -/
def rest (s : VerifiableInference.Desc.First.S) : VerifiableInference.Desc.First.S :=
  if s.inLink then { s with check := { s.live with inLink := false }, here := .between } else s

/-- **The way in, at every border of the item's span.** -/
def doorZ (Z : ProofFile.Pub) (m : ℕ) (s : VerifiableInference.Desc.First.S) :
    Option VerifiableInference.Desc.First.S :=
  match (ProofFile.pAtK2 Z m).stands with
  | .link => some (rest s)
  | .head =>
    match s.here with
    | .head a => if a.opened then none else some s
    | _ => (K2.headFrontQ {} (rest s)).toOption
  | .finish => (K2.finishFrontQ (rest s)).toOption

/-- **«carry», closed.** Z: the public parameters. lay: the layout file. -/
def carryAtZ {P W : Type} (Z : ProofFile.Pub) (lay : ByteArray) :
    ℕ → P × VerifiableInference.Desc.First.S → Strs → W → Prop :=
  carryK2 (ProofFile.rowAtK2 Z.pol lay Z.KL) (ProofFile.pAtK2 Z) (doorZ Z)
    (K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z)) smpK2

/-- What it says, at a segment. -/
theorem carryAtZ_iff {P W : Type} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ)
    (a : P × VerifiableInference.Desc.First.S) (y : Strs) (w : W) :
    carryAtZ Z lay m a y w ↔ ∃ r t, ProofFile.rowAtK2 Z.pol lay Z.KL m = some r ∧
      doorZ Z m a.2 = some t ∧ ∃ h : r.ok = true,
        carryRow r (r.ok_says h) (ProofFile.pAtK2 Z m) (K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z))
          (smpK2 r (r.ok_says h)) t y := by
  unfold carryAtZ carryK2
  cases h1 : ProofFile.rowAtK2 Z.pol lay Z.KL m with
  | none => simp
  | some r =>
    cases h2 : doorZ Z m a.2 with
    | none => simp
    | some t => simp

/-- Outside a link nothing is turned. -/
theorem rest_out (s : VerifiableInference.Desc.First.S) (h : s.inLink = false) : rest s = s := by
  unfold rest
  rw [h]
  rfl

/-- **At the border at which the item is spent the way in is ProofFile.doorAtK2**
(Johnson/Desc/ProofFile/CarryAt.lean). -/
theorem doorZ_at_switch (Z : ProofFile.Pub) (m : ℕ) (s : VerifiableInference.Desc.First.S)
    (h : s.inLink = false)
    (hh : (ProofFile.pAtK2 Z m).stands = .head → ∃ a, s.here = .head a) :
    doorZ Z m s = ProofFile.doorAtK2 Z m s := by
  unfold doorZ ProofFile.doorAtK2
  rw [rest_out s h]
  cases hs : (ProofFile.pAtK2 Z m).stands with
  | link => rfl
  | finish => rfl
  | head =>
    obtain ⟨a, ha⟩ := hh hs
    have ho : a.opened = false := by
      unfold VerifiableInference.Desc.First.S.inLink VerifiableInference.Desc.First.S.fork? at h
      rw [ha] at h
      cases hb : a.opened with
      | false => rfl
      | true => simp [hb] at h
    simp only [ha, ho]
    rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.carryAtZ_iff
#print axioms VerifiableInference.Desc.First.K2Caller.doorZ_at_switch
