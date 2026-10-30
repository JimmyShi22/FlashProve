-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SeatKeeps.lean: OUR HALF OF THE PIN AT THE SEAT THAT SITS: what the
hearing's
seat seatSO (Att/SeatO.lean) keeps of the first chain's record: the law `lay` of `PinItem`
(Att/K05Seam.lean), for EVERY reading of the record that reads neither the count of rows owed, nor
the open attention segment's ledger, nor what its own rounds have heard.

Main names:
  `restO s`: the record with these three fields blanked: rowsOwed := none; in an open attention
    segment F := {} and heard5 := none.
  `seatSO_rest`: where seatSO.lay returns s' at s: restO s' = restO s.
  `ReadsRest rc`: the reading rc factors through restO: two records with one rest are read alike.
  `seatSO_keeps`: **so rc s' = rc s for every such reading.** `readsRest_of`: f ∘ restO is one.
  `rest_st`, `rest_book`, `rest_roots`, `rest_failed`, `rest_check`, `rest_out`, `rest_req`: the
    record's seven other fields are such readings; `attRest`, `rest_att`: so is the open segment
    without its ledger and heard5 (its L, tl, g, planes, scores, d, x, t, slotA, lookHeard).
  `PinItem.atSeatSO`: a PinItem at seatSO from a reading with ReadsRest: the law `lay` is paid; the
    laws `fixes` and `fenced` stay the filler's.
  `PinItem.ofDecSO`: the filler "the words decode to the world's part" (Att/K05PinDec.lean) at
  seatSO.

Premises: none for seatSO_keeps but ReadsRest.
Limits. Whether the samples that the meant item reads lie in the fields that are kept is a fact on
that item's text, which is not typed here: by the record's own docstrings the frame's twelve and the
state of the calls lie in `check`, which is kept. A reading that reads the ledger (the slots' public
kinds, what was shown) is NOT covered: the hearing turns the ledger.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LeavesTl
import Johnson.Desc.First.Att.K05PinDec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound (Frame)

/-- The open attention segment without its ledger and without what its own rounds have heard. -/
def attRest (a : First.AttOwn) : First.AttOwn := { a with F := {}, heard5 := none }

/-- The record without the count of rows owed, the open attention segment's ledger and heard5. -/
def restO (s : First.S) : First.S :=
  match s.here with
  | .att a => { s with rowsOwed := none, here := .att (attRest a) }
  | _ => { s with rowsOwed := none }

/-- **What the hearing's seat lays has the rest of what lay in front.** -/
theorem seatSO_rest {s s' : First.S} {h : Heard} {G : Fork} (hl : seatSO.lay s h G = some s') :
    restO s' = restO s := by
  obtain ⟨a, e1, rfl⟩ := seatSO_lay hl
  unfold restO
  rw [e1]
  rfl

/-- The reading factors through the rest. -/
def ReadsRest {Rc : Type} (rc : First.S → Rc) : Prop := ∀ s t, restO s = restO t → rc s = rc t

/-- **The seat keeps every such reading.** -/
theorem seatSO_keeps {Rc : Type} (rc : First.S → Rc) (hrc : ReadsRest rc) (s : First.S) (h : Heard)
    (G : Fork) (s' : First.S) (hl : seatSO.lay s h G = some s') : rc s' = rc s :=
  hrc s' s (seatSO_rest hl)

theorem readsRest_of {Rc : Type} (f : First.S → Rc) : ReadsRest fun s => f (restO s) :=
  fun _ _ e => congrArg f e

theorem readsRest_field {Rc : Type} (f : First.S → Rc) (hf : ∀ s, f (restO s) = f s) :
    ReadsRest f := fun s t e => by rw [← hf s, ← hf t, e]

theorem rest_st : ReadsRest (·.st) := readsRest_field _ fun s => by
  unfold restO; split <;> rfl
theorem rest_book : ReadsRest (·.book) := readsRest_field _ fun s => by
  unfold restO; split <;> rfl
theorem rest_roots : ReadsRest (·.roots) := readsRest_field _ fun s => by
  unfold restO; split <;> rfl
theorem rest_failed : ReadsRest (·.failed) := readsRest_field _ fun s => by
  unfold restO; split <;> rfl
theorem rest_check : ReadsRest (·.check) := readsRest_field _ fun s => by
  unfold restO; split <;> rfl
theorem rest_out : ReadsRest (·.out) := readsRest_field _ fun s => by
  unfold restO; split <;> rfl
theorem rest_req : ReadsRest (·.req) := readsRest_field _ fun s => by
  unfold restO; split <;> rfl

/-- The open segment, without its ledger and heard5. -/
theorem rest_att : ReadsRest fun s => match s.here with
    | .att a => some (attRest a)
    | _ => none := readsRest_field _ fun s => by
  unfold restO
  cases h : s.here <;> rfl

section
variable {W Mg : Type} {F : Frame}

/-- **A PinItem at the seat that sits**: the law `lay` is paid. -/
def PinItem.atSeatSO (base : ℕ) {Rc : Type} (rc : First.S → Rc) (hrc : ReadsRest rc)
    (holds : Rc → F.E.Str → W → Prop) (part : W → Mg)
    (fixes : ∀ r y w w', holds r y w → holds r y w' → part w = part w')
    (fenced : ∀ r y y' w, SameBelow F base y y' → holds r y' w → holds r y w) :
    PinItem F seatSO base W Mg :=
  ⟨Rc, rc, holds, part, fixes, seatSO_keeps rc hrc, fenced⟩

/-- The filler "the words decode to the world's part", at the seat that sits. -/
def PinItem.ofDecSO (base : ℕ) {Rc Wd : Type} (rc : First.S → Rc) (hrc : ReadsRest rc)
    (words : F.E.Str → Wd) (hwords : ∀ y y', SameBelow F base y y' → words y' = words y)
    (dec : Rc → Wd → Option Mg) (side : Rc → Wd → Prop) (part : W → Mg) :
    PinItem F seatSO base W Mg :=
  PinItem.ofDec seatSO base rc (seatSO_keeps rc hrc) words hwords dec side part

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seatSO_rest
#print axioms VerifiableInference.Desc.First.Att.P.seatSO_keeps
#print axioms VerifiableInference.Desc.First.Att.P.rest_check
#print axioms VerifiableInference.Desc.First.Att.P.rest_att
