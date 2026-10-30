-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PinAsksOf.lean: TWO OF THE PREMISES OF `LettersAsk` (LettersWhole.lean)
PAID: «every seat of own is a tenant of one of the segment's three moments», at own := the plan's
group of the segment, outright; and the fence of `PinAsks` (PinsBack.lean: the segment's tenants sit
in commitment trees below the piece's first tree) from the table's own test on its numbers
(`fenceFit`), a Bool on the table and the written list («the segment's three pins are open in front
of the batching, of the frame's sub-protocol behind it and of the one equation») and «the plan's
count of trees at the place is no more than the piece's first tree». Definitions, theorems,
evaluations.

What is said.
  `own_group`: **the first, by the definition of a segment's group.** `mem_sampled`: a tenant of an
    open pin is among the sampled tenants at the border. `pinsAt`, `pinsFit links ps`: the Bool;
    `pins_at`: the fact at a place; `pinsFit_full`: the kernel's yes at the full list;
    `pinsAsks_full`: it asks something at 75 numbers; `pinsFit_bent`: a negative test: the second
    segment's one equation and the sub-protocol behind it, which closes the pins, changed over: no.
    `pinFence_of`: **the fence.** `pinAsks_of`: `PinAsks` from it and «the OOD samples' reader
    answers alike at the two states».

Limits. `fenceFit`'s yes at the numbers that are made of a plan is the table's files' to show;
the piece's first tree against the plan's count is the maker's; the samples' reader is a parameter.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PinsBack
import Johnson.Desc.First.Link.Law.FenceAt
import Johnson.Desc.First.Link.Law.LinkPlacesFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers pinsOf flatPlacesOf start openSets sampledIn
  fenceFit)

/-- **Every seat of a segment's group is a tenant of one of its three moments.** -/
theorem own_group (Nm : Numbers) (m : ℕ) : ∀ x ∈ Nm.group m, ∃ t < 3, x ∈ Nm.sent m t := by
  intro x hx
  unfold Numbers.group at hx
  rcases List.mem_append.1 hx with h | h
  · rcases List.mem_append.1 h with h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
  · exact ⟨2, by omega, h⟩

/-- A tenant of an open pin is among the sampled tenants at the border. -/
theorem mem_sampled (Nm : Numbers) (O : List Item) (m t : ℕ) (h : Item.pin m t ∈ O) (x : ℕ × ℕ)
    (hx : x ∈ Nm.sent m t) : x ∈ sampledIn Nm O :=
  List.mem_flatMap.2 ⟨.pin m t, h, hx⟩

/-- **The test at number k of the list**: in front of the three the segment's pins are open. -/
def pinsAt (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m =>
      if p.piece == hearN links m + 1 || p.piece == hearN links m + 2 ||
          p.piece == hearN links m + 3 then
        (pinsOf m).all ((openSets links ps (start links))[k]?.getD []).contains
      else true
    | none => true
  | none => true

/-- **The test along the list.** -/
def pinsFit (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all (pinsAt links ps)

/-- **THE FACT AT A PLACE.** -/
theorem pins_at (links : List ModelPart) (ps : List Place) (h : pinsFit links ps = true) (k m i : ℕ)
    (p : Place) (hp : ps[k]? = some p) (hl : p.link = some m) (hpc : p.piece = hearN links m + i)
    (hi : i = 1 ∨ i = 2 ∨ i = 3) :
    ∀ t < 3, Item.pin m t ∈ (openSets links ps (start links))[k]?.getD [] := by
  unfold pinsFit at h
  rw [List.all_eq_true] at h
  have h0 := h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  unfold pinsAt at h0
  rw [hp] at h0
  have h1 : (pinsOf m).all ((openSets links ps (start links))[k]?.getD []).contains = true := by
    rcases hi with rfl | rfl | rfl <;> simpa [hl, hpc] using h0
  intro t ht
  have h2 := List.all_eq_true.1 h1 (.pin m t) (by
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases ht' with rfl | rfl | rfl <;> simp [pinsOf])
  simpa using h2

set_option maxRecDepth 1000000 in
/-- **THE YES AT THE FULL LIST.** -/
theorem pinsFit_full : pinsFit fullList (flatPlacesOf fullList true) = true := by decide +kernel

/-- The place at number k is one of the three. -/
def pinsAsks (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m => p.piece == hearN links m + 1 || p.piece == hearN links m + 2 ||
        p.piece == hearN links m + 3
    | none => false
  | none => false

set_option maxRecDepth 1000000 in
/-- **THE TEST ASKS SOMETHING AT 75 NUMBERS OF THE FULL LIST.** -/
theorem pinsAsks_full : ((List.range (flatPlacesOf fullList true).length).filter
    (pinsAsks fullList (flatPlacesOf fullList true))).length = 75 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A NEGATIVE TEST: THE SECOND SEGMENT's ONE EQUATION AND THE SUB-PROTOCOL BEHIND IT, WHICH
CLOSES THE PINS, CHANGED OVER.** -/
theorem pinsFit_bent : pinsFit fullList (swapAt (flatPlacesOf fullList true) 25) = false := by
  decide +kernel

/-- **THE FENCE.** -/
theorem pinFence_of (Nm : Numbers) (links : List ModelPart) (pl : List Place)
    (hf : fenceFit Nm links pl = true) (hp : pinsFit links pl = true) (k m i base : ℕ)
    (p : Place) (hk : pl[k]? = some p) (hl : p.link = some m) (hpc : p.piece = hearN links m + i)
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (hb : Nm.treesAt pl[k]? ≤ base) :
    ∀ t < 3, ∀ x ∈ Nm.sent m t, x.1 < base := fun t ht x hx =>
  fence_of_fit Nm links pl hf k base (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hk).1) hb x
    (mem_sampled Nm _ m t (pins_at links pl hp k m i p hk hl hpc hi t ht) x hx)

/-- PinAsks from it and «the OOD samples' reader answers alike». -/
theorem pinAsks_of {P : Type} (cs : OnBytes.Codes)
    (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (Nm : Numbers) (links : List ModelPart) (pl : List Place) (hf : fenceFit Nm links pl = true)
    (hp : pinsFit links pl = true) (z : P) (k m i base : ℕ) (p : Place) (hk : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + i) (hi : i = 1 ∨ i = 2 ∨ i = 3)
    (hb : Nm.treesAt pl[k]? ≤ base) (s s' : S) (hs : smp (z, s') = smp (z, s)) :
    PinAsks cs smp Nm z m base s s' :=
  ⟨pinFence_of Nm links pl hf hp k m i base p hk hl hpc hi hb, hs⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.own_group
#print axioms VerifiableInference.Desc.LinkJoin.pins_at
#print axioms VerifiableInference.Desc.LinkJoin.pinsFit_full
#print axioms VerifiableInference.Desc.LinkJoin.pinsAsks_full
#print axioms VerifiableInference.Desc.LinkJoin.pinsFit_bent
#print axioms VerifiableInference.Desc.LinkJoin.pinFence_of
#print axioms VerifiableInference.Desc.LinkJoin.pinAsks_of
