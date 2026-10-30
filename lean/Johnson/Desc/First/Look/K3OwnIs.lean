-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3OwnIs.lean: WHAT THE BLOCK AT A LOOKUP'S ADDRESS IS: `K3.theOwn` and
`K3.theWhole` (Johnson/Desc/First/Look/K3Own.lean, K3Whole.lean), where they give a block, opened
into the seated maker `K3.Law.blockVia` (Johnson/Desc/First/Look/Via/Via.lean) at named arguments;
and WHICH RUNS OF CLAIMS the block of `K3.theStated` (K3Stated.lean) states, by name and in order.
Small lemmas with their proofs; without Mathlib.

Why. A law of the kind is proved of `blockVia seat piece laid before p guests` at letters (or of
`K3.block`, and carried). What sits in a chain is the value of `theWhole` | `theStated` at an
address. These lemmas say which letters: so that a law can name the constant of the seated text that
it speaks of.

Main names:
  `seatOfLookupOnDigitsOrCalls claim digits`: the kind's seat at the lookup on the digits, or on the calls.
  `theOwn_is`: where `theOwn … a = some b`: there are the link's number i, `digits`, the place p,
    the list `sent` and the count `laid`, each the value of its own public function at (i, digits),
    and b has the rounds, the `decide` and the name of `Law.blockVia (seatOfLookupOnDigitsOrCalls claim digits) a.piece
    laid sent p []`; and where b's test on the plan says yes, so does that block's.
  `theWhole_is`: where `theWhole … a = some B`: B is `theOwn`'s block b, or b with the step of
    `quietAt` behind it (`Block.andThen`, `roundlessBlock`).
  `theStated_is`: `theStated`'s block has the rounds, the `decide`, the name and the test on the
    plan of `theWhole`'s.
  `theOwn_names`, `theWhole_names`: with the runs on: "objects", "guests", in that order, and no run
    behind the batching.
  `statesPlanes readers X a`: a Bool: the calls' piece of a link at which `readers` gives something.
  `theStated_names`: "objects", "guests", and behind them "planes" JUST WHERE `statesPlanes` says
    so: both ways; no run behind the batching.
  `theStated_planes`: which run stands under "planes": `planesRun` at the calls' seat, the place's
    number and the caller's readers.

Limits: b's test on the plan has one conjunct more than the kind's (the padding key's), and with
`runs := false` its lists of claims are struck: neither is a matter of rounds or `decide`. Nothing
on soundness; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Stated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Aff)

/-- The kind's seat at a lookup. -/
def seatOfLookupOnDigitsOrCalls {Cl : Type} (claim : Aff → Cl) (digits : Bool) : Seat First.S Cl :=
  if digits then seatDigits claim else seatCalls claim

/-- **The block at an address is the kind's block, at these arguments.** -/
theorem theOwn_is {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (b : Block First.S Cl)
    (h : theOwn claim runs X codes shape a = some b) :
    ∃ i digits p sent laid, a.link = some i ∧ a.piece = pieceAt X i digits ∧
      First.Look.placeAt X i digits = some p ∧
      First.Look.beforeAt codes shape i digits = some sent ∧
      First.Look.laidAt X i digits = some laid ∧
      b.rounds = (Law.blockVia (seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent p []).rounds ∧
      b.decide = (Law.blockVia (seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent p []).decide ∧
      b.name = p.name ∧
      (b.planOk = true →
        (Law.blockVia (seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent p []).planOk = true) := by
  unfold theOwn at h
  split at h
  · cases h
  · obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, -, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · rename_i hp
      obtain ⟨p, hpl, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, hs, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, hl, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, -, h⟩ := Option.map_eq_some_iff.1 h
      refine ⟨i, digits, p, sent, laid, hi, by simpa using hp, hpl, hs, hl, ?_, ?_, ?_, ?_⟩
      · subst h
        cases runs <;> rfl
      · subst h
        cases runs <;> rfl
      · subst h
        cases runs <;> rfl
      · subst h
        intro hb
        cases runs <;> exact ((Bool.and_eq_true _ _).mp hb).1

/-- **The whole block at an address**: `theOwn`'s, or that with `quietAt`'s step behind it. -/
theorem theWhole_is {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block First.S Cl)
    (h : theWhole claim runs X codes shape a = some B) :
    ∃ b, theOwn claim runs X codes shape a = some b ∧
      (((a.link.bind fun i => quietAt X i (a.piece == pieceAt X i true)) = none ∧ B = b) ∨
        ∃ f, (a.link.bind fun i => quietAt X i (a.piece == pieceAt X i true)) = some f ∧
          B = b.andThen b.name (roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece f)) := by
  unfold theWhole at h
  obtain ⟨b, hb, h⟩ := Option.map_eq_some_iff.1 h
  refine ⟨b, hb, ?_⟩
  split at h
  · rename_i f hf
    exact Or.inr ⟨f, hf, h.symm⟩
  · rename_i hf
    exact Or.inl ⟨hf, h.symm⟩

/-- **The stated block has the whole block's rounds and `decide`**: "planes" is a list of claims
more. -/
theorem theStated_is {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers First.S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block First.S Cl) (h : theStated claim readers X codes shape a = some B) :
    ∃ B₁, theWhole claim true X codes shape a = some B₁ ∧ B.rounds = B₁.rounds ∧
      B.decide = B₁.decide ∧ B.name = B₁.name ∧ B.planOk = B₁.planOk := by
  unfold theStated at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨b, hb, ?_⟩
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · split at h
    · cases h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · split at h
      · cases h
        exact ⟨rfl, rfl, rfl, rfl⟩
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- With its runs on, the block at an address states "objects" and "guests", in that order. -/
theorem theOwn_names {Cl : Type} (claim : Aff → Cl) (X : Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (b : Block First.S Cl)
    (h : theOwn claim true X codes shape a = some b) :
    b.claims.map (·.1) = ["objects", "guests"] ∧ b.after = [] := by
  unfold theOwn at h
  split at h
  · cases h
  · obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, -, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, -, h⟩ := Option.map_eq_some_iff.1 h
      subst h
      exact ⟨rfl, rfl⟩

/-- So does the whole block: the step behind it states nothing. -/
theorem theWhole_names {Cl : Type} (claim : Aff → Cl) (X : Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block First.S Cl)
    (h : theWhole claim true X codes shape a = some B) :
    B.claims.map (·.1) = ["objects", "guests"] ∧ B.after = [] := by
  obtain ⟨b, hb, hB⟩ := theWhole_is claim true X codes shape a B h
  obtain ⟨h1, h2⟩ := theOwn_names claim X codes shape a b hb
  rcases hB with ⟨-, rfl⟩ | ⟨f, -, rfl⟩
  · exact ⟨h1, h2⟩
  · have e1 : (b.andThen b.name
        (roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece f)).claims = b.claims ++ [] := rfl
    have e2 : (b.andThen b.name
        (roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece f)).after = b.after ++ [] := rfl
    rw [e1, e2, List.append_nil, List.append_nil]
    exact ⟨h1, h2⟩

/-- Whether "planes" is stated at an address: the calls' piece of a link at which `readers` gives
the calling kind's readers. -/
def statesPlanes (readers : Nat → Option (Readers First.S)) (X : Model.Verify.Public) (a : Place) :
    Bool :=
  match a.link with
  | none => false
  | some i => a.piece == pieceAt X i false && (readers i).isSome

/-- **Which runs the stated block states**, by name and in order: both ways. -/
theorem theStated_names {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers First.S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block First.S Cl) (h : theStated claim readers X codes shape a = some B) :
    B.after = [] ∧
      B.claims.map (·.1) =
        ["objects", "guests"] ++ (if statesPlanes readers X a then ["planes"] else []) := by
  unfold theStated at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨h1, h2⟩ := theWhole_names claim X codes shape a b hb
  split at h
  · rename_i hl
    cases h
    refine ⟨h2, ?_⟩
    simp [statesPlanes, hl, h1]
  · rename_i i hi
    split at h
    · rename_i hp
      cases h
      have hpe : (a.piece == pieceAt X i false) = false := by simpa using hp
      refine ⟨h2, ?_⟩
      simp [statesPlanes, hi, hpe, h1]
    · rename_i hp
      have hpe : (a.piece == pieceAt X i false) = true := by simpa using hp
      split at h
      · rename_i hr
        cases h
        refine ⟨h2, ?_⟩
        simp [statesPlanes, hi, hr, h1]
      · rename_i r hr
        obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        have e : (withCaller (seatCalls claim) p r b).claims =
            b.claims ++ [("planes", planesRun (seatCalls claim) p.lm r)] := rfl
        refine ⟨h2, ?_⟩
        rw [e, List.map_append, h1]
        simp [statesPlanes, hi, hpe, hr]

/-- **Which run stands under "planes"**: the kind's own `planesRun` at the calls' seat, the place's
number of the planes' rows and the caller's readers. -/
theorem theStated_planes {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers First.S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block First.S Cl) (h : theStated claim readers X codes shape a = some B) (i : Nat)
    (r : Readers First.S) (hi : a.link = some i) (hpc : a.piece = pieceAt X i false)
    (hr : readers i = some r) :
    ∃ p b, First.Look.placeAt X i false = some p ∧ theWhole claim true X codes shape a = some b ∧
      B.claims = b.claims ++ [("planes", planesRun (seatCalls claim) p.lm r)] := by
  unfold theStated at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  rw [hi] at h
  have hpe : (a.piece != pieceAt X i false) = false := by simp [hpc]
  simp only [hpe, hr] at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨p, b, hp, hb, rfl⟩

#print axioms theStated_is
#print axioms theOwn_names
#print axioms theWhole_names
#print axioms theStated_names
#print axioms theStated_planes
#print axioms theOwn_is
#print axioms theWhole_is

end VerifiableInference.Desc.K3
