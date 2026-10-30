-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/GoesOn.lean: from the fields of a meaning to the items of the library's
table, FORWARD: if each field's sentence goes on over a relation between two statements (from the
one in front to the one behind), so does each item that reads no segment's part. Rules over
letters: the meaning, the plan's numbers and the relation are letters; no block of any description
occurs, and no frame of a prover.

Why. The library has this backward (Johnson/Desc/Sound/ItemsRide.lean: `GoesBack`, `FieldsBack`,
`holds_back`): there a verifier's yes carries what an item says from behind a block to in front of
it. An honest run wants the other direction: an item that is open in front of a block, and that the
block's row neither shuts nor owes, says behind the block what it said in front. There are many
such pairs of a block and an item, and few fields: whoever fills a field owes one sentence a field.

How. "Forward over rel" IS "backward over rel turned round" (`goesOn_iff_back`): so the step from
the fields to the items is the library's own `holds_back`, called at the turned relation.

What is said. rel a y b y': the statement in front (a, y) and the one behind (b, y') are so related.
  `GoesOn rel φ`: φ at the statement in front gives φ at the statement behind.
  `goesOn_iff_back`: it is the library's `GoesBack` at the relation turned round.
  `goesOn_of_reads`: a sentence that reads the statement through a function r alone goes on over
    every rel that keeps r. `goesOn_witness`: a sentence that reads the witness alone goes on over
    every rel. `GoesOn.mono`, `FieldsOn.mono`: over a narrower rel too.
  `FieldsOn Mg own low rel`: each of the eight fields that the twelve arms without a part read goes
    on over rel: `constr m p` where `own m p = false`; `pin j t` where `low j`; and rel keeps "no
    mark".
  `holds_on`: under `FieldsOn`, at an item with `Item.part = none` which is no `constr m p` with
    `own m p = true`, and with the library's `lowItem`: `GoesOn rel (i.holds N Mg)`.
  `fieldsOn_blind`: THE PREMISE CAN BE MET: at the library's made-up meaning whose sentences read
    the witness alone, over "the two marks are one". It says nothing of any real meaning.
  `not_fieldsOn_all`: IT CAN FAIL: over the relation that holds of all statements no meaning has
    it: "no mark" does not go on.

The two letters own and low are the library's: own m p: nothing is said of this part of segment m's
relation; low j: tree j is one of which rel speaks.

Limits. (1) That any meaning has `FieldsOn` at any relation is not shown here: the premise is owed
by whoever fills the fields. (2) That a step of any block gives any relation is not shown. (3) At
rel := False everything here holds and says nothing. (4) The seven arms with a part (forms, formsT,
worth, wo, tie, totalB, total) are not touched.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.Sound.ItemsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Item Part Meaning Numbers)
open VerifiableInference.Desc.Sound (GoesBack FieldsBack holds_back lowItem notOwn blind)

section
variable {P W : Type}

/-- A relation between two statements. -/
abbrev Rel (P : Type) : Type :=
  P × VerifiableInference.Desc.First.S → Strs → P × VerifiableInference.Desc.First.S → Strs → Prop

/-- The relation turned round. -/
def Rel.turned (rel : Rel P) : Rel P := fun a y b y' => rel b y' a y

/-- φ at the statement in front gives φ at the statement behind, wherever the two are related. -/
def GoesOn (rel : Rel P) (φ : P × VerifiableInference.Desc.First.S → Strs → W → Prop) : Prop :=
  ∀ a y b y' w, rel a y b y' → φ a y w → φ b y' w

/-- **Forward over rel is backward over rel turned round.** No premise. -/
theorem goesOn_iff_back (rel : Rel P)
    (φ : P × VerifiableInference.Desc.First.S → Strs → W → Prop) :
    GoesOn rel φ ↔ GoesBack rel.turned φ :=
  ⟨fun h a y b y' w hr hb => h b y' a y w hr hb, fun h a y b y' w hr ha => h b y' a y w hr ha⟩

/-- Over a narrower relation too. Conditional: hr: rel' is narrower than rel. -/
theorem GoesOn.mono {rel rel' : Rel P}
    {φ : P × VerifiableInference.Desc.First.S → Strs → W → Prop} (h : GoesOn rel φ)
    (hr : ∀ a y b y', rel' a y b y' → rel a y b y') : GoesOn rel' φ :=
  fun a y b y' w h' => h a y b y' w (hr a y b y' h')

/-- **A sentence that reads the statement through r alone goes on over every rel that keeps r.**
Conditional: hr: rel keeps r. -/
theorem goesOn_of_reads {X : Type} (r : P × VerifiableInference.Desc.First.S → Strs → X)
    (ψ : X → W → Prop) (rel : Rel P) (hr : ∀ a y b y', rel a y b y' → r a y = r b y') :
    GoesOn rel (fun a y w => ψ (r a y) w) := fun a y b y' w h ha => by
  show ψ (r b y') w
  rw [← hr a y b y' h]
  exact ha

/-- A sentence that reads the witness alone goes on over every rel. No premise. -/
theorem goesOn_witness (ψ : W → Prop) (rel : Rel P) : GoesOn rel (fun _ _ w => ψ w) :=
  fun _ _ _ _ _ _ h => h

/-- **Each field that an item without a part reads goes on over rel.** A premise's form: whoever
fills the fields is meant to show it. -/
structure FieldsOn (Mg : Meaning P W) (own : Nat → Part → Bool) (low : Nat → Prop)
    (rel : Rel P) : Prop where
  constr : ∀ m p, own m p = false → GoesOn rel (Mg.constr m p)
  pin : ∀ j t, low j → GoesOn rel (Mg.pin j t)
  pinW : GoesOn rel Mg.pinW
  row : ∀ m c, GoesOn rel (Mg.row m c)
  carry : ∀ m, GoesOn rel (Mg.carry m)
  pile : GoesOn rel Mg.pile
  pileOne : GoesOn rel Mg.pileOne
  wrow : GoesOn rel Mg.wrow
  /-- rel keeps "no mark" -/
  mark : ∀ a y b y', rel a y b y' → a.2.failed = none → b.2.failed = none

/-- It is the library's structure at the relation turned round. -/
theorem FieldsOn.back {Mg : Meaning P W} {own : Nat → Part → Bool} {low : Nat → Prop}
    {rel : Rel P} (H : FieldsOn Mg own low rel) : FieldsBack Mg own low rel.turned where
  constr m p h := (goesOn_iff_back rel _).1 (H.constr m p h)
  pin j t h := (goesOn_iff_back rel _).1 (H.pin j t h)
  pinW := (goesOn_iff_back rel _).1 H.pinW
  row m c := (goesOn_iff_back rel _).1 (H.row m c)
  carry m := (goesOn_iff_back rel _).1 (H.carry m)
  pile := (goesOn_iff_back rel _).1 H.pile
  pileOne := (goesOn_iff_back rel _).1 H.pileOne
  wrow := (goesOn_iff_back rel _).1 H.wrow
  mark a y b y' h := H.mark b y' a y h

/-- Over a narrower relation too. Conditional: hr: rel' is narrower than rel. -/
theorem FieldsOn.mono {Mg : Meaning P W} {own : Nat → Part → Bool} {low : Nat → Prop}
    {rel rel' : Rel P} (H : FieldsOn Mg own low rel)
    (hr : ∀ a y b y', rel' a y b y' → rel a y b y') : FieldsOn Mg own low rel' where
  constr m p h := (H.constr m p h).mono hr
  pin j t h := (H.pin j t h).mono hr
  pinW := H.pinW.mono hr
  row m c := (H.row m c).mono hr
  carry m := (H.carry m).mono hr
  pile := H.pile.mono hr
  pileOne := H.pileOne.mono hr
  wrow := H.wrow.mono hr
  mark a y b y' h := H.mark a y b y' (hr a y b y' h)

/-- **From the fields to the items, forward.** Conditional: H; hp: the item reads no segment's
part; ho: it is no part of a segment's relation that own names; hl: every tree that its pins name
has low. -/
theorem holds_on (N : Numbers) (Mg : Meaning P W) (own : Nat → Part → Bool) (low : Nat → Prop)
    (rel : Rel P) (H : FieldsOn Mg own low rel) (i : Item) (hp : i.part = none)
    (ho : notOwn own i) (hl : lowItem N low i) : GoesOn rel (i.holds N Mg) :=
  (goesOn_iff_back rel _).2 (holds_back N Mg own low rel.turned H.back i hp ho hl)

/-- **The premise can be met**: at the library's made-up meaning, over "the two marks are one". -/
theorem fieldsOn_blind (ψ : W → Prop) (own : Nat → Part → Bool) (low : Nat → Prop) :
    FieldsOn (blind (P := P) ψ) own low (fun a _ b _ => a.2.failed = b.2.failed) where
  constr _ _ _ := fun _ _ _ _ _ _ h => h
  pin _ _ _ := fun _ _ _ _ _ _ h => h
  pinW := fun _ _ _ _ _ _ h => h
  row _ _ := fun _ _ _ _ _ _ h => h
  carry _ := fun _ _ _ _ _ _ h => h
  pile := fun _ _ _ _ _ _ h => h
  pileOne := fun _ _ _ _ _ _ h => h
  wrow := fun _ _ _ _ _ _ h => h
  mark _ _ _ _ h ha := h.symm.trans ha

/-- **It can fail**: over the relation that holds of all statements no meaning has it. -/
theorem not_fieldsOn_all (Mg : Meaning P W) (own : Nat → Part → Bool) (low : Nat → Prop)
    (z : P) (s : VerifiableInference.Desc.First.S) (y : Strs) :
    ¬ FieldsOn Mg own low (fun _ _ _ _ => True) := fun H => by
  have := H.mark (z, { s with failed := none }) y (z, { s with failed := some "x" }) y trivial rfl
  cases this

end

end H2K5.Honest

#print axioms H2K5.Honest.goesOn_iff_back
#print axioms H2K5.Honest.GoesOn.mono
#print axioms H2K5.Honest.goesOn_of_reads
#print axioms H2K5.Honest.goesOn_witness
#print axioms H2K5.Honest.FieldsOn.back
#print axioms H2K5.Honest.FieldsOn.mono
#print axioms H2K5.Honest.holds_on
#print axioms H2K5.Honest.fieldsOn_blind
#print axioms H2K5.Honest.not_fieldsOn_all
