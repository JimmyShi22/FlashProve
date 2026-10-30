-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/ItemsRide.lean: from the fields of a meaning to the items of the table of joints:
if each field's sentence goes back over a relation between two statements, so does each item that
reads no segment's part. One structure of Prop, four definitions, eight theorems. Rules over
letters: the meaning, the plan's numbers and the relation are letters; no block of any description
occurs.

Why. An item that is open in front of a block, and that the block's row neither closes nor reads,
rides past the block: the tie asks that what it says of the statement behind it says of the
statement in front (`Piece.Frames`, Johnson/Desc/Sound/Spine.lean). There are many such pairs of a
block and an item, and few fields: `Item.holds` (Johnson/Desc/First/Borders.lean) reads one field of
the meaning at each of its nineteen arms. Twelve arms have `Item.part = none`. So whoever fills a
field owes one sentence a field, not one an item.

What is said. rel a y b y': the statement in front (a, y) and the one behind (b, y') are so related.
  `GoesBack rel φ`: φ at the statement behind gives φ at the statement in front.
  `goesBack_of_reads`: a sentence that reads the statement through a function r alone goes back over
    every rel that keeps r. `GoesBack.mono`, `FieldsBack.mono`: over a narrower rel too.
  `FieldsBack Mg own low rel`: each of the eight fields that these twelve arms read goes back over
    rel: `constr m p` where `own m p = false`; `pin j t` where `low j`; and rel keeps "no mark".
  `lowItem N low i`: every tree that the item's pins name has `low`.
  `holds_back`: under `FieldsBack`, at an item with `Item.part = none` which is no `constr m p`
    with `own m p = true`, and with `lowItem`: `GoesBack rel (i.holds N Mg)`.
  `meansQ_back`: the same for `meansQ` (Johnson/Desc/Sound/BordersQ.lean).
  `frames_of_fields`: at a piece whose yes gives rel inside the two promises, and whose extractor
    these items' sentences bear: `Piece.Frames` is owed for the other items alone.
  `blind ψ`, `fieldsBack_blind`: THE PREMISE CAN BE MET: at a made-up meaning whose sentences read
    the witness alone, over "the two marks are one". It says nothing of any real meaning.
  `not_fieldsBack_all`: IT CAN FAIL: over the relation that holds of all statements no meaning has
    it: "no mark" does not go back.

The two letters own and low. own m p: this part of segment m's relation is a sentence that may read
the verifier's state (by report: at the head's segment, and the part "every digit lies
in the digits' table"): nothing is said of it. low j: tree j is one of which rel speaks (a relation
that says "every tree below the piece's base is the same" says nothing of a tree at or above it).

Limits. (1) That any meaning has `FieldsBack` at any relation is not shown: the premise is owed by
whoever fills the fields. (2) That a yes of any block gives any relation is not shown. (3) At
rel := False everything here holds and says nothing. (4) The seven arms with a part (forms, formsT,
worth, wo, tie, totalB, total) are not touched. (5) It goes backward and speaks of items: the
promise's own clauses, which go forward, are not touched. No soundness of any verifier follows.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.PlainRoads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (Item Part RowClass Meaning Numbers)

section
variable {A P W Cl : Type} {C : CK} {Fr : Frame}

/-- φ at the statement behind gives φ at the statement in front, wherever the two are related. -/
def GoesBack (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (φ : P × First.S → Strs → W → Prop) : Prop :=
  ∀ a y b y' w, rel a y b y' → φ b y' w → φ a y w

/-- Over a narrower relation too. -/
theorem GoesBack.mono {rel rel' : P × First.S → Strs → P × First.S → Strs → Prop}
    {φ : P × First.S → Strs → W → Prop} (h : GoesBack rel φ)
    (hr : ∀ a y b y', rel' a y b y' → rel a y b y') : GoesBack rel' φ :=
  fun a y b y' w h' => h a y b y' w (hr a y b y' h')

/-- **A sentence that reads the statement through r alone goes back over every rel that keeps r.**
-/
theorem goesBack_of_reads {X : Type} (r : P × First.S → Strs → X) (ψ : X → W → Prop)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (hr : ∀ a y b y', rel a y b y' → r a y = r b y') :
    GoesBack rel (fun a y w => ψ (r a y) w) := fun a y b y' w h hb => by
  show ψ (r a y) w
  rw [hr a y b y' h]
  exact hb

/-- **Each field that an item without a part reads goes back over rel.** -/
structure FieldsBack (Mg : Meaning P W) (own : Nat → Part → Bool) (low : Nat → Prop)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop) : Prop where
  constr : ∀ m p, own m p = false → GoesBack rel (Mg.constr m p)
  pin : ∀ j t, low j → GoesBack rel (Mg.pin j t)
  pinW : GoesBack rel Mg.pinW
  row : ∀ m c, GoesBack rel (Mg.row m c)
  carry : ∀ m, GoesBack rel (Mg.carry m)
  pile : GoesBack rel Mg.pile
  pileOne : GoesBack rel Mg.pileOne
  wrow : GoesBack rel Mg.wrow
  /-- rel keeps "no mark" -/
  mark : ∀ a y b y', rel a y b y' → b.2.failed = none → a.2.failed = none

/-- Over a narrower relation too. -/
theorem FieldsBack.mono {Mg : Meaning P W} {own : Nat → Part → Bool} {low : Nat → Prop}
    {rel rel' : P × First.S → Strs → P × First.S → Strs → Prop} (H : FieldsBack Mg own low rel)
    (hr : ∀ a y b y', rel' a y b y' → rel a y b y') : FieldsBack Mg own low rel' where
  constr m p h := (H.constr m p h).mono hr
  pin j t h := (H.pin j t h).mono hr
  pinW := H.pinW.mono hr
  row m c := (H.row m c).mono hr
  carry m := (H.carry m).mono hr
  pile := H.pile.mono hr
  pileOne := H.pileOne.mono hr
  wrow := H.wrow.mono hr
  mark a y b y' h := H.mark a y b y' (hr a y b y' h)

/-- A made-up meaning: every sentence on the witness is ψ; every promise is kept. -/
def blind (ψ : W → Prop) : Meaning P W where
  pin := fun _ _ _ _ w => ψ w
  noColl := fun _ _ _ _ => True
  shown := fun _ _ _ => True
  held := fun _ _ _ => true
  pinW := fun _ _ w => ψ w
  decodes := fun _ _ => True
  inOrder := fun _ => true
  pub := fun _ _ => true
  constr := fun _ _ _ _ w => ψ w
  tie := fun _ _ _ w => ψ w
  forms := fun _ _ _ _ _ w => ψ w
  formsT := fun _ _ _ _ _ w => ψ w
  worth := fun _ _ _ _ _ w => ψ w
  wo := fun _ _ _ w => ψ w
  totalB := fun _ _ _ w => ψ w
  total := fun _ _ _ w => ψ w
  row := fun _ _ _ _ w => ψ w
  carry := fun _ _ _ w => ψ w
  pile := fun _ _ w => ψ w
  pileOne := fun _ _ w => ψ w
  wrow := fun _ _ w => ψ w

/-- **The premise can be met**: at the made-up meaning, over "the two marks are one". -/
theorem fieldsBack_blind (ψ : W → Prop) (own : Nat → Part → Bool) (low : Nat → Prop) :
    FieldsBack (blind (P := P) ψ) own low (fun a _ b _ => a.2.failed = b.2.failed) where
  constr _ _ _ := fun _ _ _ _ _ _ h => h
  pin _ _ _ := fun _ _ _ _ _ _ h => h
  pinW := fun _ _ _ _ _ _ h => h
  row _ _ := fun _ _ _ _ _ _ h => h
  carry _ := fun _ _ _ _ _ _ h => h
  pile := fun _ _ _ _ _ _ h => h
  pileOne := fun _ _ _ _ _ _ h => h
  wrow := fun _ _ _ _ _ _ h => h
  mark _ _ _ _ h hb := h.trans hb

/-- **It can fail**: over the relation that holds of all statements no meaning has it. -/
theorem not_fieldsBack_all (Mg : Meaning P W) (own : Nat → Part → Bool) (low : Nat → Prop)
    (z : P) (s : First.S) (y : Strs) : ¬ FieldsBack Mg own low (fun _ _ _ _ => True) := fun H => by
  have := H.mark (z, { s with failed := some "x" }) y (z, { s with failed := none }) y trivial rfl
  cases this

/-- Every tree that the item's pins name has `low`. -/
def lowItem (N : Numbers) (low : Nat → Prop) : Item → Prop
  | .pin m t => ∀ x ∈ N.sent m t, low x.1
  | .pinKept m => ∀ x ∈ N.keptOf m, low x.1
  | .pinI => low N.index.1
  | .pinV => low N.w.1
  | _ => True

/-- The item is no part of a segment's relation that `own` names. -/
def notOwn (own : Nat → Part → Bool) : Item → Prop
  | .constr m p => own m p = false
  | _ => True

/-- **From the fields to the items.** -/
theorem holds_back (N : Numbers) (Mg : Meaning P W) (own : Nat → Part → Bool) (low : Nat → Prop)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop) (H : FieldsBack Mg own low rel)
    (i : Item) (hp : i.part = none) (ho : notOwn own i) (hl : lowItem N low i) :
    GoesBack rel (i.holds N Mg) := by
  cases i with
  | constr m p => exact H.constr m p ho
  | pin m t => exact fun a y b y' w hr h x hx => H.pin x.1 x.2 (hl x hx) a y b y' w hr (h x hx)
  | pinKept m => exact fun a y b y' w hr h x hx => H.pin x.1 x.2 (hl x hx) a y b y' w hr (h x hx)
  | pinI => exact H.pin _ _ hl
  | pinV => exact H.pin _ _ hl
  | pinW => exact H.pinW
  | row m c => exact H.row m c
  | carry m => exact H.carry m
  | pile => exact H.pile
  | pileOne => exact H.pileOne
  | wrow => exact H.wrow
  | unmarked => exact fun a y b y' _ hr h => H.mark a y b y' hr h
  | tie m => cases hp
  | forms m k r => cases hp
  | formsT m k r => cases hp
  | worth m k r => cases hp
  | wo m => cases hp
  | totalB m => cases hp
  | total m => cases hp

/-- The same for what an item says of a statement of the chain. -/
theorem meansQ_back (N : Numbers) (Mg : Meaning P W) (get : A → P × First.S)
    (own : Nat → Part → Bool) (low : Nat → Prop)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop) (H : FieldsBack Mg own low rel)
    (i : Item) (hp : i.part = none) (ho : notOwn own i) (hl : lowItem N low i)
    (a b : A × Fr.E.Str) (w : W) (hr : rel (get a.1) (strsOf Fr a.2) (get b.1) (strsOf Fr b.2))
    (h : meansQ (Fr := Fr) N Mg get i b w) : meansQ (Fr := Fr) N Mg get i a w :=
  holds_back N Mg own low rel H i hp ho hl _ _ _ _ w hr h

/-- **At a piece whose yes gives rel, the tie for what rides is owed for the other items alone.** -/
theorem frames_of_fields (N : Numbers) (Mg : Meaning P W) (get : A → P × First.S)
    (own : Nat → Part → Bool) (low : Nat → Prop)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop) (H : FieldsBack Mg own low rel)
    (p : Piece C Fr A Cl W) (on on' : A × Fr.E.Str → Prop) (O In : Item → Prop)
    (hyes : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b →
      rel (get a.1) (strsOf Fr a.2) (get b.1) (strsOf Fr b.2))
    (he : ∀ i, (i.part = none ∧ notOwn own i ∧ lowItem N low i) → ∀ a τ w, on a →
      meansQ (Fr := Fr) N Mg get i a w → meansQ (Fr := Fr) N Mg get i a (p.ext a τ w))
    (rest : p.Frames on on' (meansQ (Fr := Fr) N Mg get)
      (fun i => O i ∧ ¬ (i.part = none ∧ notOwn own i ∧ lowItem N low i)) In) :
    p.Frames on on' (meansQ (Fr := Fr) N Mg get) O In :=
  frames_of_free p on on' _ O In (fun i => i.part = none ∧ notOwn own i ∧ lowItem N low i)
    (fun i hi a τ b w ha hb hb' h =>
      meansQ_back N Mg get own low rel H i hi.1 hi.2.1 hi.2.2 a b w (hyes a τ b ha hb hb') h)
    he rest

end

end VerifiableInference.Desc.Sound
