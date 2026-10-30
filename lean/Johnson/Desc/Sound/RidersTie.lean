-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RidersTie.lean: the tie for what rides past a sub-protocol, in the form in which
the kinds' ties ask it, from the fields of a meaning. Five definitions, nine theorems. Rules over
letters: the meaning, the numbers, the piece, the relation and the extractor's value are letters.

Why. A kind's tie number five asks, at border k of the first chain's table of joints: an item that
is open in front of the sub-protocol, and that its row neither closes nor reads, means of the
statement in front, at the extractor's value, what it means of the statement behind. It is asked of
every such item. Two things turn there: the statement and the witness.
Johnson/Desc/Sound/ItemsRide.lean brings the statement's side, for the twelve sorts of item that
read no segment's part, down to eight fields of the meaning (`FieldsBack`).
Johnson/Desc/Sound/BordersSides.lean has the witness's side at the table's own extractor. Here the
two are laid into the tie's own form.

What is said. z: the public part. rel: a relation between the statement in front and the one behind.
X a b w: the witness in front that the table's extractor makes of a witness w behind.
  `byField N own low i`: the item rides by its field: `Item.part = none`, no part of a relation that
    `own` names, every tree of its pins `low`. `byFieldB`: the same as a test with code;
    `byField_of_B`: the test's accept gives it.
  `t5_of_fields`: THE TIE, from: `FieldsBack Mg own low rel` · an accept of the piece inside the two
    promises, at a state without a mark, gives rel · the sentences of the riding items that ride by
    their fields bear X · the tie itself for the items that do not ride by their fields.
  `ridersL links ps k`: the items that ride past sub-protocol number k, as a list, by the table's
    own functions. `ridersByFieldB`: a test with code: all of them ride by their fields.
  `rider_mem`: the tie's two premises on an item say that it is in that list.
  `t5_of_fields_all`: where that test accepts, the last premise of `t5_of_fields` falls.
  `t5_of_test`: THE LEANER FORM: ok: any test with code on items. Where all that ride past number k
    pass ok, and the sentence of every item that passes ok goes back over rel: the tie. Nothing is
    asked of a field that no riding item reads.
  `fourSortsB`, `goesBack_four`: the test "a part of a relation other than the digits', or the index
    masks' pin, or the committed table's pin, or the pile", and what its four sorts ask: four facts.
  `bears_extQAt`: under `ReadsOkQ` and `RidersClearQ` (Johnson/Desc/Sound/BordersSides.lean) a
    riding item's sentence bears the table's own extractor `extQAt`. `t5_at_table`: so the tie at
    X := `extQAt`, with no premise on X. `t5_four_at_table`: the same from the four facts, where all
    that ride are of the four sorts.

Limits. (1) That any real meaning has `FieldsBack` at any relation is a premise. (2) That an accept
of any sub-protocol gives any relation is a premise. (3) That the sentences bear X is a premise of
the first two forms; at the table's extractor it rests on `ReadsOkQ`, which whoever fills a field
owes. (4) The test reads the table and the numbers alone. (5) At rel := False the tie's premise on
an accept cannot be met where the piece accepts. No soundness of any verifier follows from this
file.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ItemsRide
import Johnson.Desc.Sound.BordersSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Part RowClass Meaning Numbers start)

/-- The item rides by its field. -/
def byField (N : Numbers) (own : Nat → Part → Bool) (low : Nat → Prop) (i : Item) : Prop :=
  i.part = none ∧ notOwn own i ∧ lowItem N low i

/-- The same as a test with code. -/
def byFieldB (N : Numbers) (own : Nat → Part → Bool) (lowB : Nat → Bool) : Item → Bool
  | .constr m p => !own m p
  | .pin m t => (N.sent m t).all fun x => lowB x.1
  | .pinKept m => (N.keptOf m).all fun x => lowB x.1
  | .pinI => lowB N.index.1
  | .pinV => lowB N.w.1
  | .pinW => true
  | .row _ _ => true
  | .carry _ => true
  | .pile => true
  | .pileOne => true
  | .wrow => true
  | .unmarked => true
  | _ => false

/-- The test's accept gives it. -/
theorem byField_of_B (N : Numbers) (own : Nat → Part → Bool) (lowB : Nat → Bool) (i : Item)
    (h : byFieldB N own lowB i = true) : byField N own (fun j => lowB j = true) i := by
  cases i with
  | constr m p => exact ⟨rfl, by simpa [byFieldB] using h, trivial⟩
  | pin m t => exact ⟨rfl, trivial, fun x hx => List.all_eq_true.1 h x hx⟩
  | pinKept m => exact ⟨rfl, trivial, fun x hx => List.all_eq_true.1 h x hx⟩
  | pinI => exact ⟨rfl, trivial, h⟩
  | pinV => exact ⟨rfl, trivial, h⟩
  | pinW => exact ⟨rfl, trivial, trivial⟩
  | row m c => exact ⟨rfl, trivial, trivial⟩
  | carry m => exact ⟨rfl, trivial, trivial⟩
  | pile => exact ⟨rfl, trivial, trivial⟩
  | pileOne => exact ⟨rfl, trivial, trivial⟩
  | wrow => exact ⟨rfl, trivial, trivial⟩
  | unmarked => exact ⟨rfl, trivial, trivial⟩
  | tie m => simp [byFieldB] at h
  | forms m k r => simp [byFieldB] at h
  | formsT m k r => simp [byFieldB] at h
  | worth m k r => simp [byFieldB] at h
  | wo m => simp [byFieldB] at h
  | totalB m => simp [byFieldB] at h
  | total m => simp [byFieldB] at h

/-- The items that ride past sub-protocol number k: open in front, neither closed nor read. -/
def ridersL (links : List ModelPart) (ps : List Place) (k : ℕ) : List Item :=
  (openL (insL links ps) (outsL links ps) (start links) k).filter fun i =>
    decide (i ∉ insL links ps k)

/-- A test with code: all of them ride by their fields. -/
def ridersByFieldB (N : Numbers) (own : Nat → Part → Bool) (lowB : Nat → Bool) (links : List ModelPart)
    (ps : List Place) (k : ℕ) : Bool :=
  (ridersL links ps k).all (byFieldB N own lowB)

/-- A test with code: a part of a relation other than the digits'; the index masks' pin; the
committed table's pin; the pile. -/
def fourSortsB : Item → Bool
  | .constr _ p => p != .lookDigits
  | .pinI => true
  | .pinW => true
  | .pile => true
  | _ => false

/-- The tie's two premises on an item say that it is in the list. -/
theorem rider_mem (links : List ModelPart) (ps : List Place) (k : ℕ) (i : Item)
    (ho : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i)
    (hn : ¬ insQ links ps k i) : i ∈ ridersL links ps k :=
  List.mem_filter.2
    ⟨(openIsList Item (insL links ps) (outsL links ps) (start links) k i).1 ho,
      decide_eq_true hn⟩

section
variable {P W Cl : Type} {C : CK} {Fr : Frame}

/-- **The tie for what rides, from the meaning's fields.** -/
theorem t5_of_fields (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (z : P) (own : Nat → Part → Bool) (low : Nat → Prop)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop) (H : FieldsBack Mg own low rel)
    (p : Piece C Fr First.S Cl W)
    (X : First.S × Fr.E.Str → First.S × Fr.E.Str → W → W)
    (hyes : ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      rel (z, a.1) (strsOf Fr a.2) (z, b.1) (strsOf Fr b.2))
    (hX : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → byField N own low i → ∀ a b w,
      meansQ N Mg (fun s => (z, s)) i a w → meansQ N Mg (fun s => (z, s)) i a (X a b w))
    (hrest : ∀ a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      ¬ byField N own low i → meansQ N Mg (fun s => (z, s)) i a (X a b w)) :
    ∀ a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a (X a b w) := by
  intro a τ b w i ha hm hb hb' hrel ho hn
  by_cases hf : byField N own low i
  · have h1 : meansQ N Mg (fun s => (z, s)) i b w := hrel i (Or.inl ⟨ho, hn⟩)
    exact hX i ho hn hf a b w
      (meansQ_back N Mg _ own low rel H i hf.1 hf.2.1 hf.2.2 a b w (hyes a τ b ha hm hb hb') h1)
  · exact hrest a τ b w i ha hm hb hb' hrel ho hn hf

/-- **The leaner form**: at any test with code on the items that ride. -/
theorem t5_of_test (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (z : P) (rel : P × First.S → Strs → P × First.S → Strs → Prop) (p : Piece C Fr First.S Cl W)
    (X : First.S × Fr.E.Str → First.S × Fr.E.Str → W → W) (ok : Item → Bool)
    (hB : (ridersL links ps k).all ok = true)
    (hG : ∀ i, ok i = true → GoesBack rel (i.holds N Mg))
    (hyes : ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      rel (z, a.1) (strsOf Fr a.2) (z, b.1) (strsOf Fr b.2))
    (hX : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → ∀ a b w,
      meansQ N Mg (fun s => (z, s)) i a w → meansQ N Mg (fun s => (z, s)) i a (X a b w)) :
    ∀ a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a (X a b w) := by
  intro a τ b w i ha hm hb hb' hrel ho hn
  have h1 : meansQ N Mg (fun s => (z, s)) i b w := hrel i (Or.inl ⟨ho, hn⟩)
  exact hX i ho hn a b w
    (hG i (List.all_eq_true.1 hB i (rider_mem links ps k i ho hn)) _ _ _ _ w
      (hyes a τ b ha hm hb hb') h1)

/-- What the four sorts ask: four facts. -/
theorem goesBack_four (N : Numbers) (Mg : Meaning P W)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (hc : ∀ m p, p ≠ Part.lookDigits → GoesBack rel (Mg.constr m p))
    (hI : GoesBack rel (Mg.pin N.index.1 N.index.2)) (hW : GoesBack rel Mg.pinW)
    (hP : GoesBack rel Mg.pile) (i : Item) (h : fourSortsB i = true) :
    GoesBack rel (i.holds N Mg) := by
  cases i with
  | constr m p => exact hc m p (by simpa [fourSortsB] using h)
  | pinI => exact hI
  | pinW => exact hW
  | pile => exact hP
  | pin m t => simp [fourSortsB] at h
  | pinKept m => simp [fourSortsB] at h
  | pinV => simp [fourSortsB] at h
  | row m c => simp [fourSortsB] at h
  | carry m => simp [fourSortsB] at h
  | pileOne => simp [fourSortsB] at h
  | wrow => simp [fourSortsB] at h
  | unmarked => simp [fourSortsB] at h
  | tie m => simp [fourSortsB] at h
  | forms m k r => simp [fourSortsB] at h
  | formsT m k r => simp [fourSortsB] at h
  | worth m k r => simp [fourSortsB] at h
  | wo m => simp [fourSortsB] at h
  | totalB m => simp [fourSortsB] at h
  | total m => simp [fourSortsB] at h

/-- **Where all that ride ride by their fields.** -/
theorem t5_of_fields_all (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (z : P) (own : Nat → Part → Bool) (lowB : Nat → Bool)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (H : FieldsBack Mg own (fun j => lowB j = true) rel) (p : Piece C Fr First.S Cl W)
    (X : First.S × Fr.E.Str → First.S × Fr.E.Str → W → W)
    (hB : ridersByFieldB N own lowB links ps k = true)
    (hyes : ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      rel (z, a.1) (strsOf Fr a.2) (z, b.1) (strsOf Fr b.2))
    (hX : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → byField N own (fun j => lowB j = true) i → ∀ a b w,
      meansQ N Mg (fun s => (z, s)) i a w → meansQ N Mg (fun s => (z, s)) i a (X a b w)) :
    ∀ a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a (X a b w) :=
  t5_of_fields N Mg links ps k z own _ rel H p X hyes hX
    fun _ _ _ _ i _ _ _ _ _ ho hn hf =>
      absurd (byField_of_B N own lowB i (List.all_eq_true.1 hB i (rider_mem links ps k i ho hn))) hf

end

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok Cl : Type} {C : CK} {Fr : Frame} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × First.S → Tok)

/-- **A riding item's sentence bears the table's own extractor.** -/
theorem bears_extQAt {A : Type} (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ)
    (hr : ReadsOkQ arr N links Mg) (hc : RidersClearQ arr N links ps) (i : Item)
    (ho : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i)
    (hn : ¬ insQ links ps k i) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (h : meansQ N Mg get i a w) :
    meansQ N Mg get i a (extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w) :=
  hr i _ _ w _
    (fun c hm => extQAt_keeps cs G arr smp ms decT c₀ tokOf N links ps get k a b w c
      (hc k i ho hn c hm)) h

/-- **The tie at the table's own extractor.** -/
theorem t5_at_table (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (z : P) (own : Nat → Part → Bool) (lowB : Nat → Bool)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (H : FieldsBack Mg own (fun j => lowB j = true) rel)
    (p : Piece C Fr First.S Cl (Wit Cells Tok MsgT))
    (hB : ridersByFieldB N own lowB links ps k = true) (hr : ReadsOkQ arr N links Mg)
    (hc : RidersClearQ arr N links ps)
    (hyes : ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      rel (z, a.1) (strsOf Fr a.2) (z, b.1) (strsOf Fr b.2)) :
    ∀ a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a
        (extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun s => (z, s)) k a b w) :=
  t5_of_fields_all N Mg links ps k z own lowB rel H p
    (fun a b w => extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun s => (z, s)) k a b w) hB hyes
    fun i ho hn _ a b w h =>
      bears_extQAt cs G arr smp ms decT c₀ tokOf N Mg links ps (fun s => (z, s)) k hr hc i ho hn a b
        w h

/-- **The tie at the table's own extractor, from four facts**, where all that ride are of the four
sorts. -/
theorem t5_four_at_table (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (z : P) (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (p : Piece C Fr First.S Cl (Wit Cells Tok MsgT))
    (hB : (ridersL links ps k).all fourSortsB = true)
    (h1 : ∀ m q, q ≠ Part.lookDigits → GoesBack rel (Mg.constr m q))
    (h2 : GoesBack rel (Mg.pin N.index.1 N.index.2)) (h3 : GoesBack rel Mg.pinW)
    (h4 : GoesBack rel Mg.pile) (hr : ReadsOkQ arr N links Mg) (hc : RidersClearQ arr N links ps)
    (hyes : ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      rel (z, a.1) (strsOf Fr a.2) (z, b.1) (strsOf Fr b.2)) :
    ∀ a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      p.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a
        (extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun s => (z, s)) k a b w) :=
  t5_of_test N Mg links ps k z rel p
    (fun a b w => extQAt cs G arr smp ms decT c₀ tokOf N links ps (fun s => (z, s)) k a b w)
    fourSortsB hB (goesBack_four N Mg rel h1 h2 h3 h4) hyes
    fun i ho hn a b w h =>
      bears_extQAt cs G arr smp ms decT c₀ tokOf N Mg links ps (fun s => (z, s)) k hr hc i ho hn a b
        w h

end

end VerifiableInference.Desc.Sound
