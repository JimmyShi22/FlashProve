-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
rides_at_seat_fields: no filling of the table's meaning is known at which
FieldsBack holds over relOut.
Johnson/Desc/Sound/RidesFields.lean: WHAT RIDES PAST A SEAT, FROM THE MEANING's FIELDS: the premise
hOut of rides_at_seat (Johnson/Desc/Sound/RidesSide.lean: "every rider without a part is ReadsOut")
PAID BY FieldsBack (Johnson/Desc/Sound/ItemsRide.lean: "each of the eight fields that such an item
reads goes back over rel") at the relation relOut base: what was handed to the chain is the same,
the verifier's two states agree in all but the open link's own part (SameOut), the strings stay
below base (Stays). Statements and proofs. Ties: no error term. It names no kind. NO RESULT ON THE
PROTOCOL.

OBJECT: no text that runs: two sentences on a sentence of the table of joints' meaning.
USER: nobody yet.
LETTERS: all free.

Compiled with the whole library.

Main names:
  `relOut base`: the relation.
  `readsOut_iff_goesBack`: ReadsOut base φ IS GoesBack (relOut base) φ: both ways.
  `hOut_of_fieldsBack`: so FieldsBack over relOut base gives ReadsOut base (i.holds N Mg) at every
    item without a part that is no part of a segment's relation which "own" names and whose pins'
    trees are "low".
  `rides_at_seat_fields`: THE SECOND CONJUNCT OF SeatLaws where no rider has a part, from: hback ·
    hSame · hNo · FieldsBack at low j := j < q.base · the two side conditions at every rider.

WHAT IS LEFT, AND WHOSE IT IS. FieldsBack: the fillers' of the eight fields, once for the file.
hown, hlow: facts on the table and the plan's numbers at the block's place.

Limits. A rule over letters. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.RidesSide
import Johnson.Desc.Sound.ItemsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker OnBytes.Flat KObj Fo.Peel
open _root_.Run.PQ (CK SgX)
open Johnson.Desc.First.Walk.Tied (Stays)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start SameOut ReadsOut)

section
variable {Cl P W : Type} {C : CK} {Fr : Frame}

/-- What was handed to the chain is the same; the two states agree in all but the open link's own
part; the strings stay below base. -/
def relOut (base : ℕ) : P × First.S → Strs → P × First.S → Strs → Prop :=
  fun a y b y' => a.1 = b.1 ∧ SameOut a.2 b.2 ∧ Stays base y y'

/-- **The two sentences are one.** -/
theorem readsOut_iff_goesBack (base : ℕ) (φ : P × First.S → Strs → W → Prop) :
    ReadsOut base φ ↔ GoesBack (relOut base) φ := by
  constructor
  · intro h a y b y' w hr hb
    obtain ⟨z, s⟩ := a
    obtain ⟨z', s'⟩ := b
    obtain ⟨e, hs, hy⟩ := hr
    have e' : z = z' := e
    subst e'
    exact h z s s' y y' w hs hy hb
  · intro h z s s' y y' w hs hy hb
    exact h (z, s) y (z, s') y' w ⟨rfl, hs, hy⟩ hb

/-- **From the fields to hOut.** -/
theorem hOut_of_fieldsBack (N : Numbers) (Mg : Meaning P W) (own : Nat → First.Part → Bool)
    (low : Nat → Prop) (base : ℕ) (H : FieldsBack Mg own low (relOut base)) (i : Item)
    (hp : i.part = none) (ho : notOwn own i) (hl : lowItem N low i) :
    ReadsOut base (i.holds N Mg) :=
  (readsOut_iff_goesBack base _).2 (holds_back N Mg own low _ H i hp ho hl)

/-- **WHAT RIDES PAST A SEAT AT WHICH NO RIDER HAS A PART, FROM THE MEANING's FIELDS.** -/
theorem rides_at_seat_fields (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (P × First.S) Cl W) (N : Numbers) (Mg : Meaning P W)
    (Bst : Block First.S Cl) (hback : q.back = [])
    (hSame : ∀ B', SeatOf Bst B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → SameOut a.1 b.1)
    (hNo : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → i.part = none)
    (own : Nat → First.Part → Bool) (H : FieldsBack Mg own (· < q.base) (relOut q.base))
    (hown : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → notOwn own i)
    (hlow : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → lowItem N (· < q.base) i) :
    ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w :=
  rides_at_seat_partless links ps k q N Mg Bst hback hSame hNo fun i ho hn =>
    hOut_of_fieldsBack N Mg own (· < q.base) q.base H i (hNo i ho hn) (hown i ho hn)
      (hlow i ho hn)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsOut_iff_goesBack
#print axioms VerifiableInference.Desc.Sound.hOut_of_fieldsBack
#print axioms VerifiableInference.Desc.Sound.rides_at_seat_fields
