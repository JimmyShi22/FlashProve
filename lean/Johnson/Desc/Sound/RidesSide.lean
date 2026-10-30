-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RidesSide.lean: WHAT RIDES PAST A BLOCK WHOSE EXTRACTOR IS THE IDENTITY, WHATEVER
ITS KIND: it is the statement's side alone; and an item whose sentence is ReadsOut
(Johnson/Desc/First/SameOut.lean) rides past every piece whose yes leaves all but the open link's
own part of the record. Statements and proofs. Ties: no error term. It names no kind. NO RESULT ON
THE PROTOCOL.

OBJECT: a piece over the carried record that holds "below B" and has nothing put behind its rounds.
USER: Johnson/Desc/First/Look/K3Rides.lean.
LETTERS: all free.
Compiled with the whole library.


Main names:
  `rides_of_side`: a rider holds behind because it is open behind (the relation at border k + 1 is
    "every open item holds", and what is open at k and not closed or read by block k is open at
    k + 1): so "what rides", at one witness, follows from the statement's side.
  `side_out`: the statement's side of an item whose sentence is ReadsOut at the piece's base, at a
    yes of the piece that is SameOut: by what a stage leaves of the strings (stays_behind,
    Johnson/Top/H0/Walk/StaysBehind.lean).
  `rides_at_seat`: THE SECOND CONJUNCT OF SeatLaws (Johnson/Desc/Sound/TiedSeat.lean), TO THE SIGN,
    from: hback · hSame (a yes of the piece is SameOut) · hOut (every rider that the table books as
    reading no segment's part is ReadsOut) · hOwn (the other riders' statement's side, as it
    stands).
  `ridersPartless links ps k`: A Bool ON THE TABLE: every item that is open in front of block k and
    that its row neither closes nor reads has no part. `partless_of_test`: what a yes gives.
  `rides_at_seat_partless`: where no rider has a part hOwn falls.

WHAT IS LEFT, AND WHOSE IT IS. hSame: the kind's. hOut: each sort's filler's, once for the file.
hOwn: the fillers' of the items that read the open link's own part. THESE ARE DEBTS: NOTHING HERE
PAYS THEM.

Limits. No filling of the table's meaning is known at which hOut holds at
every rider. A rule over letters. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.SameOut
import Johnson.Desc.Sound.TiedSeat
import Johnson.Desc.Sound.BordersSides
import Johnson.Top.H0.Walk.StaysBehind
import Johnson.Desc.Sound.PieceYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker OnBytes.Flat KObj Fo.Peel
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start openSets readsOpen rowOf SameOut
  ReadsOut)

/-! ## 1 Where the extractor is the identity -/

section
variable {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S)

/-- **A rider holds behind because it is open behind**: so what rides, at one witness, is the
statement's side. -/
theorem rides_of_side (k : ℕ) (a b : A × Fr.E.Str) (w : W) (i : Item)
    (hR : relQ N Mg links ps get (k + 1) b w)
    (ho : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i)
    (hn : ¬ insQ links ps k i)
    (hside : meansQ N Mg get i b w → meansQ N Mg get i a w) : meansQ N Mg get i a w :=
  hside (hR i (Or.inl ⟨ho, hn⟩))

end

/-! ## 2 A sentence that reads nothing of the open link's own part -/

section
variable {Cl P W : Type} {C : CK} {Fr : Frame}

/-- **Such a sentence rides past a piece whose yes is SameOut.** -/
theorem side_out (p : Piece C Fr First.S Cl W) (B : Block First.S Cl) (hb : p.b = below B)
    (hback : p.back = []) (z : P) (N : Numbers) (Mg : Meaning P W) (i : Item)
    (hi : ReadsOut p.base (i.holds N Mg)) (a b : First.S × Fr.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (w : W) (h : p.ior.red.out a τ = some b)
    (hS : SameOut a.1 b.1) :
    meansQ N Mg (fun s => (z, s)) i b w → meansQ N Mg (fun s => (z, s)) i a w := by
  obtain ⟨-, e2, -, -⟩ := piece_below_plain p B hb hback a b τ h
  intro hm
  refine hi z a.1 b.1 (strsOf Fr a.2) (strsOf Fr b.2) w hS ?_ hm
  rw [e2]
  exact Johnson.Desc.First.Walk.Tied.stays_behind C Fr p.base p.ds a.2 τ

/-! ## 3 What rides past a seat -/

/-- **THE SECOND OF THE FOUR THAT A KIND OWES AT A SEAT.** -/
theorem rides_at_seat (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (P × First.S) Cl W) (N : Numbers) (Mg : Meaning P W)
    (Bst : Block First.S Cl) (hback : q.back = [])
    (hSame : ∀ B', SeatOf Bst B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → SameOut a.1 b.1)
    (hOut : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → i.part = none → ReadsOut q.base (i.holds N Mg))
    (hOwn : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      i.part ≠ none → meansQ N Mg (fun s => (z, s)) i b w → meansQ N Mg (fun s => (z, s)) i a w) :
    ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w := by
  intro B' hS z a τ b w i ha hm hb hb' hR ho hn
  refine rides_of_side N Mg links ps (fun s => (z, s)) k a b w i hR ho hn ?_
  by_cases hp : i.part = none
  · exact side_out (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C Fr First.S Cl W) B' rfl hback z N Mg i (hOut i ho hn hp) a b τ w hb
      (hSame B' hS a τ b hb)
  · exact hOwn B' hS z a τ b w i ha hm hb hb' ho hn hp

end

/-! ## 4 A Bool on the table: no rider has a part -/

/-- Every item that is open in front of block k and that its row neither closes nor reads has no
part: the table books it as reading no segment's part of the record. -/
def ridersPartless (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((openSets links ps (start links))[k]?.getD []).all fun i =>
    (((ps[k]?.map (rowOf links)).getD {}).ins ++ ((ps[k]?.map (rowOf links)).getD {}).ctx ++
      [Item.unmarked]).contains i || i.part.isNone

/-- **What a yes gives**, where the table's two tests say yes. -/
theorem partless_of_test (links : List ModelPart) (ps : List Place) (k : ℕ) (hk : k ≤ ps.length)
    (h1 : ridersPartless links ps k = true) (h2 : readsOpen links ps (start links) = true)
    (h3 : rowsApart links ps = true) :
    ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → i.part = none := by
  intro i ho hn
  have hu : Item.unmarked ∈ start links := List.mem_append_left _ (List.mem_cons_self)
  have hL : i ∈ openL (insL links ps) (outsL links ps) (start links) k :=
    (openIsList Item (insL links ps) (outsL links ps) (start links) k i).1 ho
  have hO := (openL_iff_openSets links ps (start links) h2 h3 hu k hk i).1 hL
  have h4 := List.all_eq_true.1 h1 i hO
  rcases Eq.mp (Bool.or_eq_true _ _) h4 with h5 | h5
  · refine absurd ?_ hn
    show i ∈ (rowQ links ps k).ins ++ (rowQ links ps k).ctx ++ [.unmarked]
    exact List.contains_iff_mem.1 h5
  · exact Option.isNone_iff_eq_none.1 h5

section
variable {Cl P W : Type} {C : CK} {Fr : Frame}

/-- **Where no rider has a part, the statement's side is hOut alone.** -/
theorem rides_at_seat_partless (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (P × First.S) Cl W) (N : Numbers) (Mg : Meaning P W)
    (Bst : Block First.S Cl) (hback : q.back = [])
    (hSame : ∀ B', SeatOf Bst B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → SameOut a.1 b.1)
    (hNo : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → i.part = none)
    (hOut : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → ReadsOut q.base (i.holds N Mg)) :
    ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w :=
  rides_at_seat links ps k q N Mg Bst hback hSame (fun i ho hn _ => hOut i ho hn)
    fun _ _ _ _ _ _ _ i _ _ _ _ ho hn hp _ => absurd (hNo i ho hn) hp

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.rides_of_side
#print axioms VerifiableInference.Desc.Sound.side_out
#print axioms VerifiableInference.Desc.Sound.rides_at_seat
#print axioms VerifiableInference.Desc.Sound.partless_of_test
#print axioms VerifiableInference.Desc.Sound.rides_at_seat_partless
