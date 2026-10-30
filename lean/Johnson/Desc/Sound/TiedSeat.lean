-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TiedSeat.lean: FROM A KIND'S LAW AT THE TABLE'S OWN WORDS TO THE TIE AT THE
DESCRIPTION'S PIECE, WHATEVER THE KIND. A rule over letters; nothing in it names a kind. NO RESULT
ON THE PROTOCOL.

What is said.
  `SeatOf Bst B'`: B' narrows the block Bst that a seat lays, and its yes bears no mark.
  `tiedBy_of_own`: a block's own law at the table, what rides (in the tie's own fenced form) and the
    two facts on its text ("a mark stays", "decodes rides") give the tie at the table's own words.
  **`tiedBy_of_seat`**: so at the description's piece: it spends of the place TWO THINGS ALONE:
    `SeatOf Bst B` and the piece's form q.b = (below B).lift …: whoever shows these two at a place
    of a description (from the driver's flat list: AtDriver.lean; or at a description's value) has
    the tie from the kind's four premises. By `tiedBy_of_part` (TiedLift.lean).
  `SeatLaws … Bst` (from K3's
    files, here so that a kind's files can END IN THE NAME): the four, asked at EVERY B' with
    `SeatOf Bst B'`: at a seat the block B stands under "there is": a kind's files cannot name it. `tiedBy_of_seatLaws`: the tie from that name.

Limits. The four premises are the caller's; that they can be met is not said. hE: THESE RULES SERVE
THE ROWS AT WHICH THE TABLE's EXTRACTOR LAYS NOTHING ALONE (for the rows that lay: TiedLays.lean).
hMark at a block whose yes bears no mark says in effect "at a marked record there is no yes":
payable where the kind's decision keeps the mark, since the mark's guard then refuses. Nothing on
hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TiedLift
import Johnson.Desc.Sound.MergeNarrow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes OnBytes.Maker OnBytes.Flat KObj
open OnBytes.Model (Aff)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Pub start segRow shift pubRowOf pubFit
  pubRowM pubStartM More)

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S)

/-- A block's own law at the table, what rides (IN THE TIE's OWN FENCED FORM: no mark in front, the
promise and all that is open behind in hand), and the two facts on its text: a tie at the table's
own words. -/
theorem tiedBy_of_own (k : ℕ) (q : Piece C Fr A Cl W)
    (ho : q.Own (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (insQ links ps k) (outsQ links ps k))
    (t5 : ∀ a τ b w i, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
      relQ N Mg links ps get (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i a (q.ext a τ w))
    (hMark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2)) :
    TiedBy N Mg links ps get k q (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1))
      (relAt (meansQ N Mg get) (insQ links ps k)) (relAt (meansQ N Mg get) (outsQ links ps k)) :=
  ⟨ho, fun _ ha _ => ha, fun _ _ _ _ _ _ hb => hb, fun _ _ _ _ _ _ _ _ hO => hO,
    fun _ _ _ _ _ _ _ _ _ hR => hR,
    t5, hMark, hDec⟩

end

section
variable {Cl P W : Type} {C : CK} {Fr : Frame} (links : List ModelPart)

/-- B' narrows the block Bst, and its yes bears no mark. -/
def SeatOf (Bst B' : Block First.S Cl) : Prop :=
  B'.Narrows Bst ∧ ∀ s rs gs t, B'.decide s rs gs = .ok t → t.failed = none

/-- **A BLOCK AT A SEAT IS TIED, WHATEVER ITS KIND.** Bst: what the seat lays; B: the block that the
description's piece q holds beneath the lift over the public part (hq), which narrows Bst and whose
yes bears no mark (hS). row, rides, hMark, hDec: LEFT TO THE KIND's FILES, at the piece over the
carried record that holds `below B`, for every value z of the public part (asked AT B ALONE;
hS is then spent by nothing here: it stands for the kind's
files, and in `SeatLaws`). rides: in the tie's own fenced form. E: the table's extractor at k, which
lays nothing at this row (hE). -/
theorem tiedBy_of_seat (ps : List Place) (k : ℕ) (Bst B : Block First.S Cl)
    (q : Piece C Fr (P × First.S) Cl W) (hS : SeatOf Bst B)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (N : Numbers) (Mg : Meaning P W)
    (E : (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (row : ∀ z : P,
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr First.S Cl W).Own
        (onQ N Mg links ps (fun s => (z, s)) k) (onQ N Mg links ps (fun s => (z, s)) (k + 1))
        (meansQ N Mg fun s => (z, s)) (insQ links ps k) (outsQ links ps k))
    (rides : ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w)
    (hMark : ∀ a τ b,
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none)
    (hDec : ∀ (z : P) a τ b,
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    TiedBy N Mg links ps (fun a => a) k (q.withMap E) (onQ N Mg links ps (fun a => a) k)
      (onQ N Mg links ps (fun a => a) (k + 1)) (relAt (meansQ N Mg fun a => a) (insQ links ps k))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps k)) :=
  tiedBy_of_part N Mg links ps k q (below B) hq E hE
    (fun z => onQ N Mg links ps (fun s => (z, s)) k)
    (fun z => onQ N Mg links ps (fun s => (z, s)) (k + 1))
    (fun z => relAt (meansQ N Mg fun s => (z, s)) (insQ links ps k))
    (fun z => relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k))
    fun z => tiedBy_of_own N Mg links ps (fun s => (z, s)) k _ (row z)
      (rides z) hMark (hDec z)



/-- **What a kind's files owe at a seat**, as `tiedBy_of_seat` takes it. -/
def SeatLaws {Cl P W : Type} {C : CK} {Fr : Frame} (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (P × First.S) Cl W) (N : Numbers) (Mg : Meaning P W) (Bst : Block First.S Cl) :
  Prop := (∀ B', SeatOf Bst B' → ∀ z : P,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr First.S Cl W).Own
        (onQ N Mg links ps (fun s => (z, s)) k) (onQ N Mg links ps (fun s => (z, s)) (k + 1))
        (meansQ N Mg fun s => (z, s)) (insQ links ps k) (outsQ links ps k)) ∧
  (∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) ∧
  (∀ B', SeatOf Bst B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none) ∧
  ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)

/-- **The tie from the kind's four under that name.** -/
theorem tiedBy_of_seatLaws (ps : List Place) (k : ℕ) (Bst B : Block First.S Cl)
    (q : Piece C Fr (P × First.S) Cl W) (hS : SeatOf Bst B)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (N : Numbers) (Mg : Meaning P W)
    (E : (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (H : SeatLaws links ps k q N Mg Bst) :
    TiedBy N Mg links ps (fun a => a) k (q.withMap E) (onQ N Mg links ps (fun a => a) k)
      (onQ N Mg links ps (fun a => a) (k + 1)) (relAt (meansQ N Mg fun a => a) (insQ links ps k))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps k)) :=
  tiedBy_of_seat links ps k Bst B q hS hq N Mg E hE (H.1 B hS) (H.2.1 B hS) (H.2.2.1 B hS)
    (H.2.2.2 B hS)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tiedBy_of_own
#print axioms VerifiableInference.Desc.Sound.tiedBy_of_seat
#print axioms VerifiableInference.Desc.Sound.tiedBy_of_seatLaws
