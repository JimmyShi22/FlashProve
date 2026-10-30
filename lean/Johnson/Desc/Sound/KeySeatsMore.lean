-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeySeatsMore.lean: MORE TOOLS FOR THE SEATS OF A CHAIN.

What is said.
  `seat_of_pass`: a seat, whichever its number, whose block hands the record on just where some
    clauses hold is filled (`SeatGood`, Johnson/Desc/Sound/KeySeatsAt.lean), between the row in
    front of it and the same row with the clauses passed (`JointRow.passed`,
    Johnson/Desc/Sound/KeyJoints.lean). `seat_of_end` there is the case of a chain's last seat.
  `seat_of_same`: a seat whose block hands the record on as it is, is filled between a row and the
    same row: so against every list of rows that has one row at its two borders.
  `seat_of_goodIn`: a seat is filled by `Piece.GoodIn` (Johnson/Desc/Sound/GoodIn.lean), where the
    two rows are the law's two borders. `seats_of_eachGoodIn`: a whole stretch of seats is filled by
    one row of that form (`EachGoodIn`). `goodIn_below`, `seat_of_goodIn_own`: A SEAT IS FILLED BY A
    KIND'S FILES' LAW AT THE CHAIN'S OWN RECORD (`Piece.GoodIn` of the description's block itself
    at the cut stretch), with a claim carried beside it (`goodInBeside`, `liftGoodIn`).
    `seat_between`: a seat that is filled between two rows of its own is filled between
    the rows at its borders, where these are joined to its own by `rowLe`
    (Johnson/Desc/Sound/KeyRowsOfBorders.lean).
  `onImageAt pub fst b`: THE GUARD `onImage` (KeyJoints.lean) AT A CARRIED RECORD OF WHATEVER MAKE:
    fst reads the public part out of it (in the first chain the first part; in the later chains the
    first part's first part). `onImageAt_first`: at the first chain it is `onImage`.
    `onImageAt_keep`: a step that leaves the public part as it is keeps it.

Limits. Rules.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeySeatsAt
import Johnson.Desc.Sound.GoodInProofs
import Johnson.Desc.Sound.LiftRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.ChainEnd
open _root_.Run (ckP)
open _root_.Iop (Err)

variable {P S₀ Cl W : Type} {F : Frame}

/-- **A seat whose block hands the record on just where some clauses hold is filled**, between the
row in front of it and the same row with the clauses passed. -/
theorem seat_of_pass (εs : ℝ≥0∞) (A : JointRow (P × S₀) F)
    (ps : List (Piece (ckP .two) F (P × S₀) Cl W)) (rs : List (JointRow (P × S₀) F))
    (bs : List (Block S₀ Cl))
    (hbs : ps.map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s))) (i : ℕ)
    (e : Block S₀ Cl) (he : bs[i]? = some e) (asks : S₀ → Clauses)
    (hdec : ∀ s rs gs s', e.decide s rs gs = .ok s' → (∀ c ∈ asks s, c.2 = true) ∧ s' = s)
    (hrow : keyRowAt A rs (i + 1) = (keyRowAt A rs i).passed fun t => asks t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, ps[i]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (i + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (i + 1)).rel) :
    SeatGood εs A ps rs i := by
  refine seat_of_quiet εs A ps rs i e hnd
    (fun p hp' => ⟨block_at ps bs hbs i p e hp' he, hp p hp'⟩) ?_
  rw [hrow]
  exact quietOwn_of_pass e asks hdec _

/-- **A seat whose block hands the record on as it is, is filled between a row and the same row.**
So it is filled against every list of rows that has one row at its two borders. -/
theorem seat_of_same (εs : ℝ≥0∞) (A : JointRow (P × S₀) F)
    (ps : List (Piece (ckP .two) F (P × S₀) Cl W)) (rs : List (JointRow (P × S₀) F))
    (bs : List (Block S₀ Cl))
    (hbs : ps.map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s))) (i : ℕ)
    (e : Block S₀ Cl) (he : bs[i]? = some e)
    (hdec : ∀ s rs gs s', e.decide s rs gs = .ok s' → s' = s)
    (hrow : keyRowAt A rs (i + 1) = keyRowAt A rs i) (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, ps[i]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (i + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (i + 1)).rel) :
    SeatGood εs A ps rs i := by
  refine seat_of_quiet εs A ps rs i e hnd
    (fun p hp' => ⟨block_at ps bs hbs i p e hp' he, hp p hp'⟩) ?_
  rw [hrow]
  intro p s s' y rs gs ha hd
  obtain rfl := hdec s rs gs s' hd
  exact ⟨ha, fun hr => hr⟩

/-- **A seat is filled by the rule of composition's files' own form of a block's law**
(`Piece.GoodIn`, Johnson/Desc/Sound/GoodIn.lean: the promise behind is kept, and every witness
behind gives one in front), where the two rows are the law's two borders (`JointRow.ofBorder`). -/
theorem seat_of_goodIn {S : Type} (εs : ℝ≥0∞) (A : JointRow S F)
    (ps : List (Piece (ckP .two) F S Cl W)) (rs : List (JointRow S F)) (i : ℕ)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (hA : keyRowAt A rs i = JointRow.ofBorder on R)
    (hB : keyRowAt A rs (i + 1) = JointRow.ofBorder on' R')
    (h : ∀ p, ps[i]? = some p → p.GoodIn on on' R R' ∧ Err.Below p.err εs) :
    SeatGood εs A ps rs i := by
  intro p hp
  rw [hA, hB]
  exact ⟨goodShadow p on on' R R' (goodOfGoodIn S Cl W (ckP .two) F p on on' R R' (h p hp).1),
    (h p hp).2⟩

/-- Along a row of that form (`EachGoodIn`), block by block. -/
theorem eachGoodIn_at {S : Type} (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) :
    ∀ (l : List (Piece (ckP .two) F S Cl W)) (k : ℕ), EachGoodIn on R k l →
      ∀ (i : ℕ) (p : Piece (ckP .two) F S Cl W), l[i]? = some p →
        p.GoodIn (on (k + i)) (on (k + i + 1)) (R (k + i)) (R (k + i + 1))
  | [], _, _, _, _, h => by cases h
  | q :: _, _, h, 0, p, hp => by
    obtain rfl : q = p := Option.some.inj hp
    exact h.1
  | _ :: l, k, h, i + 1, p, hp => by
    have e := eachGoodIn_at on R l (k + 1) h.2 i p hp
    have e1 : k + 1 + i = k + (i + 1) := by omega
    rw [e1] at e
    exact e

/-- **A whole stretch of seats is filled by one row of that form** (`EachGoodIn`): the
pieces l sit at the seats j, j + 1, …; the rows there are the row's borders from the number k on. -/
theorem seats_of_eachGoodIn {S : Type} (εs : ℝ≥0∞) (A : JointRow S F)
    (ps : List (Piece (ckP .two) F S Cl W)) (rs : List (JointRow S F))
    (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) (j k : ℕ)
    (l : List (Piece (ckP .two) F S Cl W)) (hl : ∀ i, i < l.length → ps[j + i]? = l[i]?)
    (hr : ∀ i, i ≤ l.length → keyRowAt A rs (j + i) = JointRow.ofBorder (on (k + i)) (R (k + i)))
    (hε : ∀ p ∈ l, Err.Below p.err εs) (h : EachGoodIn on R k l) :
    ∀ i, i < l.length → SeatGood εs A ps rs (j + i) := fun i hi =>
  seat_of_goodIn εs A ps rs (j + i) _ _ _ _ (hr i (Nat.le_of_lt hi)) (hr (i + 1) hi) fun p hp =>
    have hp' : l[i]? = some p := (hl i hi).symm.trans hp
    ⟨eachGoodIn_at on R l k h i p hp', hε p (List.mem_of_getElem? hp')⟩

/-- A block's law in that form holds of the block with the test below the prime in front: it says
yes less often. -/
theorem goodIn_below {S : Type} (p : Piece (ckP .two) F S Cl W) (hb : viewWordsBelowPrime ⟨p.back, []⟩ = true)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (h : p.GoodIn on on' R R') :
    p.below.GoodIn on on' R R' := fun a ha =>
  Iop.Doomed.mono _ _ (fun τ hτ b hb' => hτ b (Piece.below_out p hb a b τ hb').2) (h a ha)

/-- **A SEAT IS FILLED BY A KIND'S FILES' LAW AT THE CHAIN'S OWN RECORD** (`Piece.GoodIn` of the
description's block itself, at the stretch that the maker cuts), WITH A CLAIM CARRIED BESIDE IT. p₀:
the block with its stretch at the chain's own record; the piece at seat i is p₀ with the test below
the prime in front, lifted. Rc: what is open besides and the block neither reads nor tests (it may
read what was handed to the chain): the one premise on it is asked where the block says yes, inside
the promise. -/
theorem seat_of_goodIn_own (εs : ℝ≥0∞) (A : JointRow (P × S₀) F)
    (ps : List (Piece (ckP .two) F (P × S₀) Cl W)) (rs : List (JointRow (P × S₀) F)) (i : ℕ)
    (p₀ : Piece (ckP .two) F S₀ Cl W) (hback : viewWordsBelowPrime ⟨p₀.back, []⟩ = true)
    (on on' : S₀ × F.E.Str → Prop) (R R' : S₀ × F.E.Str → W → Prop)
    (Rc : (P × S₀) × F.E.Str → W → Prop)
    (hq : ps[i]? = some (p₀.below.lift Prod.snd fun t s => (t.1, s)))
    (hA : keyRowAt A rs i = JointRow.ofBorder (fun a => on (atPart Prod.snd a))
      (fun a w => R (atPart Prod.snd a) w ∧ Rc a w))
    (hB : keyRowAt A rs (i + 1) = JointRow.ofBorder (fun a => on' (atPart Prod.snd a))
      (fun a w => R' (atPart Prod.snd a) w ∧ Rc a w))
    (h : p₀.GoodIn on on' R R') (hε : Err.Below p₀.err εs)
    (hc : ∀ a τ b w, on (atPart Prod.snd a) →
      (p₀.below.lift Prod.snd fun (t : P × S₀) s => (t.1, s)).ior.red.out a τ = some b →
      on' (atPart Prod.snd b) → Rc b w → Rc a (p₀.ext (atPart Prod.snd a) τ w)) :
    SeatGood εs A ps rs i :=
  seat_of_goodIn εs A ps rs i _ _ _ _ hA hB fun p hp => by
    obtain rfl : (p₀.below.lift Prod.snd fun (t : P × S₀) s => (t.1, s)) = p :=
      Option.some.inj (hq.symm.trans hp)
    exact ⟨goodInBeside _ _ _ _ _ _ _ _ _ _ Rc
      (liftGoodIn (P × S₀) S₀ Cl W (ckP .two) F Prod.snd (fun t s => (t.1, s)) p₀.below on on' R R'
        (fun _ _ => rfl) (fun _ _ _ => rfl) (goodIn_below p₀ hback on on' R R' h)) hc, hε⟩

/-- **Two seats whose rows do not meet to the letter are joined**: a seat that is filled between A'
and B' is filled between the rows at its borders, where the row in front gives A' and B' gives the
row behind (`rowLe`, Johnson/Desc/Sound/KeyRowsOfBorders.lean). -/
theorem seat_between {S : Type} (εs : ℝ≥0∞) (A : JointRow S F)
    (ps : List (Piece (ckP .two) F S Cl W)) (rs : List (JointRow S F)) (i : ℕ)
    (A' B' : JointRow S F) (mA : rowLe (keyRowAt A rs i) A') (mB : rowLe B' (keyRowAt A rs (i + 1)))
    (h : ∀ p, ps[i]? = some p →
      (p.bk A'.on B'.on (fun a _ => A'.rel a) (fun a _ => B'.rel a)).Good ∧ Err.Below p.err εs) :
    SeatGood εs A ps rs i := fun p hp =>
  ⟨goodInto p _ B' _ mB (goodFrom p _ A' B' mA (h p hp).1), (h p hp).2⟩

/-- **The guard at a carried record of whatever make**: the public part, read by fst, is some
instance's public part. -/
def onImageAt {R Q S Y : Type} (pub : R → Q) (fst : S → Q) (b : S × Y) : Prop :=
  ∃ rec, fst b.1 = pub rec

theorem onImageAt_first {R Q S' Y : Type} (pub : R → Q) (b : (Q × S') × Y) :
    onImageAt pub Prod.fst b ↔ onImage pub b := Iff.rfl

theorem onImageAt_keep {R Q S Y : Type} (pub : R → Q) (fst : S → Q) (b b' : S × Y)
    (h : fst b'.1 = fst b.1) (hb : onImageAt pub fst b) : onImageAt pub fst b' :=
  hb.imp fun _ e => h.trans e

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.seat_of_pass
#print axioms VerifiableInference.Desc.Sound.seat_of_same
#print axioms VerifiableInference.Desc.Sound.seat_of_goodIn
#print axioms VerifiableInference.Desc.Sound.seats_of_eachGoodIn
#print axioms VerifiableInference.Desc.Sound.seat_of_goodIn_own
#print axioms VerifiableInference.Desc.Sound.seat_between
#print axioms VerifiableInference.Desc.Sound.onImageAt_first
#print axioms VerifiableInference.Desc.Sound.onImageAt_keep
