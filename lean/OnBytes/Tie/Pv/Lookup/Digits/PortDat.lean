-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortDat.lean: the digits of a smallness test, as the verifier's own
record lays them, as a value of the record `CbQ.DatQ`; and a Bool test that gives that record's
laws.

A sub-proof's smallness test writes each tested number in a low and a high digit. The prover commits
to the digits in an array ZZ and to the bits of the lookup's counts in an array BZ. The lookup on
the digits numbers its keys and rows jointly for both digits. `CbQ.DatQ`
(Cb/Pv/Lookup/Digits/DatQ.lean) has that numbering as letters. Here the letters are computable terms
on `OnBytes.Model.HTailF2`, the verifier's record of a smallness test, and on its `Forest.Shape`.

Main names:
  `Counts`, `dgP_laid_of_counts`: over a variable record: the law `laid` from one count for each
    call.
  `testOK`, in five parts; `dgP_ok_of_parts`, `dgP_ok_of_test`: the test gives `DatOK`.
  `spread`, `spread_at`; `facE`, `rowEAt`, `rowBAt`, `rowNAt`, `pinTarget`: the three rows that read
    the planes, as functions of (joint row, plane).
  `Ent3`: an entry of a committed array: (array, row, column). `Pl tl`: a digit's place of one kind.
  `keyNo`, `posN`, `digAtN`: a digit's key number inside its call; its joint number; the way back.
  `padsP`: the public padding. `portQ tl`: the value.
Limits: the maps are written from the docstrings of OnBytes/Model/Forest.lean and Tail.lean. That
they are the verifier's is not shown here for a variable record: TestPortGuards.lean
[not in this library; so here read: not tested in this library] compares the verifier's own
coefficients with them, entry by entry, at one small shape. A digit's place is (column of the low
half of ZZ, combination), not (matrix, row of cells, combination): PortCols.lean carries the second
to the first. `Ent3` is an infinite type: a caller with a finite type of entries takes PortJ.lean.
Nothing on an honest prover.

-/
import Cb.Pv.Lookup.Digits.DatQ
import OnBytes.Tie.Pv.Lookup.Port.ShiftQPort
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open CbQ Cb.LdLkp Cb.Lkp Blocks

/-! ## Over a variable record of the digits -/

section
variable {I J : Type} [Fintype I] [DecidableEq I] (Q : DatQ I J)

/-- The counts from which «laid» follows: the calls' padding rows are apart; no other row has
padding; and, call by call, the joint keys of the call are its padding keys and its digits. -/
structure Counts : Prop where
  zInj : ∀ c < Q.nc, ∀ c' < Q.nc, Q.zRow c = Q.zRow c' → c = c'
  off  : ∀ u < 2 ^ Q.d, (∀ c < Q.nc, Q.zRow c ≠ u) → padCnt Q.pads u = 0
  cnt  : ∀ c < Q.nc, ((Finset.range (2 ^ Q.v)).filter fun X => Q.fK X = c).card =
           padCnt Q.pads (Q.zRow c) + (Finset.univ.filter fun p : Bool × I => Q.call p.1 = c).card

omit [DecidableEq I] in
theorem dgP_laid_of_counts
    (posLt : ∀ p, Q.pos p < 2 ^ Q.v) (inv : ∀ p, Q.digAt (Q.pos p) = some p)
    (inv' : ∀ X < 2 ^ Q.v, ∀ p, Q.digAt X = some p → Q.pos p = X)
    (callK : ∀ p, Q.fK (Q.pos p) = Q.call p.1) (kLt : ∀ X < 2 ^ Q.v, Q.fK X < Q.nc)
    (hC : Counts Q) :
    ∀ u < 2 ^ Q.d, padCnt Q.pads u =
      (((Finset.range (2 ^ Q.v)).filter fun X => Q.padB X = true).filter fun X => Q.zRow (Q.fK X) =
          u).card := by
  classical
  intro u hu
  by_cases hex : ∃ c, c < Q.nc ∧ Q.zRow c = u
  · obtain ⟨c, hc, rfl⟩ := hex
    have e1 : ((Finset.range (2 ^ Q.v)).filter fun X => Q.padB X = true).filter
          (fun X => Q.zRow (Q.fK X) = Q.zRow c) =
        ((Finset.range (2 ^ Q.v)).filter fun X => Q.fK X = c).filter fun X => Q.padB X = true := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, hC.zInj _ (kLt X h1) _ hc h3⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h3⟩, by rw [h2]⟩
    have e2 : (((Finset.range (2 ^ Q.v)).filter fun X => Q.fK X = c).filter fun X => ¬ Q.padB X =
        true) =
        (Finset.univ.filter fun p : Bool × I => Q.call p.1 = c).image Q.pos := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        cases hd : Q.digAt X with
        | none => exact absurd (by unfold DatQ.padB; rw [hd]; rfl) h3
        | some p =>
          have hp := inv' X h1 p hd
          exact ⟨p, by rw [← callK p, hp, h2], hp⟩
      · rintro ⟨p, hp, rfl⟩
        refine ⟨⟨posLt p, by rw [callK p, hp]⟩, ?_⟩
        unfold DatQ.padB
        rw [inv p]
        simp
    have hinj : Function.Injective Q.pos := fun p p' e =>
      Option.some.inj ((inv p).symm.trans ((congrArg Q.digAt e).trans (inv p')))
    have e3 := Finset.card_filter_add_card_filter_not
      (s := (Finset.range (2 ^ Q.v)).filter fun X => Q.fK X = c) (fun X => Q.padB X = true)
    rw [e2, Finset.card_image_of_injective _ hinj, hC.cnt c hc] at e3
    rw [e1]
    omega
  · have hno : ∀ c < Q.nc, Q.zRow c ≠ u := fun c hc e => hex ⟨c, hc, e⟩
    rw [hC.off u hu hno]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro X hX
    exact hno _ (kLt X (Finset.mem_range.1 (Finset.mem_filter.1 hX).1))

/-! The test, in five parts: a walk over the digits; over the joint keys; over the joint rows and
the
tables' values; over the calls; one count for each call. -/

def testDig : Bool :=
  decide (∀ p : Bool × I, Q.pos p < 2 ^ Q.v ∧ Q.digAt (Q.pos p) = some p ∧ Q.fK (Q.pos p) = Q.call
      p.1)
def testKey : Bool :=
  decide (∀ X < 2 ^ Q.v, (∀ p ∈ Q.digAt X, Q.pos p = X) ∧ Q.fK X < Q.nc)
omit [Fintype I] [DecidableEq I] in
def testRow (q H : ℕ) : Bool :=
  decide (∀ Y < 2 ^ Q.d, Q.fT Y < Q.nc ∧ (Q.fT Y = Q.call false → Q.rowV Y < q) ∧ (Q.fT Y = Q.call
      true → Q.rowV Y < H) ∧
    ((∀ c < Q.nc, Q.zRow c ≠ Y) → padCnt Q.pads Y = 0)) &&
  decide (∀ a < q, Q.rowOf (Q.call false) a < 2 ^ Q.d ∧ Q.fT (Q.rowOf (Q.call false) a) = Q.call
      false ∧
    Q.rowV (Q.rowOf (Q.call false) a) = a) &&
  decide (∀ a < H, Q.rowOf (Q.call true) a < 2 ^ Q.d ∧ Q.fT (Q.rowOf (Q.call true) a) = Q.call true
      ∧
    Q.rowV (Q.rowOf (Q.call true) a) = a)
omit [Fintype I] [DecidableEq I] in
def testCall (pp : ℕ) : Bool :=
  decide (∀ c < Q.nc, (Q.zRow c < 2 ^ Q.d ∧ Q.fT (Q.zRow c) = c ∧ Q.rowV (Q.zRow c) = 0) ∧ Q.tag c <
      pp ∧
    (∀ c' < Q.nc, Q.tag c = Q.tag c' → c = c') ∧ (∀ c' < Q.nc, Q.zRow c = Q.zRow c' → c = c')) &&
  padsOK Q.v Q.d Q.pads
def testCnt : Bool :=
  decide (∀ c < Q.nc, ((Finset.range (2 ^ Q.v)).filter fun X => Q.fK X = c).card =
    padCnt Q.pads (Q.zRow c) + (Finset.univ.filter fun p : Bool × I => Q.call p.1 = c).card)

/-- One Bool test for all of `DatOK`. -/
def testOK (q H pp : ℕ) : Bool := testDig Q && testKey Q && testRow Q q H && testCall Q pp &&
    testCnt Q

omit [DecidableEq I] in
/-- The laws from the parts: the three parts that walk over digits and joint keys as propositions,
so that they can be proved where a walk is too long; the two on rows and calls as Bool tests. -/
theorem dgP_ok_of_parts {q H pp : ℕ}
    (hp : ∀ p : Bool × I, Q.pos p < 2 ^ Q.v ∧ Q.digAt (Q.pos p) = some p ∧ Q.fK (Q.pos p) = Q.call
        p.1)
    (hX : ∀ X < 2 ^ Q.v, (∀ p ∈ Q.digAt X, Q.pos p = X) ∧ Q.fK X < Q.nc)
    (hcnt : ∀ c < Q.nc, ((Finset.range (2 ^ Q.v)).filter fun X => Q.fK X = c).card =
      padCnt Q.pads (Q.zRow c) + (Finset.univ.filter fun p : Bool × I => Q.call p.1 = c).card)
    (hR : testRow Q q H = true) (hCl : testCall Q pp = true) : Q.DatOK q H pp := by
  simp only [testRow, testCall, Bool.and_eq_true, decide_eq_true_eq] at hR hCl
  obtain ⟨⟨hY, hq⟩, hH⟩ := hR
  obtain ⟨hc, hpads⟩ := hCl
  have inv' : ∀ X < 2 ^ Q.v, ∀ p, Q.digAt X = some p → Q.pos p = X := fun X h1 p hd =>
    (hX X h1).1 p (Option.mem_def.2 hd)
  exact
    { posLt := fun p => (hp p).1, inv := fun p => (hp p).2.1, inv' := inv', callK := fun p => (hp
        p).2.2,
      kLt := fun X h1 => (hX X h1).2, tLt := fun Y h1 => (hY Y h1).1, rowLo := fun Y h1 => (hY Y
          h1).2.1,
      rowHi := fun Y h1 => (hY Y h1).2.2.1, ofLo := hq, ofHi := hH, zero := fun c h1 => (hc c h1).1,
      tagLt := fun c h1 => (hc c h1).2.1, tagInj := fun c h1 => (hc c h1).2.2.1, pads := hpads,
      laid := dgP_laid_of_counts Q (fun p => (hp p).1) (fun p => (hp p).2.1) inv' (fun p => (hp
          p).2.2)
        (fun X h1 => (hX X h1).2)
        { zInj := fun c h1 => (hc c h1).2.2.2, off := fun u h1 => (hY u h1).2.2.2, cnt := hcnt } }

/-- The test gives the laws. -/
theorem dgP_ok_of_test {q H pp : ℕ} (h : testOK Q q H pp = true) : Q.DatOK q H pp := by
  simp only [testOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact dgP_ok_of_parts Q (of_decide_eq_true h1) (of_decide_eq_true h2) (of_decide_eq_true h5) h3 h4

end

/-! ## The three rows that read the planes of the counts' bits -/

section
variable {I J E : Type} [Field E] (Q : DatQ I J)

/-- Coefficients a Y j (joint row Y, plane j < 2^w) laid at the planes' places, in the form of
`LkHeadF.numRowF` (Cb/Pv/Lookup/Blocks/HeadF.lean). -/
def spread [DecidableEq J] (w : ℕ) (a : ℕ → ℕ → E) : J → E := fun n =>
  ∑ Y ∈ Finset.range (2 ^ Q.d), ∑ j ∈ Finset.range (2 ^ w), if Q.bAt Y j = n then a Y j else 0

/-- Where the planes' places are apart, the spread form has at a place the coefficient that was laid
there. -/
theorem spread_at [DecidableEq J] (w : ℕ) (a : ℕ → ℕ → E)
    (hinj : ∀ Y < 2 ^ Q.d, ∀ j < 2 ^ w, ∀ Y' < 2 ^ Q.d, ∀ j' < 2 ^ w, Q.bAt Y j = Q.bAt Y' j' → Y =
        Y' ∧ j = j')
    (Y j : ℕ) (hY : Y < 2 ^ Q.d) (hj : j < 2 ^ w) : spread Q w a (Q.bAt Y j) = a Y j := by
  unfold spread
  rw [Finset.sum_eq_single Y, Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro j' hj' hne
    rw [if_neg fun e => hne (hinj Y hY j' (Finset.mem_range.1 hj') Y hY j hj e).2]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h
  · intro Y' hY' hne
    refine Finset.sum_eq_zero fun j' hj' => ?_
    rw [if_neg fun e => hne (hinj Y' (Finset.mem_range.1 hY') j' (Finset.mem_range.1 hj') Y hY j hj
        e).1]
  · intro h
    exact absurd (Finset.mem_range.2 hY) h

/-- The index of a bit: (joint row | plane). -/
def bitNo (w Y j : ℕ) : ℕ := Y * 2 ^ w + j

/-- The public factor of the row of the table's leaves: eps (alpha - 1 - the extension of the
shifted
joint table at the row's coordinates, the first d of the point). -/
def facE (eps al th : E) (pt : ℕ → E) : E :=
  eps * (al - 1 - ext Q.d (shTabQ Q.fT (Q.tab (E := E)) Q.tagE th) pt)

/-- The row of the table's leaves on the planes, at (Y, j): the factor times eq(pt, (Y | j)). -/
def rowEAt (w : ℕ) (eps al th : E) (pt : ℕ → E) (Y j : ℕ) : E :=
  facE Q eps al th pt * eqN (Q.d + w) 0 pt (bitNo w Y j)

/-- The bit test's end row on the planes, at (Y, j): eq(pt, (Y | j)). -/
def rowBAt (w : ℕ) (pt : ℕ → E) (Y j : ℕ) : E := eqN (Q.d + w) 0 pt (bitNo w Y j)

/-- The row that sums the counts, at (Y, j), and its target (those of `LkHeadF.numRowF`). -/
def rowNAt (_Y j : ℕ) : E := (2 : E) ^ j
def pinTarget : E := ((2 ^ Q.v - padNum Q.pads : ℕ) : E)

end

/-! ## The value at the verifier's own record -/

open OnBytes OnBytes.Model

/-- An entry of a committed array: (the array's number in the sub-proof's list, row, column). -/
abbrev Ent3 : Type := ℕ × ℕ × ℕ

/-- A digit's place of one kind: (column of a half of ZZ, combination). -/
abbrev Pl (tl : HTailF2) : Type := Fin tl.mz × Fin tl.tau

def qOf (b : Bool) : ℕ := if b then 1 else 0

/-- The pieces of call q, as a list. -/
def piecesL (tl : HTailF2) (q : ℕ) : List Piece := (tl.zOf q).pieces.toList

/-- The piece of call q whose rows hold the combination u (`Piece`, OnBytes/Model/Forest.lean). -/
def pieceAt (tl : HTailF2) (q u : ℕ) : Option Piece :=
  (piecesL tl q).find? fun p => decide (p.r0 ≤ u) && decide (u < p.r0 + p.Rp)

/-- The key's number inside its call: off + r CP + c (the docstring of `Piece`). -/
def inP (p : Piece) (c u : ℕ) : ℕ := p.off + (c + p.CP * (u - p.r0))
def keyNo (tl : HTailF2) (q c u : ℕ) : ℕ := ((pieceAt tl q u).map fun p => inP p c u).getD 0

/-- The joint key's number of key kn of call q: (the place in a tree | the tree's number), as
the head of OnBytes/Model/Forest.lean has it; it is `Port.keyP` read backwards. -/
def posK (h : Port.Sh) (q kn : ℕ) : ℕ := (Port.fst h q + kn / 2 ^ h.dT) + 2 ^ h.rK * (kn % 2 ^ h.dT)
def posN (tl : HTailF2) (q c u : ℕ) : ℕ := posK tl.f9 q (keyNo tl q c u)

/-- Backwards: the tree's number; the key's number inside its call; the piece that holds it; the
digit. -/
def treeOf (h : Port.Sh) (X : ℕ) : ℕ := X % 2 ^ h.rK
def knOf (h : Port.Sh) (X : ℕ) : ℕ :=
  X / 2 ^ h.rK + 2 ^ h.dT * (treeOf h X - Port.fst h (Port.co h (treeOf h X)))
def pieceK (tl : HTailF2) (q kn : ℕ) : Option Piece :=
  (piecesL tl q).find? fun p => decide (p.off ≤ kn) && decide (kn < p.off + 2 ^ p.b)
def cut (p : Piece) (q kn : ℕ) : Option (ℕ × ℕ × ℕ) :=
  if (kn - p.off) / p.CP < p.Rp ∧ (kn - p.off) % p.CP < p.Cp then
    some (q, (kn - p.off) % p.CP, p.r0 + (kn - p.off) / p.CP)
  else none

/-- posN's inverse, on numbers. none: a padding place. -/
def digAtN (tl : HTailF2) (X : ℕ) : Option (ℕ × ℕ × ℕ) :=
  if treeOf tl.f9 X < tl.f9.NT then
    (pieceK tl (Port.co tl.f9 (treeOf tl.f9 X)) (knOf tl.f9 X)).bind fun p =>
      cut p (Port.co tl.f9 (treeOf tl.f9 X)) (knOf tl.f9 X)
  else none

def digAtP (tl : HTailF2) (X : ℕ) : Option (Bool × Pl tl) :=
  match digAtN tl X with
  | some (q, c, u) =>
    if h1 : c < tl.mz then if h2 : u < tl.tau then some (q == 1, ⟨c, h1⟩, ⟨u, h2⟩) else none else
        none
  | none => none

/-- There are 2^5 planes (`linBits9`, OnBytes/Model/Tail.lean, weighs column u by 2^(u % 32)). -/
def wP : ℕ := 5

/-- The public padding by call: row t0 of call c, in the joint numbering; the padding keys of c's
trees, and for call 0 those of the trees of padding alone. -/
def padsP (h : Port.Sh) : List (ℕ × ℕ) :=
  (List.range h.NC).map fun c =>
    (c + 2 ^ h.cK * Port.t0Of h c,
      (((List.range h.NT).filter fun y => Port.co h y = c).map fun y => h.pub.getD y 0).sum +
        if c = 0 then h.emptyKeys else 0)

/-- The record of the digits at the verifier's own record of a smallness test. -/
def portQ (tl : HTailF2) : DatQ (Pl tl) Ent3 where
  lo := fun i => (tl.ix.ZZ, i.2.val, i.1.val)
  hi := fun i => (tl.ix.ZZ, i.2.val, tl.mz + i.1.val)
  v := tl.f9.v
  d := tl.f9.d
  nc := tl.f9.NC
  call := qOf
  pos := fun p => posN tl (qOf p.1) p.2.1.val p.2.2.val
  digAt := digAtP tl
  fK := Port.fK tl.f9
  fT := Port.fT tl.f9
  rowV := fun Y => Y / 2 ^ tl.f9.cK % 2 ^ Port.kOf tl.f9 (Port.fT tl.f9 Y)
  tag := fun c => c
  rowOf := fun c a => a * 2 ^ tl.f9.cK + c
  zRow := fun c => c + 2 ^ tl.f9.cK * Port.t0Of tl.f9 c
  bAt := fun Y j => (tl.ix.BZ, bitNo wP Y j / tl.bzColumns, bitNo wP Y j % tl.bzColumns)
  pads := padsP tl.f9

#print axioms dgP_laid_of_counts
#print axioms dgP_ok_of_parts
#print axioms dgP_ok_of_test
#print axioms spread_at

end OnBytes.DgP
