-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/EndsBlindLm.lean: THE LOOKUP's END VALUES DO NOT READ THE LETTER lm ("the planes'
matrix has 2 ^ lm rows"): `Fo.endsOf h lm jLK rs` (OnBytes/Tie/Pv/Lookup/Forest/FoEnds.lean) IS ONE
VALUE AT EVERY lm; SO K3's PROMISE ON THE FIXED PART, `K3Ok hd lm jLK q`
(Johnson/Top/H/Keep/RunsPlain.lean), IS ONE SENTENCE AT EVERY lm. Statements and proofs.

Why. In the payers of K9's field AreadyS the letter lm is a free number: K3Ok is had at every lm;
while a comment in Johnson/Desc/First/Link/Law/SortLetters.lean says that at other numbers the
promise's third clause is, as far as can be seen there, false at an honest state. Were
both right, no honest state could meet the promise. The clause does not read lm:
Lean's kernel says so here.

How. `numsF h lm jLK θ` (FoV.lean) reads lm in ONE field, bAt (the places of the planes' cells).
None of the functions that endsOf's text names reads that field.
  `fac_b` … `traceOfFlat_b`: each of these functions of TwV (Cb/Pv/Lookup/Out/TwV.lean) gives the
    same at N and at { N with bAt := b }.
  `endsWithN h jLK rs N t`: endsOf's own text with the public numbers N and the trace t as letters:
    CUT BY PROGRAM out of FoEnds.lean. `endsOf_is`: endsOf IS it at forN and forTrace: by rfl: so
    Lean holds the cut against the text.
  `endsWithN_b`: it gives the same at N and at { N with bAt := b }.
  `endsOf_lm`: **endsOf h lm jLK rs = endsOf h lm' jLK rs.**
  `stood_lm`, `k3Ok_lm`: **Stood hd lm jLK q x ↔ Stood hd lm' jLK q x; K3Ok hd lm jLK q ↔ K3Ok hd
    lm' jLK q.**
WHAT IT DOES NOT SAY: jLK IS read (the ledgers' places; lvFirst): nothing here on jLK. The rows that
read bAt (rowEnd, rowBitE, rowNum) and the run "planes" do read lm: they are no part of K3Ok.
Limits. No soundness statement.

-/
import Johnson.Top.H.Keep.RunsPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open TwV FoNums Fo

section
variable {P K : Type} [CommRing K] (N : Nums P K) (b : ℕ → ℕ → P)

theorem fac_b (lam : K) : fac { N with bAt := b } lam = fac N lam := rfl

theorem tieS0_b (lam : K) (l : ℕ) (s : Sc K) :
    tieS0 { N with bAt := b } lam l s = tieS0 N lam l s := rfl

theorem tieInc_b : ∀ l : List (Sc K), tieInc { N with bAt := b } l = tieInc N l
  | [] => rfl
  | _ :: _ => rfl

theorem tieRowsR_b (lam : K) :
    ∀ l : List (Sc K), tieRowsR { N with bAt := b } lam l = tieRowsR N lam l
  | [] => rfl
  | s :: rest => by
    show rowU (N.ledTie rest.length) [3] s (tieInc { N with bAt := b } rest)
        (tieS0 { N with bAt := b } lam rest.length s) :: tieRowsR { N with bAt := b } lam rest =
      rowU (N.ledTie rest.length) [3] s (tieInc N rest) (tieS0 N lam rest.length s) ::
        tieRowsR N lam rest
    rw [tieRowsR_b lam rest, tieInc_b, tieS0_b]

theorem fK_b (t : Trace K) : fK { N with bAt := b } t = fK N t := rfl

theorem incT0_b (t : Trace K) : incT0 { N with bAt := b } t = incT0 N t := rfl

theorem tgT0_b (t : Trace K) : tgT0 { N with bAt := b } t = tgT0 N t := rfl

theorem rowBitU_b (t : Trace K) : rowBitU { N with bAt := b } t = rowBitU N t := rfl

omit [CommRing K] in
theorem dgE_b : dgE { N with bAt := b } = dgE N := rfl

theorem pntK_b (t : Trace K) : pntK { N with bAt := b } t = pntK N t := rfl

theorem traceOfFlat_b (rs : Rounds K) :
    traceOfFlat { N with bAt := b } rs = traceOfFlat N rs := rfl

end

section
variable {K : Type} [CommRing K]

/-- endsOf's own text, the public numbers and the trace as letters. -/
def endsWithN (h : Sh) (jLK : ℕ) (rs : Rounds K) (N : Nums _root_.Fo.Pl K) (t : Trace K) :
    Ends K :=
  let pnt := pntK N t
  let gam := byVar N.oE t.cls.xs
  { theta := thetaOf h rs
    alpha := t.lam
    a := fac N t.lam
    tieRows := (tieRowsR N t.lam t.tie.reverse).reverse
    keyRows := (lvRowsR N.ledK 0 (fK N t) t.keys.reverse).reverse
    tabRows := (lvRowsR N.ledT N.w (incT0 N t) t.tabl.reverse).reverse
    bitU := rowBitU N t
    lvEps := t.cls.eps
    lvFin := t.cls.fin
    lvXs := t.cls.xs
    lvZs := inRounds N.oE (pntTop N.oT t.join t.tabl.reverse)
    lvDg := dgE N
    lvInc := incTop N.ledT (incT0 N t) t.tabl.reverse
    lvTg := tgTop (tgT0 N t) t.tabl.reverse
    lvFirst := jLK + (S h).fEnd
    leavesA := ((List.range (2 ^ N.d)).map fun r => eqN (gam.drop N.w) r * (t.lam - 1 - N.tab
        r)).sum
    sBit := slotNo (N.ledB.sh 0)
    bitV := t.bits.v 0
    bitBe := t.bits.be
    zx := (pnt.drop h.rK).reverse
    zy := (pnt.take h.rK).reverse
    e := (List.range h.NC).map fun c =>
      (((List.range h.NT).filter fun y => co h y = c).map fun y => eqN (pnt.take h.rK) y).sum
    cEndF := scale (-1) (incTop N.ledK (fK N t) t.keys.reverse)
    cEndC := t.kT
    cEndInc := incTop N.ledK (fK N t) t.keys.reverse
    zb0 := gam.reverse
    zb1 := (byVar N.oB t.bits.xs).reverse
    tT := (List.range h.NC).map fun c =>
      ((List.range (2 ^ h.kT)).map fun r =>
        eqN ((gam.drop (FoNums.w + h.cK)).take h.kT) r * N.tab (r * 2 ^ h.cK + c)).sum -
          (c : K) * thetaOf h rs
    zk := (List.range h.NC).map fun c => (pnt.drop h.rK ++ pnt.take (io h c)).reverse }

/-- The cut is the text. -/
theorem endsOf_is (h : Sh) (lm jLK : ℕ) (rs : Rounds K) :
    endsOf h lm jLK rs = endsWithN h jLK rs (forN h lm jLK rs) (forTrace h lm jLK rs) := rfl

theorem endsWithN_b (h : Sh) (jLK : ℕ) (rs : Rounds K) (N : Nums _root_.Fo.Pl K)
    (b : ℕ → ℕ → _root_.Fo.Pl) (t : Trace K) :
    endsWithN h jLK rs { N with bAt := b } t = endsWithN h jLK rs N t := by
  unfold endsWithN
  simp only [fac_b, tieRowsR_b, fK_b, incT0_b, tgT0_b, rowBitU_b, dgE_b, pntK_b]

/-- **THE END VALUES DO NOT READ lm.** -/
theorem endsOf_lm (h : Sh) (lm lm' jLK : ℕ) (rs : Rounds K) :
    endsOf h lm jLK rs = endsOf h lm' jLK rs := by
  have eN : forN h lm jLK rs =
      { forN h lm' jLK rs with bAt := (forN h lm jLK rs).bAt } := rfl
  have eT : forTrace h lm jLK rs = forTrace h lm' jLK rs := by
    show traceOfFlat (forN h lm jLK rs) (afterShift h rs) =
      traceOfFlat (forN h lm' jLK rs) (afterShift h rs)
    rw [eN]
    exact traceOfFlat_b _ _ _
  rw [endsOf_is, endsOf_is, eT, eN]
  exact endsWithN_b _ _ _ _ _ _

end

section
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open Cb Cb.Fo Cb.Fo.PlaneClaims
open OnBytes.K.Kc
open VerifiableInference.Desc.K9L (Pub9)
open VerifiableInference.OnPublicFiles

variable {α : Type} (hd : α → Option Heard)

theorem stood_lm (lm lm' jLK : ℕ) (q : α × Option Pub9) (x : Heard × Rounds GE) :
    Stood hd lm jLK q x ↔ Stood hd lm' jLK q x := by
  unfold Stood
  rw [endsOf_lm x.1.shape lm lm' jLK x.2]

/-- **K3's PROMISE ON THE FIXED PART IS ONE SENTENCE AT EVERY lm.** -/
theorem k3Ok_lm (lm lm' jLK : ℕ) (q : α × Option Pub9) :
    K3Ok hd lm jLK q ↔ K3Ok hd lm' jLK q := by
  unfold K3Ok
  simp only [stood_lm hd lm lm' jLK]

end

end LPFK9

#print axioms LPFK9.fac_b
#print axioms LPFK9.tieS0_b
#print axioms LPFK9.tieInc_b
#print axioms LPFK9.tieRowsR_b
#print axioms LPFK9.fK_b
#print axioms LPFK9.incT0_b
#print axioms LPFK9.tgT0_b
#print axioms LPFK9.rowBitU_b
#print axioms LPFK9.dgE_b
#print axioms LPFK9.pntK_b
#print axioms LPFK9.traceOfFlat_b
#print axioms LPFK9.endsOf_is
#print axioms LPFK9.endsWithN_b
#print axioms LPFK9.endsOf_lm
#print axioms LPFK9.stood_lm
#print axioms LPFK9.k3Ok_lm
