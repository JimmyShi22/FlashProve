-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/Halves.lean: CONDITIONAL.

Not shown here. THAT A WORD OF THE HONEST PARTS READS AS THE LIBRARY's TERM: every field of
OpenedRight and of OpenedRightBack is a hypothesis HERE; laws for eleven of OpenedRight's fourteen
stand in Johnson/Road/K4/C/, Law/W/RightNorms.lean, Law/W/RightGated.lean and Law/W/EmbRight.lean,
each under hypotheses of its own. That the fields can hold together: no example is known. OpenedLeft
is a hypothesis here (Law/SlotsTrue.lean proves it, under K4Stand), and it is asked twice: in the
world behind "front" for Opened, in the world behind "back" for OpenedBack. SEVEN FIELDS HOLD NO
TERM OF THE LIBRARY (cl8, sqR, rt, sc, sel, sideA, sideB) AND ONE IS A HYPOTHESIS ON THE WITNESS
(emb): the docstrings say what each asks. FOR emb THE ONE LAW STANDS AT THE LIBRARY's OWN SIZES
ALONE: in the first group, at another plan, no example of OpenedRight can come by the laws named. By
a walk of import lines the closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass,
CmsGlue, CmsBcs, Cms, Bcs), through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or
Johnson/D/; under Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. Nothing on
soundness, on completeness or on any other property. No property is claimed.

The hypotheses `Opened` and `OpenedBack` (Johnson/Road/K4/W/Ground.lean) in two halves: `OpenedLeft`
(Law/SlotsTrue.lean: each slot is worth the reading of the honest part's own word) and
`OpenedRight`, typed here: the reading of each such word is the right side of Opened's field.

  `wSum`, `wSq`, `wProd`, `wLead8`, `wEnd8`, `wTerm`, `wStack`, `wLv1`, `wLv2`, `wEmb`   the honest
      parts' words, as OpenedLeft's right sides have them.
  `HalvesNums Q o D`   eight public facts.
  `OpenedRight Wd Q o w h ds D t`   one field for each field of Opened.
  `OpenedRightBack Wd Q o w h ds seen`   one field for each field of OpenedBack.
  `opened_of_halves`, `openedBack_of_halves`   the two halves give the whole.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Road.K4.W.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open Finset
open OnBytes (zeroE)
open OnBytes.Model (Reading World ledNS ledNP ledNO eqTab)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.Road (pt wHat pHat)
open OnBytes.Road.K4.W (Opened OpenedBack uEOf)
open OnBytes.Desc.First.K4 (k0)
open OnBytes.Desc.First.K4.Honest
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell bS xS led lF lFe slV upV slV' upV')
open Blocks (ext)

/-! ## 1 The honest parts' words -/

section Words
variable (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn)

/-- Sum number i of the norms. -/
def wSum (i : Nat) : OnBytes.E := (wSums Q w (ptsOf Q w (h ++ ds.take (k0 Q.g)))).getD i zeroE

/-- End value number e of the squares' product layer. -/
def wSq (e : Nat) : OnBytes.E :=
  endWord (jobSquares Q w (ptsOf Q w (h ++ ds.take (rJ1 Q.g)))) (ownE ds (rJ1 Q.g + 1) Q.P.rd.muV) e

/-- Row product number i. -/
def wProd (i : Nat) : OnBytes.E :=
  (rowProducts Q w (ptsOf Q w (h ++ ds.take (rowsRound Q.P Q.g)))).getD i zeroE

/-- The sum that the row products' sumcheck claims. -/
def wLead8 : OnBytes.E := leadWord (jobRows Q w (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g)))) 0

/-- End value number e of the row products' sumcheck. -/
def wEnd8 (e : Nat) : OnBytes.E :=
  endWord (jobRows Q w (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g))))
    (ownE ds (rJ2 Q.P Q.g + 1) Q.P.y.h.lt) e

/-- End value number e of the second token sumcheck. -/
def wTerm (e : Nat) : OnBytes.E :=
  endWord (jobTerms Q w (ptsOf Q w (h ++ ds.take (rJ3 Q.P Q.g))))
    (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt) e

/-- End value number e of the batched sumcheck. seen: the rounds shown in front of it. -/
def wStack (seen : Seen) (e : Nat) : OnBytes.E :=
  endWord (jobStack Q w (ptsOf Q w (h ++ ds.take (rJ4 Q.P Q.g))) (k4SentAt seen.rounds (k4TermsEnds Q)))
    (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS) e

/-- End value number e of the first product layer of the gated products. -/
def wLv1 (e : Nat) : OnBytes.E :=
  endWord (jobGated Q w (ptsOf Q w (h ++ ds.take (rJ5 Q.P Q.hp Q.g))))
    (ownE ds (rJ5 Q.P Q.hp Q.g + 1) Q.P.rd.muH) e

/-- End value number e of the second. -/
def wLv2 (e : Nat) : OnBytes.E :=
  endWord (jobGated2 Q w (ptsOf Q w (h ++ ds.take (rJ6 Q.P Q.hp Q.g))))
    (ownE ds (rJ6 Q.P Q.hp Q.g + 1) Q.P.rd.muH2) e

/-- The embedding's value. -/
def wEmb : OnBytes.E := embValue Q w (ptsOf Q w (h ++ ds.take (rE Q.P Q.hp Q.g)))

end Words

/-! ## 2 The hypotheses -/

/-- **Eight public facts**: an equation of layouts, one of groups, four numbers, two inequalities.
This defines a hypothesis; the definition claims nothing. -/
structure HalvesNums (Q : K4Pub) (o : Own) (D : Dim) : Prop where
  y : o.v.y = Q.P.y
  g : o.v.g = Q.g
  NI : Q.P.y.NI = D.nNu
  NS : ledNS Q.P.y.h.xl = 9
  NP : ledNP Q.P.y.h.xl = 7
  NO : ledNO Q.P.y.h.xl = 4
  ends : Q.P.y.NN * Q.P.y.Lam + Q.P.y.LamM + Q.P.y.LamM * Q.P.y.h.NE ≤ nEndT Q.P.y
  stack : 1 + (1 + Q.P.y.LamM) < nStack Q.P Q.hp Q.g

/-- **THE READING OF EACH HONEST WORD IS THE RIGHT SIDE OF Opened's FIELD**, one field for each. At
sums, prods, ends8, sqL, lv1L to lv2R that is a term of the library at the cells t. At cl8 and sqR
it is made of honest words again: an equation between these. At rt, sc, sel it is the worth of a
form in Wd's entries of the reads: the field says that the entries which the honest side has read
are Wd's, and that a form's worth at the end point is the extension of its worths at the corners. At
emb the word is the embedding claim's value on the committed matrix: the field follows where the
stream is the embedding of the tokens (the library's identity j11), and from nothing else that is
known. This defines a hypothesis; the definition claims nothing. -/
structure OpenedRight [scl : Scl] (Wd : World Cb.Gl.E) (Q : K4Pub) (o : Own) (w : K4In)
    (h ds : List Fmt.Drawn) (D : Dim) (t : Cell → Cb.Gl.E) : Prop where
  sums : ∀ ν, ν < D.nNu → ∀ s, s < 9 →
    Reading.gl.val (wSum Q w h ds (9 * ν + s)) = wHat D t ν (pt Reading.gl o.H.PV) s
  prods : ∀ ν, ν < D.nNu → ∀ j, j < 7 →
    Reading.gl.val (wProd Q w h ds (7 * ν + j)) = pHat D t ν (pt Reading.gl o.H.PV) j
  cl8 : Reading.gl.val (wLead8 Q w h ds) = ∑ i ∈ range (ledNP o.v.y.h.xl * o.v.y.NI),
    Reading.gl.val (o.H.omV.getD i zeroE) * Reading.gl.val (wProd Q w h ds i)
  ends8 : ∀ ν, ν < D.nNu →
    Reading.gl.val (wEnd8 Q w h ds (4 * ν + 0)) =
      ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) (pt Reading.gl o.H.tV.r) ∧
    Reading.gl.val (wEnd8 Q w h ds (4 * ν + 1)) =
      ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) (pt Reading.gl o.H.tV.r) ∧
    Reading.gl.val (wEnd8 Q w h ds (4 * ν + 2)) =
      ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) (pt Reading.gl o.H.tV.r) ∧
    Reading.gl.val (wEnd8 Q w h ds (4 * ν + 3)) =
      ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) (pt Reading.gl o.H.tV.r)
  sqL : Reading.gl.val (wSq Q w h ds 0) =
    ext (Q.P.rd.lNI + o.v.y.lPd - o.v.y.ls + o.v.y.ls + D.lT)
      (OnBytes.Road.K4.sqV o.v.y.NI (o.v.y.h.d / o.v.y.S2 * 2 ^ o.v.y.ls) o.v.y.lPd o.v.y.xb.nl
        D.lT (fun l => Reading.gl.val (o.H.gp.getD l zeroE)) (fun ν l j p => bS D t ν l j p))
      (pt Reading.gl o.H.wpl.r)
  sqR : Reading.gl.val (wSq Q w h ds 1) = Reading.gl.val (wSq Q w h ds 0)
  rt : ∀ i, i < o.v.y.NN * o.v.y.Lam → ∀ x, o.v.rowR "rt" i = some x →
    Reading.gl.val (wTerm Q w h ds i) = x.value Reading.gl Wd
  sc : ∀ lm, lm < o.v.y.LamM → ∀ x, o.v.shA "sc" "rt" lm 0 = some x →
    Reading.gl.val (wTerm Q w h ds (o.v.y.NN * o.v.y.Lam + lm)) = x.value Reading.gl Wd
  sel : ∀ i, i < o.v.y.LamM * o.v.y.h.NE → ∀ x,
    o.v.shA "sel" "rt" (i / o.v.y.h.NE) (i % o.v.y.h.NE) = some x →
    Reading.gl.val (wTerm Q w h ds (o.v.y.NN * o.v.y.Lam + o.v.y.LamM + i)) =
      x.value Reading.gl Wd
  lv1L : Reading.gl.val (wLv1 Q w h ds 0) =
    ext (D.lL + lF D + D.lT) (slV D t) (pt Reading.gl o.hd.r)
  lv1R : Reading.gl.val (wLv1 Q w h ds 1) =
    ext (D.lL + lF D + D.lT) (upV D t) (pt Reading.gl o.hd.r)
  lv2L : ∀ o2, o.hd2 = some o2 → Reading.gl.val (wLv2 Q w h ds 0) =
    ext (D.lL - 1 + lFe D + D.lT) (slV' D t) (pt Reading.gl o2.r)
  lv2R : ∀ o2, o.hd2 = some o2 → Reading.gl.val (wLv2 Q w h ds 1) =
    ext (D.lL - 1 + lFe D + D.lT) (upV' D t) (pt Reading.gl o2.r)
  emb : o.v.g = 0 → Reading.gl.val (wEmb Q w h ds) =
    ∑ kh ∈ range (o.v.y.h.d / o.v.y.S2), Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
      ∑ r ∈ range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
        ext D.lT (fun p => xS D t 0 (kh * 2 ^ o.v.y.ls + r) p) (uEOf Reading.gl o.v o.H)

/-- **The like for the two slots that "back" reads**: the worth of a form in Wd's entries of the
reads: both fields say that the entries which the honest side has read are Wd's. This defines a
hypothesis; the definition claims nothing. -/
structure OpenedRightBack (Wd : World Cb.Gl.E) (Q : K4Pub) (o : Own) (w : K4In)
    (h ds : List Fmt.Drawn) (seen : Seen) : Prop where
  sideA : Reading.gl.val (wStack Q w h ds seen 0) = o.K.fin.Alin.value Reading.gl Wd
  sideB : Reading.gl.val (wStack Q w h ds seen (1 + (1 + Q.P.y.LamM))) =
    o.K.fin.Blin.value Reading.gl Wd

/-! ## 3 The two halves give the whole -/

section
variable {Wd : World Cb.Gl.E} {Q : K4Pub} {o : Own} {w : K4In} {h ds : List Fmt.Drawn}
  {seen : Seen} {D : Dim} {t : Cell → Cb.Gl.E}

/-- **Opened from its two halves.** CONDITIONAL: on L, on every field of R, and on N. -/
theorem opened_of_halves [scl : Scl] (L : OpenedLeft Wd Q o w h ds seen)
    (R : OpenedRight Wd Q o w h ds D t) (N : HalvesNums Q o D) :
    Opened Reading.gl Wd Q.P o D t := by
  have hy := N.y
  have q0 := L.sq 0 (by omega)
  have q1 := L.sq 1 (by omega)
  have a0 := L.lv1 0 (by omega)
  have a1 := L.lv1 1 (by omega)
  rw [Nat.add_zero] at q0 a0
  have hE := N.ends
  exact
    { sums := fun ν hν s hs => by
        rw [Nat.add_assoc, L.sums (9 * ν + s) (by rw [N.NS, N.NI]; omega)]
        exact R.sums ν hν s hs
      prods := fun ν hν j hj => by
        rw [Nat.add_assoc, L.prods (7 * ν + j) (by rw [N.NP, N.NI]; omega)]
        exact R.prods ν hν j hj
      cl8 := by
        rw [L.cl8]
        refine R.cl8.trans (sum_congr rfl fun i hi => ?_)
        rw [L.prods i (by rw [← hy]; exact mem_range.mp hi)]
        rfl
      ends8 := fun ν hν => by
        obtain ⟨e0, e1, e2, e3⟩ := R.ends8 ν hν
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Nat.add_assoc, L.ends8 (4 * ν + 0) (by rw [N.NO, N.NI]; omega)]
          exact e0
        · rw [Nat.add_assoc, L.ends8 (4 * ν + 1) (by rw [N.NO, N.NI]; omega)]
          exact e1
        · rw [Nat.add_assoc, L.ends8 (4 * ν + 2) (by rw [N.NO, N.NI]; omega)]
          exact e2
        · rw [Nat.add_assoc, L.ends8 (4 * ν + 3) (by rw [N.NO, N.NI]; omega)]
          exact e3
      sqL := q0.trans R.sqL
      sqR := by
        rw [L.sR, q1, q0]
        exact R.sqR
      rt := fun tT hT i hi x hx => by
        rw [(L.terms tT hT).2 i (by rw [hy] at hi; omega)]
        exact R.rt i hi x hx
      sc := fun tT hT lm hl x hx => by
        rw [Nat.add_assoc,
          (L.terms tT hT).2 (o.v.y.NN * o.v.y.Lam + lm) (by rw [hy] at hl ⊢; omega)]
        exact R.sc lm hl x hx
      sel := fun tT hT i hi x hx => by
        rw [Nat.add_assoc, Nat.add_assoc, ← Nat.add_assoc (o.v.y.NN * o.v.y.Lam),
          (L.terms tT hT).2 (o.v.y.NN * o.v.y.Lam + o.v.y.LamM + i)
            (by rw [hy] at hi ⊢; omega)]
        exact R.sel i hi x hx
      lv1L := a0.trans R.lv1L
      lv1R := by
        rw [L.hR, a1]
        exact R.lv1R
      lv2L := fun o2 h2 => by
        have b0 := (L.lv2 o2 h2).2 0 (by omega)
        rw [Nat.add_zero] at b0
        exact b0.trans (R.lv2L o2 h2)
      lv2R := fun o2 h2 => by
        rw [(L.lv2 o2 h2).1, (L.lv2 o2 h2).2 1 (by omega)]
        exact R.lv2R o2 h2
      emb := fun h0 => by
        rw [L.emb (beq_iff_eq.mpr (N.g.symm.trans h0))]
        exact R.emb h0 }

/-- **OpenedBack from its two halves.** CONDITIONAL: on L, on both fields of R, and on N. -/
theorem openedBack_of_halves (L : OpenedLeft Wd Q o w h ds seen)
    (R : OpenedRightBack Wd Q o w h ds seen) (N : HalvesNums Q o D) :
    OpenedBack Reading.gl Wd o := by
  have s0 := L.stack 0 (by have := N.stack; omega)
  rw [Nat.add_zero] at s0
  exact
    { sideA := s0.trans R.sideA
      sideB := by
        rw [L.sB0, L.stack _ N.stack]
        exact R.sideB }

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.opened_of_halves
#print axioms ProofFile.Honest.K4.W.openedBack_of_halves
