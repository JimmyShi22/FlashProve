-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttBetween.lean: names for what lies between the claims of an attention sub-proof
and the relation of the attention segment. Definitions alone.

Main definitions.
 - Units, slotOf, slotVal: the slot of each named scalar of the key forms (the library's KSc), and
   its hidden value in a world.
 - Linear: the named scalars that a single claim ties to a table.
 - EndsAt: both end values of every pair of a sumcheck of products are the library's maps.
 - ScorePub, ProductPub, BelowPub: the public premises of the statements of
   Johnson/Road/Rows/AttEnds14.lean, for all pairs of a sumcheck at once.
 - ScoreGiven, ProductGiven, BelowGiven: for each pair, the forms have been made and the two claims
   on the end values have the value 0.

What this file does not claim. It holds no theorem. None of these statements is shown to hold of a
run. Nothing is said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttEnds14

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork HTailF2 eqTab blockRows ofNat)
open OnBytes.Attention (Heard Score ScoreTables PlaneClaim PW Seg Sc3 sc3A sc3B readHead readGroup
  readDenominator plane tok scoreTiles tileSums lastCoords lastN pointM)
open Inst.Model.AttSeg (Calls Pub Step Aext Bext KSc Fam Reg rv sumPhi rd2 eqT wp yg yi denV EF
  Idn idnVal keyVec lutSet lut castT)

variable {K : Type} [Field K]

/-! ## The named scalars -/

/-- The four units of the calls of kinds KR and KFD, where each segment has one unit: the plane
claims of the segments rm and rd, and the units of the scores of the segments fm and fd with their
tables. -/
structure Units where
  /-- the plane claim of segment rm -/
  pM : PlaneClaim
  /-- the plane claim of segment rd -/
  pD : PlaneClaim
  /-- the unit of segment fm -/
  kM : Score
  /-- the unit of segment fd -/
  kD : Score
  /-- the tables of the unit of segment fm -/
  tM : ScoreTables
  /-- the tables of the unit of segment fd -/
  tD : ScoreTables

/-- The slot of a named scalar of the key forms. A name that the library's list does not hold gets
the slot 0. -/
def slotOf (h : Heard) (u : Units) : KSc → ℕ
  | .cell .m1 jj => u.pM.s0 + jj
  | .cell .d1 jj => u.pD.s0 + jj
  | .cell .m2 jj => u.kM.s0 + jj
  | .cell .d2 jj => u.kD.s0 + jj
  | .cell _ _ => 0
  | .ms .M => u.kM.s0 + 5
  | .ms .D => u.kD.s0 + 5
  | .ss .M => u.kM.s0 + 6
  | .ss .D => u.kD.s0 + 6
  | .acc => h.d.sACC
  | .zo => h.d.sZO
  | .zc => h.d.sZC
  | .rh => h.d.sRH
  | .rh' => h.d.sRHP
  | .ib k => h.d.sIB + k
  | .rg => h.d.s5h
  | .rg' => h.d.s5h + 1

/-- The hidden value of a named scalar in a world. -/
def slotVal (W : World K) (h : Heard) (u : Units) (k : KSc) : K := W.slot (slotOf h u k)

/-- The named scalars that one claim ties to a table: all but the two scores, the denominator times
the output, and the accumulator. -/
def Linear : KSc → Prop
  | .ss _ => False
  | .zo => False
  | .acc => False
  | _ => True

/-! ## The end values of a sumcheck of products -/

/-- Both end values of every pair are the library's maps of step st at the sumcheck's point. -/
def EndsAt (ρ : Reading K) (W : World K) (h : Heard) (M : Mats K) (C : Calls) (p : Pub K)
    (sc : Sc3) (st : Step) : Prop :=
  ∀ b < h.S.NP,
    W.slot (sc.sEnd + 2 * b) = Aext (L5.dimOf h.S) C p (cellsK h.S M) st b (pt ρ sc.r) ∧
      W.slot (sc.sEnd + (2 * b + 1)) = Bext (L5.dimOf h.S) C p (cellsK h.S M) st b (pt ρ sc.r)

/-- The public premises of ScoreEnd, for a unit k of segment seg with the tables tb. -/
structure ScorePub (ρ : Reading K) (tl : HTailF2) (h : Heard) (C : Calls) (p : Pub K) (seg : Seg)
    (k : Score) (tb : ScoreTables) : Prop where
  /-- the unit's segment -/
  isSeg : k.seg = seg
  /-- the length of the sumcheck's point -/
  r : k.sc.r.size = h.S.nvKF seg
  /-- the length of the point on the rows of a tile -/
  zi : k.zi.size = h.S.cf.lB
  /-- the length of the point on the columns of a tile -/
  zj : k.zj.size = h.S.cf.lB
  /-- piece b is pair b -/
  pairs : PiecesAll h.S k.pw
  /-- the point on the rows of a tile is the library's -/
  vi : ∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j
  /-- the point on the columns of a tile is the library's -/
  vj : ∀ j < h.S.cf.lB, pt ρ k.zj j = Inst.Model.AttSeg.zj' (L5.dimOf h.S) C p.z j
  /-- the table on the queries -/
  tQ : TabAt tl h tb.tQ (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
    (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).1 k.zi))
  /-- the table on the keys -/
  tK : TabAt tl h tb.tK (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
    (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).2 k.zj))

/-- For each piece of the unit: the two forms have been made, and the two claims on the end values
have the value 0. -/
def ScoreGiven (ρ : Reading K) (W : World K) (K3 : ℕ) (h : Heard) (k : Score) (tb : ScoreTables) :
    Prop :=
  ∀ b w, k.pw[b]? = some w → ∃ (q kx : Aff) (F F' G G' : Fork) (c c1 c' c1' : Ctx),
    Cols F h K3 ∧ Cols F' h K3 ∧
    (readHead h tb.tQ h.S.atQ k.sc.r (lastCoords k.sc.r h.S.cf.ldh) w.lam w.a F).Yields c (q, G)
      c1 ∧
    (readGroup h tb.tK h.S.atK k.sc.r (lastCoords k.sc.r h.S.cf.ldh) w.lam F').Yields c' (kx, G')
      c1' ∧
    (sc3A k.sc b - q).value ρ W = 0 ∧ (sc3B k.sc b - kx).value ρ W = 0

/-- The public premises of ProductEnd. -/
structure ProductPub (ρ : Reading K) (tl : HTailF2) (h : Heard) (C : Calls) (p : Pub K) :
    Prop where
  /-- the length of the sumcheck's point -/
  r : h.d.scE.r.size = h.S.nvE
  /-- the length of the point on the features -/
  zc : h.d.zcW.size = h.S.cf.ldh
  /-- piece b is pair b -/
  pairs : PiecesAll h.S h.d.pwW
  /-- the point on the features is the library's -/
  vn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j
  /-- the table on the denominators -/
  hE : TabAt tl h h.t.hE h.S.cf.NAs h.S.T
    (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt)))
  /-- the table on the outputs -/
  qO : TabAt tl h h.t.qO (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
    (blockRows (lowOf h.S h.d.zcW)
      (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))))

/-- For each piece of segment wl: the two forms of ProductEnd have been made, and the two claims
have the value 0. -/
def ProductGiven (ρ : Reading K) (W : World K) (K3 : ℕ) (h : Heard) : Prop :=
  ∀ b w, h.d.pwW[b]? = some w → ∃ (z o : Aff) (F F' G G' : Fork) (c c1 c' c1' : Ctx),
    Cols F h K3 ∧ Cols F' h K3 ∧
    (readDenominator h h.t.hE h.d.scE.r w.lam w.a F).Yields c (z, G) c1 ∧
    (readHead h h.t.qO h.S.atO h.d.scE.r h.d.zcW w.lam w.a F').Yields c' (o, G') c1' ∧
    (sc3A h.d.scE b - z).value ρ W = 0 ∧ (sc3B h.d.scE b - o).value ρ W = 0

/-- The public premises of ValueBelowEnd that ProductPub does not hold. -/
structure BelowPub (ρ : Reading K) (tl : HTailF2) (h : Heard) (C : Calls) (p : Pub K) :
    Prop where
  /-- the length of the sumcheck's point -/
  r : h.d.vpm.r.size = h.S.nvVM
  /-- the length of the point on the tokens -/
  zi : h.d.ziW.size = h.S.cf.lt
  /-- the point at which the softmax weights are read -/
  ptM : h.t.ptM = pointM h.S h.d
  /-- the weights of the tile columns -/
  wJv : h.d.wJv = (tileSums h.S
    (eqTab (h.d.vpm.r.extract h.S.cf.lgk (h.S.cf.lgk + (h.S.lnT - 1))))
    (eqTab (h.d.vpm.r.extract (h.S.cf.lgk + (h.S.lnT - 1))
      (h.S.cf.lgk + (h.S.lnT - 1) + h.S.lnT)))).2
  /-- the point on the rows of a tile is the library's -/
  vi : ∀ j < h.S.cf.lB, pt ρ (h.d.zilo h.S) j = Inst.Model.AttSeg.yi' (L5.dimOf h.S) C p.z j
  /-- the drawn element is the library's -/
  gam : ρ.val h.d.gam = p.th
  /-- the table on the softmax weights -/
  tVM : AsAt h h.t.tVM (lastN h.t.ptM h.S.cf.lmS)
  /-- the table on the values -/
  qVM : TabAt tl h h.t.qVM (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
    (blockRows (lowOf h.S h.d.zcW) (tok h.S h.d.wJv (lastCoords h.d.vpm.r h.S.cf.lB)))

/-- For each piece of segment wl: the three forms of ValueBelowEnd have been made, and the two
claims have the value 0. -/
def BelowGiven (ρ : Reading K) (W : World K) (K3 : ℕ) (h : Heard) : Prop :=
  ∀ b w, h.d.pwW[b]? = some w →
    ∃ (p3 p4 v : Aff) (F F' F'' G G' G'' : Fork) (c c1 c' c1' c'' c1'' : Ctx),
    Cols F h K3 ∧ Cols F' h K3 ∧ Cols F'' h K3 ∧
    (plane h h.t.tVM 3 w.lam w.a h.t.ptM false F).Yields c (p3, G) c1 ∧
    (plane h h.t.tVM 4 w.lam w.a h.t.ptM false F').Yields c' (p4, G') c1' ∧
    (readGroup h h.t.qVM h.S.atV h.d.vpm.r h.d.zcW w.lam F'').Yields c'' (v, G'') c1'' ∧
    (sc3A h.d.vpm b - (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256))).value ρ W = 0 ∧
    (sc3B h.d.vpm b - (Aff.ofConst h.d.gam + v)).value ρ W = 0

end OnBytes.Road.Rows
