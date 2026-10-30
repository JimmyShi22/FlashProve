-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds14.lean: the end values of the first four sumchecks of the attention
sub-proof, said on cells. Statements alone.

The attention sub-proof runs eight kinds of sumcheck (OnBytes/Model/Attention.lean: hear). In the
order of the run the first four are: the score of a unit below the diagonal; the score of a unit
on the diagonal (OnBytes/Model/AttentionScores.lean: scoreUnit); the denominator times the output;
the value product below the diagonal (OnBytes/Model/AttentionDivide.lean: productIn, valueBelowIn).
Each is a sumcheck of products: for each pair b it leaves two end values, under the slots
sEnd + 2 b and sEnd + 2 b + 1. For each end value the verifier adds one claim: the end value minus
a form on a table is 0 (endValues; endValuesE; valueProduct).

The library has the same four sumchecks as definitions on the cells of an attention segment
(Inst/Model/Att/Sums.lean): the steps s6b, s6d, s8, s11, with the maps Acube and Bcube on the cube
and their multilinear extensions Aext and Bext.

Each statement here says, for one kind: in a world in which every table is true of the matrices, if
the two claims on the end values of a pair have the value 0, then the two end values are Aext and
Bext of that step, on the cells of the matrices, at the sumcheck's point of challenges.

Main definitions: ScoreEnd, ScoreFmEnd, ScoreFdEnd, ProductEnd, ValueBelowEnd.

What a statement takes as given, beside the setting (AttAt in Johnson/Road/Rows/AttRead.lean):
 - the lengths of the points, all public;
 - that the points which the verifier has cut from the lookup's point are the library's (zi', zj',
   yi', yn), coordinate by coordinate, and that the drawn element gam is the library's th;
 - that the tables which the claims read lie in the list with the weights that
   OnBytes/Model/AttentionTables.lean (placeAll) gives them;
 - that the functions which make the forms have returned, each from a state of its own in which the
   vector of tables has its columns (Cols).

What this file does not claim. It holds no theorem: each statement is a definition of type Prop.
Nothing is said about probabilities, about the rounds of a sumcheck, about its row, or about hiding.
The program does not import this file.


-/
import Johnson.Road.Rows.AttRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Model (Reading World Aff Fork HTailF2 eqTab blockRows ofNat)
open OnBytes.Attention (Heard Score ScoreTables PW Seg sc3A sc3B readHead readGroup
  readDenominator plane tok scoreTiles tileSums lastCoords lastN pointM)
open Inst.Model.AttSeg (Calls Pub Step Aext Bext)

/-! ## The scores -/

/-- The end values of the sumcheck of one unit of the scores. seg: the unit's segment; st: the
library's step. w is piece number b of the unit; its pair has the number w.lam HA + w.a. -/
def ScoreEnd (seg : Seg) (st : Step) : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (C : Calls) (p : Pub K) (k : Score) (tb : ScoreTables) (b : ℕ) (w : PW)
    (q kx : Aff) (F F' G G' : Fork) (c c1 c' c1' : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 → Cols F' h K3 →
    k.seg = seg → k.sc.r.size = h.S.nvKF seg →
    k.zi.size = h.S.cf.lB → k.zj.size = h.S.cf.lB → w.a < h.S.HA →
    (∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j) →
    (∀ j < h.S.cf.lB, pt ρ k.zj j = Inst.Model.AttSeg.zj' (L5.dimOf h.S) C p.z j) →
    TabAt tl h tb.tQ (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).1 k.zi)) →
    TabAt tl h tb.tK (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).2 k.zj)) →
    (readHead h tb.tQ h.S.atQ k.sc.r (lastCoords k.sc.r h.S.cf.ldh) w.lam w.a F).Yields c (q, G)
      c1 →
    (readGroup h tb.tK h.S.atK k.sc.r (lastCoords k.sc.r h.S.cf.ldh) w.lam F').Yields c' (kx, G')
      c1' →
    (sc3A k.sc b - q).value ρ W = 0 →
    (sc3B k.sc b - kx).value ρ W = 0 →
    W.slot (k.sc.sEnd + 2 * b) =
        Aext (L5.dimOf h.S) C p (cellsK h.S M) st (w.lam * h.S.HA + w.a) (pt ρ k.sc.r) ∧
      W.slot (k.sc.sEnd + (2 * b + 1)) =
        Bext (L5.dimOf h.S) C p (cellsK h.S M) st (w.lam * h.S.HA + w.a) (pt ρ k.sc.r)

/-- The score of a unit below the diagonal: its end values are the query and the key of the
library's step s6b. -/
def ScoreFmEnd : Prop := ScoreEnd .fm .s6b

/-- The score of a unit on the diagonal: its end values are the query and the key of the library's
step s6d. -/
def ScoreFdEnd : Prop := ScoreEnd .fd .s6d

/-! ## The denominator times the output -/

/-- The end values of the sumcheck for the denominator times the output are the denominator and the
output of the library's step s8. w is piece number b of segment wl. -/
def ProductEnd : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (C : Calls) (p : Pub K) (b : ℕ) (w : PW)
    (z o : Aff) (F F' G G' : Fork) (c c1 c' c1' : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 → Cols F' h K3 →
    h.d.scE.r.size = h.S.nvE → h.d.zcW.size = h.S.cf.ldh → w.a < h.S.HA →
    (∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j) →
    TabAt tl h h.t.hE h.S.cf.NAs h.S.T
      (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))) →
    TabAt tl h h.t.qO (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S h.d.zcW)
        (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt)))) →
    (readDenominator h h.t.hE h.d.scE.r w.lam w.a F).Yields c (z, G) c1 →
    (readHead h h.t.qO h.S.atO h.d.scE.r h.d.zcW w.lam w.a F').Yields c' (o, G') c1' →
    (sc3A h.d.scE b - z).value ρ W = 0 →
    (sc3B h.d.scE b - o).value ρ W = 0 →
    W.slot (h.d.scE.sEnd + 2 * b) =
        Aext (L5.dimOf h.S) C p (cellsK h.S M) .s8 (w.lam * h.S.HA + w.a) (pt ρ h.d.scE.r) ∧
      W.slot (h.d.scE.sEnd + (2 * b + 1)) =
        Bext (L5.dimOf h.S) C p (cellsK h.S M) .s8 (w.lam * h.S.HA + w.a) (pt ρ h.d.scE.r)

/-! ## The value product below the diagonal -/

/-- The end values of the value product's sumcheck below the diagonal are the softmax weight, and
gam plus the value, of the library's step s11. w is piece number b of segment wl. -/
def ValueBelowEnd : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (C : Calls) (p : Pub K) (b : ℕ) (w : PW)
    (p3 p4 v : Aff) (F F' F'' G G' G'' : Fork) (c c1 c' c1' c'' c1'' : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 → Cols F' h K3 → Cols F'' h K3 →
    h.d.vpm.r.size = h.S.nvVM → h.d.ziW.size = h.S.cf.lt → h.d.zcW.size = h.S.cf.ldh →
    w.a < h.S.HA →
    h.t.ptM = pointM h.S h.d →
    h.d.wJv = (tileSums h.S
      (eqTab (h.d.vpm.r.extract h.S.cf.lgk (h.S.cf.lgk + (h.S.lnT - 1))))
      (eqTab (h.d.vpm.r.extract (h.S.cf.lgk + (h.S.lnT - 1))
        (h.S.cf.lgk + (h.S.lnT - 1) + h.S.lnT)))).2 →
    (∀ j < h.S.cf.lB, pt ρ (h.d.zilo h.S) j = Inst.Model.AttSeg.yi' (L5.dimOf h.S) C p.z j) →
    (∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j) →
    ρ.val h.d.gam = p.th →
    AsAt h h.t.tVM (lastN h.t.ptM h.S.cf.lmS) →
    TabAt tl h h.t.qVM (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
      (blockRows (lowOf h.S h.d.zcW) (tok h.S h.d.wJv (lastCoords h.d.vpm.r h.S.cf.lB))) →
    (plane h h.t.tVM 3 w.lam w.a h.t.ptM false F).Yields c (p3, G) c1 →
    (plane h h.t.tVM 4 w.lam w.a h.t.ptM false F').Yields c' (p4, G') c1' →
    (readGroup h h.t.qVM h.S.atV h.d.vpm.r h.d.zcW w.lam F'').Yields c'' (v, G'') c1'' →
    (sc3A h.d.vpm b - (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256))).value ρ W = 0 →
    (sc3B h.d.vpm b - (Aff.ofConst h.d.gam + v)).value ρ W = 0 →
    W.slot (h.d.vpm.sEnd + 2 * b) =
        Aext (L5.dimOf h.S) C p (cellsK h.S M) .s11 (w.lam * h.S.HA + w.a) (pt ρ h.d.vpm.r) ∧
      W.slot (h.d.vpm.sEnd + (2 * b + 1)) =
        Bext (L5.dimOf h.S) C p (cellsK h.S M) .s11 (w.lam * h.S.HA + w.a) (pt ρ h.d.vpm.r)

end OnBytes.Road.Rows
