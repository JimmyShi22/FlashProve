-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds58.lean: the end values of the last four sumchecks of the attention
sub-proof, said on cells. Statements alone.

The attention sub-proof runs eight kinds of sumcheck (OnBytes/Model/Attention.lean: hear). In the
order of the run the last four are: the value product on the diagonal tiles; the score at the index;
the key at the index; the bits of the index (OnBytes/Model/AttentionDivide.lean: valueOnIn,
scoreAtIndexIn, keyAtIndexIn, bitsIn). A sumcheck ends in hidden end values. The verifier ties each
of them down by a claim: an affine form, in the end value's slot and in entries of tables, that must
be 0 (OnBytes/Model/AttentionClaimsB.lean: claims 6, 7 and 8).

The library has the same four sumchecks as definitions on the cells of an attention segment: the
steps s12, s16 and s21 with the maps Aext and Bext (Inst/Model/Att/Sums.lean), and step 18, whose
end values are rvKC and rvIBP (Inst/Model/Att/KeyForms.lean). rvM6 there is the value from which the
score at the index starts.

There is one statement for each claim. It says: in a world in which every table is true of the
matrices, if the verifier's form has the value 0, then the hidden value under the claim's slot is
the library's, on the cells of the matrices, at the verifier's own points. Each statement has its
own state F, in which the claim's form is made: the verifier adds claims between two forms, and
that changes the state.

The bits. The library takes as many bits for "which bit" as the number of bits of a position needs
(lK); the verifier always takes 4. The two agree for requests of 2^9 to 2^16 tokens. So the maps of
that sumcheck are written for any number kap of such bits (bitCube in
Cb/Pv/Att/Bits.lean); at kap = lK they are the library's, by definition, and the
statements here are at the verifier's 4.

Main definitions: QaAt, AhAt, bitsForm; ValueOnEndA, ValueOnEndB, ScoreStartEnd,
ScoreAtIndexEnd, KeyAtIndexEndK, KeyAtIndexEndB, BitsEndA, BitsEndB.

What a statement takes as given, beside the setting (AttAt in Johnson/Road/Rows/AttRead.lean):
 - the lengths of the points, all public;
 - that the points which the verifier holds are the library's, coordinate by coordinate (yi', yn,
   tg, ti, fn), and that the drawn element gam is the library's th;
 - that the table which the claim reads lies in the list with the weights that
   OnBytes/Model/AttentionTables.lean (placeAll) gives it;
 - that the function which makes the form has returned;
 - in ValueOnEndA: a column of the matrix as is not longer than a plane on the diagonal tiles (the
   verifier's function shape tests it: af-shape-lmS).

What this file does not claim. It holds no theorem: each statement is a definition of type Prop.
Nothing is said about probabilities, about the rounds of a sumcheck, about its row, or about hiding.
The second end values of the score at the index are tied down by no claim: they are the start of the
sumcheck for the key at the index. The program does not import this file.


-/
import Johnson.Road.Rows.AttRead
import Cb.Pv.Att.Bits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open OnBytes.Model (Reading World Aff Fork SubM HTailF2 eqTab blockRows ofNat)
open OnBytes.Attention (Heard PW sc3A sc3B plane readHead readGroup readIndexBit readMaximum tok
  lastCoords lastN pointD minusOne)
open Inst.Model.AttSeg (Calls Pub Step Aext Bext rvM6 rvKC rvIBP)

/-- A table on blocks of features of qa begins at entry t: blocks of 2^la rows, weighted by the last
ls coordinates of the point zc on the features of a head and by the token weights ptk. -/
def QaAt (tl : HTailF2) (h : Heard) (t : ℕ) (zc ptk : Array E) : Prop :=
  TabAt tl h t (h.S.cf.NAs + 3) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) ptk)

/-- A table on ah begins at entry t: blocks of T rows, weighted by the token weights psi. -/
def AhAt (tl : HTailF2) (h : Heard) (t : ℕ) (psi : Array E) : Prop :=
  TabAt tl h t h.S.cf.NAs h.S.T psi

/-! ## The value product on the diagonal tiles -/

/-- The first end value of a pair in the value product's sumcheck on the diagonal tiles is the
softmax weight of the library's step s12. b: the number of the pair's piece in segment wl; w: the
piece. -/
def ValueOnEndA : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (F : Fork) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (C : Calls) (p : Pub K) (b : ℕ) (w : PW) (p3 p4 : Aff) (G G' : Fork) (c c1 c' c1' : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 →
    h.d.vpd.r.size = h.S.nvVD → h.d.ziW.size = h.S.cf.lt →
    w.a < h.S.HA →
    h.S.cf.lmS ≤ h.S.nD →
    h.t.ptD = pointD h.S h.d →
    (∀ j < h.S.cf.lB, pt ρ (h.d.zilo h.S) j = Inst.Model.AttSeg.yi' (L5.dimOf h.S) C p.z j) →
    AsAt h h.t.tVD (lastN h.t.ptD h.S.cf.lmS) →
    (plane h h.t.tVD 3 w.lam w.a h.t.ptD true F).Yields c (p3, G) c1 →
    (plane h h.t.tVD 4 w.lam w.a h.t.ptD true F).Yields c' (p4, G') c1' →
    (sc3A h.d.vpd b - (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256))).value ρ W = 0 →
    W.slot (h.d.vpd.sEnd + 2 * b) =
      Aext (L5.dimOf h.S) C p (cellsK h.S M) .s12 (w.lam * h.S.HA + w.a) (pt ρ h.d.vpd.r)

/-- The second end value of a pair in the value product's sumcheck on the diagonal tiles is gam plus
the value, of the library's step s12. -/
def ValueOnEndB : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (F : Fork) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (C : Calls) (p : Pub K) (b : ℕ) (w : PW) (v : Aff) (G : Fork) (c c1 : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 →
    h.d.vpd.r.size = h.S.nvVD → h.d.zcW.size = h.S.cf.ldh →
    w.a < h.S.HA →
    (∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j) →
    ρ.val h.d.gam = p.th →
    QaAt tl h h.t.qVD h.d.zcW
      (tok h.S (eqTab (h.d.vpd.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT)))
        (lastCoords h.d.vpd.r h.S.cf.lB)) →
    (readGroup h h.t.qVD h.S.atV h.d.vpd.r h.d.zcW w.lam F).Yields c (v, G) c1 →
    (sc3B h.d.vpd b - (Aff.ofConst h.d.gam + v)).value ρ W = 0 →
    W.slot (h.d.vpd.sEnd + (2 * b + 1)) =
      Bext (L5.dimOf h.S) C p (cellsK h.S M) .s12 (w.lam * h.S.HA + w.a) (pt ρ h.d.vpd.r)

/-! ## The score at the index -/

/-- The value sent for the row maximum of pair b, from which the sumcheck for the score at the index
starts, is the library's rvM6: the row maximum at the drawn point. -/
def ScoreStartEnd : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (F : Fork) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (p : Pub K) (b : ℕ) (m : Aff) (G : Fork) (c c1 : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 →
    h.x.tg.size = h.S.cf.lgk → h.x.ti.size = h.S.cf.lt →
    b < h.S.NP →
    (∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j) →
    (∀ j < h.S.cf.lt, pt ρ h.x.ti j = p.ti j) →
    AhAt tl h h.t.hT (eqTab h.x.ti) →
    (readMaximum h h.t.hT h.x.tg (b / h.S.HA) (b % h.S.HA) F).Yields c (m, G) c1 →
    (Aff.slot (h.x.sM6 + b) - m).value ρ W = 0 →
    W.slot (h.x.sM6 + b) = rvM6 (L5.dimOf h.S) p (cellsK h.S M) b

/-- The first end value of pair b in the sumcheck for the score at the index is the query of the
library's step s16. -/
def ScoreAtIndexEnd : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (F : Fork) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (C : Calls) (p : Pub K) (b : ℕ) (q : Aff) (G : Fork) (c c1 : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 →
    h.x.scF.r.size = h.S.nvF →
    b < h.S.NP →
    QaAt tl h h.t.qF (h.x.rc h.S) (eqTab (h.x.ri h.S)) →
    (readHead h h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S) (b / h.S.HA) (b % h.S.HA) F).Yields c
      (q, G) c1 →
    (sc3A h.x.scF b - q).value ρ W = 0 →
    W.slot (h.x.scF.sEnd + 2 * b) =
      Aext (L5.dimOf h.S) C p (cellsK h.S M) .s16 b (pt ρ h.x.scF.r)

/-! ## The key at the index -/

/-- The end value of layer lam in the sumcheck for the key at the index is the library's rvKC: the
key of the layer at the sumcheck's point on position and head and at the point on the features that
the sumcheck before it has left. -/
def KeyAtIndexEndK : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (F : Fork) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (p : Pub K) (lam : ℕ) (kx : Aff) (G : Fork) (c c1 : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 →
    h.x.scF.r.size = h.S.nvF → h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk →
    lam < h.S.Lam →
    (∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = p.fn j) →
    QaAt tl h h.t.qKx (h.x.rc h.S) (eqTab (h.x.pj h.S)) →
    (readGroup h h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) lam F).Yields c (kx, G) c1 →
    (Aff.slot (h.x.sKC + lam) - kx).value ρ W = 0 →
    W.slot (h.x.sKC + lam) = rvKC (L5.dimOf h.S) p (cellsK h.S M) (pt ρ h.x.scd.r) lam

/-- The end value for bit k of pair b in the sumcheck for the key at the index is the library's
rvIBP: the bit of the index at the sumcheck's point on head and query's position. -/
def KeyAtIndexEndB : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (F : Fork) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (b k : ℕ) (bit : Aff) (G : Fork) (c c1 : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 →
    h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk →
    b < h.S.NP → k < h.S.cf.lt →
    AhAt tl h h.t.hPi (eqTab (h.x.pi h.S)) →
    (readIndexBit h h.t.hPi (h.x.pg h.S) (b / h.S.HA) (b % h.S.HA) k F).Yields c (bit, G) c1 →
    (Aff.slot (h.x.sIb h.S b k) - bit).value ρ W = 0 →
    W.slot (h.x.sIb h.S b k) = rvIBP (L5.dimOf h.S) (cellsK h.S M) (pt ρ h.x.scd.r) b k

/-! ## The bits of the index -/

/-- The form of claim 8 on the first end value of pair b, as the text of claim8 makes it
(OnBytes/Model/AttentionClaimsB.lean): the end value minus the sum over k below lt of eq(rk, k)
times bit k of the index. -/
def bitsForm (h : Heard) (b : ℕ) : SubM Aff :=
  (List.range h.S.cf.lt).foldlM (fun s k => do
    let bit ← readIndexBit h h.t.hR2 (h.x.rg2 h.S) (b / h.S.HA) (b % h.S.HA) k
    pure (Aff.addMul s bit (mulE minusOne ((eqTab (h.x.rk h.S)).getD k zeroE)))) (sc3A h.x.scH b)

/-- The first end value of pair b in the sumcheck for the bits is the extension of bitCube, with the
verifier's 4 bits, at the sumcheck's point. -/
def BitsEndA : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K)
    (h : Heard) (F : Fork) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (b : ℕ) (f : Aff) (G : Fork) (c c1 : Ctx),
    AttAt ρ W tl K3 M h lid cf fs → Cols F h K3 →
    h.x.scH.r.size = h.S.nvH →
    b < h.S.NP →
    AhAt tl h h.t.hR2 (eqTab (h.x.ri2 h.S)) →
    (bitsForm h b F).Yields c (f, G) c1 →
    f.value ρ W = 0 →
    W.slot (h.x.scH.sEnd + 2 * b) =
      Blocks.ext ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4)
        (bitCube 4 (L5.dimOf h.S) (cellsK h.S M) b) (pt ρ h.x.scH.r)

/-- The second end value of pair b in the sumcheck for the bits is the first minus 1. This claim
reads no table. -/
def BitsEndB : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (h : Heard) (b : ℕ),
    (sc3B h.x.scH b - sc3A h.x.scH b + Aff.ofConst oneE).value ρ W = 0 →
    W.slot (h.x.scH.sEnd + (2 * b + 1)) = W.slot (h.x.scH.sEnd + 2 * b) - 1

end OnBytes.Road.Rows
