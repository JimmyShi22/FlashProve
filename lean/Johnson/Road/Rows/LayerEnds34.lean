-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerEnds34.lean: what the claims around two sumchecks of a layer sub-proof say
on cells: the second token sumcheck and the batched sumcheck of the inner products.

A sumcheck stands between two statements. Its in-claim says that a form is worth a sum. Its
out-claims are the one equation that its rounds leave and, for each end value, that the hidden value
is a certain function of the cells at the point of challenges. That the out-claims imply the
in-claim, but for an error, is the sumcheck's own soundness; it is not looked at here. This file
names the statements on both sides in the letters of the verifier's Lean text
(OnBytes/Model/Layer.lean) and says what each comes to on cells. Every statement is an identity or
an implication in one world (World, OnBytes/Model/HideLaws.lean): no challenge is random here.

The public record. Pub34 gathers what is public once the sub-proof's own messages have been heard
(hearOwn). The records hd and hd2 of the two product layers, the points pts and the tables funs come
after the end of the batched sumcheck. With these stand the
public hypotheses of the theorem capstone (Johnson/Road/FormsKeysCaller.lean), whose head says
where each of these is run or proved, and six more in the letters of the verifier's caller: hrs,
hKT, hinv and the three ties of the slots. hKT is the line of hearTerms (OnBytes/Model/Layer.lean),
by reading: no theorem of this library concludes it from a run. (For the hearTerms of
OnBytes/Desc/First/K4/Hear.lean, which is another text, hearTerms_KT in
OnBytes/Desc/First/K4/HearLaws.lean concludes it from a run.)
Johnson/Road/Rows/LayerEnds34Ref.lean makes such a record from one equation that a
run is to show. A record Pub34 asks the fourth profile and the switches of
Switches. At the small example none exists: its field hfl fails there.

The names, in the order in which a proof of soundness walks, from the last claim to the first.
 - MapsL4: the two sides of the batched sumcheck's summand, on the hidden end values, are the
   extensions of the two long vectors at the end point. L4EndOut: it follows from the two claims on
   the sides' hidden values, from what the merge is there to show (Merged) and from what the
   product layers are there to show (Gated). Proved: l4EndOut.
 - InL4: the start form is worth the sum over all places of the product of the two long vectors.
   L4EndIn: then the three brackets B1 + B2 + x B3 add up to 0. Proved: l4EndIn.
 - LeftL3: what the second token sumcheck leaves (KT) is worth its summand at its end point, on
   the values that were sent; this is B3 = 0. L3EndRow: it says the same as the equation that the
   rounds of that sumcheck leave, with this summand. Proved: l3EndRow.
 - InL3: the hidden sum Cl is the sum over the cube of the summand Gpos under the equality weights
   of the token point; this is B2 = 0. Proved: l3EndIn.
 - Join: the form that the lookup's key side leaves is worth the weighted sum of the extensions of
   the library's eight key vectors; this is B1 = 0. It is the claim that the lookup reads; through
   the lookup it serves the clause key of LayerOrd (Johnson/Road/FormsKeysLinkL.lean).

What is not claimed. Nothing on soundness, and nothing on hiding. Between InL4 and LeftL3 lies the
draw of the element x, between MapsL4 and InL4 the batched sumcheck, between LeftL3 and InL3 the
second token sumcheck. The matrices Mm and M are any functions. The world is any world: a hidden
value is tied to nothing that is committed here. The two long vectors and the start form are read
in the world's entries of the reads, whose commitment is sent after the end point of the batched
sumcheck; that they are functions of the cells and of what is public before the element x, on true
reads, is stated by no theorem here. That the summand Gpos has degree at most 2 in each coordinate
off the cube is not stated either. The statements are in the letters of the verifier's Lean text;
nothing in this library ties them to a typed sumcheck. LayerOrd is named for the
reader alone: its file is not read here. The program does not read this file.

-/
import Johnson.Road.FormsKeysCaller
import Johnson.Road.FormsKeysWv
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff CallD Seg WsShape WsClaim HFun HTailF2 Level lastOf wsLayOf
  eqTab)
open OnBytes.Model.Layer (Env Lay Heard Reads TableAsk TableAt PanelEnv ClaimEnv Panels StackEnd
  layout scalesHeld readsOf layTables tableAsks panelsA panelsT placePanels stackEnd pointsOf funsOf
  matIx)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW Pan Sig1 ClT Gpos rdTrue wc zc famsIn fSh hhU zpos aC keyVec
  fams used lut layerR call len pos present key keyIdx)

variable {K : Type} [Field K]

/-! ## The three brackets, on one hypothesis on the reads -/

section Whole

variable {ρ : Reading K} {Wo : World K} {h : Model.Layer.Shape} {pc : List (List String)}
  {p : PanelEnv} {c : ClaimEnv} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {D : Dim} {s : WsShape} {lk : ℕ}
  {tb : Tables} {Zp : Array E} {ends : Array (Array E)} {s0 : Model.Forest.Shape} {H : Heard}
  {tT : Model.Tsc} {tl : HTailF2} {hd : Level} {hd2 : Option Level}
  {pts : List (String × Array E)} {funs : Array HFun}

/-- whole_lib (Johnson/Road/FormsKeysCaller.lean) under the hypotheses of capstone without its
last three: the start form of the batched sumcheck, less the sum over all places of the product of
the two long vectors, is the sum of three brackets, with one hypothesis on the reads (Hd). -/
theorem whole_holds (hy : layout h pc = .ok p.v.y) (S : Switches h)
    (hs : scalesHeld h p.v.sc = .ok ()) (hg : p.v.g < p.v.y.NGr) (hrd : readsOf p.v.y = .ok rd)
    (hl : layTables (matsR p.v.y p.v.g) (tableAsks p.v.y rd p.v.g) 0 = some r)
    (ht : p.v.tab = r.1) (hρ : Numerals ρ) (Z : Sized h D) (hc : D.cap = h.lidb)
    (hN : LinesAre p.v.y) (hfl : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k))
    (hsx : H.fo.zx.size = p.v.y.fo.dT) (hsy : H.fo.zy.size = p.v.y.fo.rK)
    (hzk : p.v.zk = (Array.range p.v.y.fo.NC).map fun q =>
      H.fo.zy.extract (p.v.y.fo.rK - p.v.y.fo.iota.getD q 0) H.fo.zy.size ++ H.fo.zx)
    (he : p.e = (Array.range p.v.y.fo.NC).map (Model.Forest.callWeight p.v.y.fo H.fo.zy))
    (hZ : lastOf H.fo.zx p.v.y.h.la = .ok Zp) (hzt : lastOf H.fo.zx p.v.y.h.lt = .ok H.ztF)
    (hm : p.v.zk.mapM (fun z => (lastOf z p.v.y.h.la).toOption) = some ends)
    (ha : ends.all (· == Zp) = true)
    (hs0 : Model.Forest.shape p.v.y.cl p.v.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (p.v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (env : p.v = c.v) (Zw : SizedW s D.P) (hsL : s.L = h.L)
    (hlw : wsLayOf s true lk = .ok c.wsLay) (h4 : h.p4 = true) (hcrt : c.rt = tT.r)
    (R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb (c.v.g * c.v.y.Lam) lam)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR p.v.y p.v.g) (hNM : tl.NM = tl.mats.size)
    (hpts : pointsOf p.v.y H hd hd2 = some pts)
    (hfun : funsOf p.v.y H.fo pts r.2.1 = some funs) (hT : H.tT = some tT) (Mm : Mats K)
    (Hd : ∀ Fn ∈ funs, Holds ρ Wo tl p.v.iU3 p.v.K3 Mm Fn)
    (M : Wm K) (hh : ℕ → ℕ → K) {TS : List ℕ}
    (hTS : rd.tscCalls.mapM p.v.y.callNo = some TS)
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hcl : c.weightClaims TS = some cl) {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1)
    {rs H1 V : Array E} {lam : ℕ} {shownA shownB : E} {s' : StackEnd}
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s')
    (hlam : (ceilLog2 (placePanels pans'.bl).2 == lam) = true)
    (hHe : H.fo.e = p.e) (alpha theta : E)
    {weighed : Array (Array Bool)} (hw : p.v.y.calls.mapM p.v.weighedOf = some weighed)
    {parts : List Aff}
    (hparts : (p.v.y.calls.zip weighed).toList.zipIdx.mapM
      (fun x => p.v.joinPart alpha theta x.2 x.1.1 x.1.2) = some parts)
    (hpad : ∀ k : Fin 8,
      ρ.val (ofF ((p.v.y.cl.getD k.val {}).tauAt (p.v.y.cl.getD k.val {}).t0)) =
        (((lut tb k).pad : ℤ) : K))
    (hH : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
      ∀ l, l < D.nl → ∀ j, j < fSh D l → hh 0 (l * 2 ^ ceilLog2 p.v.y.h.f + j) =
        hhU D (cellsOf D (cellsAt p.v.y Mm)) l j (zpos D (zOf ρ H.fo.zx H.fo.zy))) :
    letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
    (startOf H om parts).value ρ Wo -
        ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
          vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y =
      ((∑ q : Fin 8, wc D (zOf ρ H.fo.zx H.fo.zy) q *
          (ρ.val alpha - (q.val : K) * ρ.val theta -
            Blocks.ext (aC D q)
              (keyVec D (cellsOf D (cellsAt p.v.y Mm)) tb (c.v.g * c.v.y.Lam)
                (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) q)
              (zc D (zOf ρ H.fo.zx H.fo.zy) q))) +
        ρ.val (padOf H) - H.fo.cEnd.value ρ Wo) +
      (ClT D (cellsOf D (cellsAt p.v.y Mm)) tb (c.v.g * c.v.y.Lam)
          (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) (zOf ρ H.fo.zx H.fo.zy) -
        Wo.slot tT.sCl) +
      ρ.val (om.getD 1 zeroE) *
        (H.KT.value ρ Wo -
          Sig1 D (rPort ρ p.v.y p.shownT hh D (cellsOf D (cellsAt p.v.y Mm))
              (zOf ρ H.fo.zx H.fo.zy) (pt ρ c.rt)) tb
            (c.v.g * c.v.y.Lam) (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l))
            (zOf ρ H.fo.zx H.fo.zy) (pt ρ c.rt)) := by
  have sh := (admitted_of_layout hy S.p3).shape
  obtain ⟨Z1, hZ1, T⟩ := trueAt_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hzt hfun Mm Hd
  obtain ⟨Z2, hZ2, hr2, T2⟩ :=
    trueAt2_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hfun hT Mm Hd
  have e1 : Z1 = Zp := Except.ok.inj (hZ1.symm.trans hZ)
  have e2 : Z2 = Zp := Except.ok.inj (hZ2.symm.trans hZ)
  subst e1
  subst e2
  have Ro := shortQa_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hfun h4 Mm Hd
  rw [sh] at T T2 Ro
  rw [← hcrt] at T2 hr2
  have hrt : c.rt.size = D.lT := by rw [hr2, sh, Z.lT]
  exact whole_lib hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0 hpt env Zw
    hsL hlw h4 hrt R T T2 Ro M hh (ts_eq hy S.p3 hN hrd hTS) hp hcl hom hst hlam H hHe hT alpha
    theta hw hparts hpad hH

end Whole

/-! ## The public record -/

/-- What is public in the check of a layer sub-proof once the sub-proof's own messages have been
heard (hearOwn). The records hd and hd2 of the two product layers, the points pts and the tables
funs come after the end of the batched sumcheck. With these stand the
public hypotheses of capstone (Johnson/Road/FormsKeysCaller.lean) and six more, the last six
fields, which are lines of the verifier's caller. The data are the records that
the check builds (hearOwn, hearStack in OnBytes/Model/Layer.lean); the library's sizes D, tables tb
and shape of the weights s stand beside them. The end point of the batched sumcheck is c.rs. The
four numbers sA0, sH1, sB0, sV are the slots of its end values. -/
structure Pub34 (K : Type) [Field K] where
  /-- how an element of the program's field is read in K -/
  ρ : Reading K
  /-- the shape -/
  h : Model.Layer.Shape
  /-- the lines of calls -/
  pc : List (List String)
  /-- the panels' environment -/
  p : PanelEnv
  /-- the weight claims' environment -/
  c : ClaimEnv
  /-- the reads -/
  rd : Reads
  /-- the tables as they are laid out -/
  r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ
  /-- the library's sizes -/
  D : Dim
  /-- the shape of the weights -/
  s : WsShape
  /-- the bits of a column of the matrix of weights -/
  lk : ℕ
  /-- the library's tables -/
  tb : Tables
  /-- the last la coordinates of the lookup's point -/
  Zp : Array E
  /-- the last la coordinates of the calls' points -/
  ends : Array (Array E)
  /-- the lookup's shape -/
  s0 : Model.Forest.Shape
  /-- what was heard up to the second token sumcheck -/
  H : Heard
  /-- the second token sumcheck -/
  tT : Model.Tsc
  /-- the smallness test -/
  tl : HTailF2
  /-- the first product layer of the gated products -/
  hd : Level
  /-- the second -/
  hd2 : Option Level
  /-- the points by name -/
  pts : List (String × Array E)
  /-- all tables with their weights -/
  funs : Array HFun
  /-- the calls with terms in the second token sumcheck -/
  TS : List ℕ
  /-- the panels -/
  pans : Panels
  /-- the weight claims -/
  cl : List WsClaim
  /-- the two weights 1 and x -/
  om : Array E
  /-- what was sent for the never-sent vectors -/
  H1 : Array E
  /-- what was sent for the weight claims -/
  V : Array E
  /-- the number of rounds of the batched sumcheck -/
  lam : ℕ
  /-- what was sent for the A side -/
  shownA : E
  /-- what was sent for the B side -/
  shownB : E
  /-- the end of the batched sumcheck -/
  fin : StackEnd
  /-- the lookup's challenge -/
  alpha : E
  /-- the lookup's shift -/
  theta : E
  /-- the marks of joinStart -/
  weighed : Array (Array Bool)
  /-- the calls' factors of joinStart -/
  parts : List Aff
  /-- the slot of the A side's end value -/
  sA0 : ℕ
  /-- the slot of the first never-sent vector's end value -/
  sH1 : ℕ
  /-- the slot of the B side's end value -/
  sB0 : ℕ
  /-- the slot of the first weight claim's end value -/
  sV : ℕ
  hy : layout h pc = .ok p.v.y
  S : Switches h
  hs : scalesHeld h p.v.sc = .ok ()
  hg : p.v.g < p.v.y.NGr
  hrd : readsOf p.v.y = .ok rd
  hl : layTables (matsR p.v.y p.v.g) (tableAsks p.v.y rd p.v.g) 0 = some r
  ht : p.v.tab = r.1
  hρ : Numerals ρ
  Z : Sized h D
  hc : D.cap = h.lidb
  hN : LinesAre p.v.y
  hfl : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k)
  hsx : H.fo.zx.size = p.v.y.fo.dT
  hsy : H.fo.zy.size = p.v.y.fo.rK
  hzk : p.v.zk = (Array.range p.v.y.fo.NC).map fun q =>
    H.fo.zy.extract (p.v.y.fo.rK - p.v.y.fo.iota.getD q 0) H.fo.zy.size ++ H.fo.zx
  he : p.e = (Array.range p.v.y.fo.NC).map (Model.Forest.callWeight p.v.y.fo H.fo.zy)
  hZ : lastOf H.fo.zx p.v.y.h.la = .ok Zp
  hzt : lastOf H.fo.zx p.v.y.h.lt = .ok H.ztF
  hm : p.v.zk.mapM (fun z => (lastOf z p.v.y.h.la).toOption) = some ends
  ha : ends.all (· == Zp) = true
  hs0 : Model.Forest.shape p.v.y.cl p.v.y.h.lidb = .ok s0
  hpt : ((List.range s0.NC).all fun q =>
    (p.v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true
  env : p.v = c.v
  Zw : SizedW s D.P
  hsL : s.L = h.L
  hlw : wsLayOf s true lk = .ok c.wsLay
  h4 : h.p4 = true
  hcrt : c.rt = tT.r
  R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb (c.v.g * c.v.y.Lam) lam
  htm : (tl.mats.map fun M => (M.m, M.k)) = matsR p.v.y p.v.g
  hNM : tl.NM = tl.mats.size
  hpts : pointsOf p.v.y H hd hd2 = some pts
  hfun : funsOf p.v.y H.fo pts r.2.1 = some funs
  hT : H.tT = some tT
  hTS : rd.tscCalls.mapM p.v.y.callNo = some TS
  hp : panelsT p TS (panelsA p {}) = some pans
  hcl : c.weightClaims TS = some cl
  hom : ρ.val (om.getD 0 zeroE) = 1
  hst : stackEnd p.v.y (placePanels pans.bl).1 c.rs lam om H1 V shownA shownB = some fin
  hlam : (ceilLog2 (placePanels pans.bl).2 == lam) = true
  hHe : H.fo.e = p.e
  hw : p.v.y.calls.mapM p.v.weighedOf = some weighed
  hparts : (p.v.y.calls.zip weighed).toList.zipIdx.mapM
    (fun x => p.v.joinPart alpha theta x.2 x.1.1 x.1.2) = some parts
  hpad : ∀ k : Fin 8,
    ρ.val (ofF ((p.v.y.cl.getD k.val {}).tauAt (p.v.y.cl.getD k.val {}).t0)) =
      (((lut tb k).pad : ℤ) : K)
  /-- one challenge for each round of the batched sumcheck -/
  hrs : lam ≤ c.rs.size
  /-- the letters in which the check makes what the second token sumcheck leaves (hearTerms):
  the equation that its rounds leave, asked for without the summand, times -1 / eps -/
  hKT : H.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps))
  /-- the drawn eps was not 0 (the test coin-zero), and the reading takes the program's inverse and
  negative to those of K -/
  hinv : ρ.val (negE (invE tT.p.eps)) * ρ.val tT.p.eps = -1
  /-- the slots of the end values, as hearStack numbers them: the never-sent vectors' -/
  hsH1 : sH1 = sA0 + 1
  /-- the B side's -/
  hsB0 : sB0 = sH1 + (1 + (if p.v.y.h.p3 then p.v.y.LamM else 0))
  /-- the weight claims' -/
  hsV : sV = sB0 + 1

namespace Pub34

variable (X : Pub34 K) (Wo : World K) (Mm : Mats K) (M : Wm K) (hh : ℕ → ℕ → K)

/-- The width of the model in the weights' shape is the layout's. -/
theorem hsd : X.s.d = X.c.v.y.h.d := by
  have A := (admitted_of_layout X.hy X.S.p3).shape
  rw [X.Zw.d, X.Z.d, ← X.env, A]

/-- So is a routed expert's hidden width. -/
theorem hsfe : X.s.fe = X.c.v.y.h.fe := by
  have A := (admitted_of_layout X.hy X.S.p3).shape
  rw [X.Zw.fe, X.Z.fe, ← X.env, A]

/-- A layer has twice the hidden units of an expert. -/
theorem f2 : X.D.f = 2 * X.D.fe := by
  have A := admitted_of_layout X.hy X.S.p3
  show X.D.P.f = 2 * X.D.P.fe
  rw [X.Z.f, X.Z.fe, ← A.shape]
  exact A.laid.ffe

/-! ## The letters -/

/-- The cells that are read in the entries of Mm, by the library's rule for a cell's place. -/
def t : Cell → K := cellsOf X.D (cellsAt X.p.v.y Mm)

/-- The number of the group's first layer. -/
def L0 : ℕ := X.c.v.g * X.c.v.y.Lam

/-- The weights of the group's layers, read in M by the library's layout. -/
def w : ℕ → LW K := fun l => layerR X.D.P X.lk M (X.c.v.g * X.c.v.y.Lam + l)

/-- The library's point, made from the lookup's two points. -/
def z : ℕ → K := zOf X.ρ X.H.fo.zx X.H.fo.zy

/-- The end point of the second token sumcheck. -/
def zh : ℕ → K := pt X.ρ X.c.rt

/-- The element that joins the two claims of the batched sumcheck's start form. -/
def x : K := X.ρ.val (X.om.getD 1 zeroE)

/-- The long A vector. It holds what the second token sumcheck sent, as it was sent. -/
def vecA (Y : ℕ) : K := vecOf (aG X.ρ Wo X.p.v.y X.om hh) (placePanels X.pans.bl).1.toList Y

/-- The long B vector. -/
def vecB (Y : ℕ) : K :=
  vecOf (bG X.ρ Wo (wvOf X.ρ X.c.wsLay M X.cl)) (placePanels X.pans.bl).1.toList Y

/-- The worth of the start form of the batched sumcheck. -/
def start : K := (startOf X.H X.om X.parts).value X.ρ Wo

/-- The weighted sum of the extensions of the library's eight key vectors, with the padding trees'
number. -/
def joinK : K :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  (∑ q : Fin 8, wc X.D (zOf X.ρ X.H.fo.zx X.H.fo.zy) q *
      (X.ρ.val X.alpha - (q.val : K) * X.ρ.val X.theta -
        Blocks.ext (aC X.D q)
          (keyVec X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) X.tb (X.c.v.g * X.c.v.y.Lam)
            (fun l => layerR X.D.P X.lk M (X.c.v.g * X.c.v.y.Lam + l)) q)
          (zc X.D (zOf X.ρ X.H.fo.zx X.H.fo.zy) q))) +
    X.ρ.val (padOf X.H)

/-- The honest value of the sum that the second token sumcheck claims. -/
def clT : K :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  ClT X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) X.tb (X.c.v.g * X.c.v.y.Lam)
    (fun l => layerR X.D.P X.lk M (X.c.v.g * X.c.v.y.Lam + l)) (zOf X.ρ X.H.fo.zx X.H.fo.zy)

/-- The summand of the second token sumcheck at a token point u. -/
def gpos (u : ℕ → K) : K :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  Gpos X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) X.tb (X.c.v.g * X.c.v.y.Lam)
    (fun l => layerR X.D.P X.lk M (X.c.v.g * X.c.v.y.Lam + l)) (zOf X.ρ X.H.fo.zx X.H.fo.zy) u

/-- The summand of the second token sumcheck at its end point, on the values that were sent: the
sum of the late panels' shares. -/
def sig1 : K :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  Sig1 X.D (rPort X.ρ X.p.v.y X.p.shownT hh X.D (cellsOf X.D (cellsAt X.p.v.y Mm))
      (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt)) X.tb
    (X.c.v.g * X.c.v.y.Lam) (fun l => layerR X.D.P X.lk M (X.c.v.g * X.c.v.y.Lam + l))
    (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt)

/-- The first bracket: the lookup's join. -/
def B1 : K := X.joinK Mm M - X.H.fo.cEnd.value X.ρ Wo

/-- The second bracket: the sum that the second token sumcheck claims. -/
def B2 : K := X.clT Mm M - Wo.slot X.tT.sCl

/-- The third bracket: what the second token sumcheck leaves. -/
def B3 : K := X.H.KT.value X.ρ Wo - X.sig1 Mm M hh

/-! ## The statements on the world -/

/-- Every table of the reads holds what it says of the matrices Mm. -/
def ReadsTrue : Prop := ∀ Fn ∈ X.funs, Holds X.ρ Wo X.tl X.p.v.iU3 X.p.v.K3 Mm Fn

/-- The never-sent vector number 0 is the vector of the gated products at the lookup's token
point. This fixes a letter; it is no claim. -/
def Honest0 : Prop :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  ∀ l, l < X.D.nl → ∀ j, j < fSh X.D l → hh 0 (l * 2 ^ ceilLog2 X.p.v.y.h.f + j) =
    hhU X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) l j (zpos X.D (zOf X.ρ X.H.fo.zx X.H.fo.zy))

/-- What the merge of the weight claims and the test on the committed matrix are there to show: the
hidden end value of each weight claim is the sum that the claim speaks of in M. -/
def Merged : Prop :=
  ∀ a y, X.cl[a]? = some y → Wo.slot (X.sV + a) = claimVal X.ρ X.c.wsLay M y

/-- What the product layers of the gated products are there to show: the hidden end value of each
never-sent vector is the vector's extension at the end point's coordinates of its panel. -/
def Gated : Prop :=
  ∀ b ∈ (placePanels X.pans.bl).1.toList,
    (∀ k, b.tri = true → b.virt = some k →
      Wo.slot (X.sH1 + k) = ∑ yv ∈ range (2 ^ b.wy), eqR X.ρ X.c.rs 0 b.wy yv * hh k yv) ∧
    (∀ k, b.tri = false → b.virt = some k →
      Wo.slot (X.sH1 + k) = gsum X.ρ X.c.rs b (fun i yv => hh k (i * 2 ^ b.wy + yv)))

/-- The verifier's two claims on the hidden end values of the two sides
(OnBytes/Model/Layer.lean, runForkHidG2). -/
def sideClaims : List Aff := [Aff.slot X.sA0 - X.fin.Alin, Aff.slot X.sB0 - X.fin.Blin]

/-- The out-claims of the batched sumcheck on its end values, in one: the two factors of its
summand, computed on the hidden end values, are the extensions of the two long vectors at the end
point. -/
def MapsL4 : Prop :=
  AsAt X.ρ Wo X.p.v.y X.c.rs X.lam X.om (fun k => Wo.slot (X.sH1 + k))
      (fun n => Wo.slot (X.sV + n)) (Wo.slot X.sA0) (placePanels X.pans.bl).1.toList =
    ∑ Y ∈ range (2 ^ X.lam), eqR X.ρ X.c.rs 0 X.lam Y * X.vecA Wo hh Y ∧
  BsAt X.ρ Wo X.p.v.y X.c.rs X.lam X.om (fun k => Wo.slot (X.sH1 + k))
      (fun n => Wo.slot (X.sV + n)) (Wo.slot X.sB0) (placePanels X.pans.bl).1.toList =
    ∑ Y ∈ range (2 ^ X.lam), eqR X.ρ X.c.rs 0 X.lam Y * X.vecB Wo M Y

/-- The in-claim of the batched sumcheck. -/
def InL4 : Prop := X.start Wo = ∑ Y ∈ range (2 ^ X.lam), X.vecA Wo hh Y * X.vecB Wo M Y

/-- The out-claim of the second token sumcheck that stands for its last equation: what it leaves is
worth its summand at its end point, on the values that were sent. -/
def LeftL3 : Prop := X.H.KT.value X.ρ Wo = X.sig1 Mm M hh

/-- The in-claim of the second token sumcheck: the hidden sum is the sum over the cube of the
summand under the equality weights of the lookup's token point. -/
def InL3 : Prop :=
  Wo.slot X.tT.sCl =
    Blocks.ext X.D.lT (fun i => X.gpos Mm M (Blocks.cubePt X.D.lT i))
      (zpos X.D (zOf X.ρ X.H.fo.zx X.H.fo.zy))

/-- The claim that the lookup reads: the form that its key side leaves is worth the weighted sum of
the extensions of the library's key vectors. -/
def Join : Prop := X.H.fo.cEnd.value X.ρ Wo = X.joinK Mm M

end Pub34

/-! ## The ends -/

/-- The end of the batched sumcheck on the side of its out-claims. -/
def L4EndOut (X : Pub34 K) : Prop :=
  ∀ (Wo : World K) (M : Wm K) (hh : ℕ → ℕ → K),
    (∀ f ∈ X.sideClaims, f.value X.ρ Wo = 0) → X.Merged Wo M → X.Gated Wo hh → X.MapsL4 Wo M hh

/-- The end of the batched sumcheck on the side of its in-claim. -/
def L4EndIn (X : Pub34 K) : Prop :=
  ∀ (Wo : World K) (Mm : Mats K) (M : Wm K) (hh : ℕ → ℕ → K),
    X.ReadsTrue Wo Mm → X.Honest0 Mm hh →
      (X.InL4 Wo M hh ↔ X.B1 Wo Mm M + X.B2 Wo Mm M + X.x * X.B3 Wo Mm M hh = 0)

/-- The end of the second token sumcheck on the side of its in-claim, and what is then left for the
lookup. -/
def L3EndIn (X : Pub34 K) : Prop :=
  ∀ (Wo : World K) (Mm : Mats K) (M : Wm K),
    (X.InL3 Wo Mm M ↔ X.B2 Wo Mm M = 0) ∧ (X.Join Wo Mm M ↔ X.B1 Wo Mm M = 0)

/-- The end of the second token sumcheck on the side of its last equation: that what it leaves is
worth the summand says the same as the equation that its rounds leave, with that summand: the form
that pscRow returns without a summand, plus eps times the summand, is 0. -/
def L3EndRow (X : Pub34 K) : Prop :=
  ∀ (Wo : World K) (Mm : Mats K) (M : Wm K) (hh : ℕ → ℕ → K),
    X.LeftL3 Wo Mm M hh ↔
      (X.tT.p.rowForm zeroE {}).value X.ρ Wo + X.ρ.val X.tT.p.eps * X.sig1 Mm M hh = 0

/-- From the three in-claims and out-claims to the claim that the lookup reads. -/
def L34Join (X : Pub34 K) : Prop :=
  ∀ (Wo : World K) (Mm : Mats K) (M : Wm K) (hh : ℕ → ℕ → K),
    X.ReadsTrue Wo Mm → X.Honest0 Mm hh → X.InL4 Wo M hh → X.LeftL3 Wo Mm M hh →
      X.InL3 Wo Mm M → X.Join Wo Mm M

theorem l4EndOut (X : Pub34 K) : L4EndOut X := by
  intro Wo M hh hc hM hG
  have cA := hc (Aff.slot X.sA0 - X.fin.Alin) (by simp [Pub34.sideClaims])
  have cB := hc (Aff.slot X.sB0 - X.fin.Blin) (by simp [Pub34.sideClaims])
  obtain ⟨a, b, -⟩ := stack_slots X.hp X.hlam X.hrs
    (endsTrue_of_claims X.ρ X.p X.c X.env X.TS X.hp X.hcl X.hlw X.hsd X.hsfe M
      (vv := fun n => Wo.slot (X.sV + n)) hM (h1 := fun k => Wo.slot (X.sH1 + k)) hG)
    X.hst cA cB
  exact And.intro a b

theorem l4EndIn (X : Pub34 K) : L4EndIn X := by
  intro Wo Mm M hh Hd hH
  have key := whole_holds X.hy X.S X.hs X.hg X.hrd X.hl X.ht X.hρ X.Z X.hc X.hN X.hfl X.hsx X.hsy
    X.hzk X.he X.hZ X.hzt X.hm X.ha X.hs0 X.hpt X.env X.Zw X.hsL X.hlw X.h4 X.hcrt X.R X.htm X.hNM
    X.hpts X.hfun X.hT Mm Hd M hh X.hTS X.hp X.hcl X.hom X.hst X.hlam X.hHe X.alpha X.theta X.hw
    X.hparts X.hpad hH
  have key' : X.start Wo - ∑ Y ∈ range (2 ^ X.lam), X.vecA Wo hh Y * X.vecB Wo M Y =
      X.B1 Wo Mm M + X.B2 Wo Mm M + X.x * X.B3 Wo Mm M hh := key
  unfold Pub34.InL4
  rw [← key', sub_eq_zero]

theorem l3EndIn (X : Pub34 K) : L3EndIn X := by
  intro Wo Mm M
  have hf : X.D.f = 2 * X.D.fe := X.f2
  refine ⟨?_, ?_⟩
  · have e : X.clT Mm M = Blocks.ext X.D.lT (fun i => X.gpos Mm M (Blocks.cubePt X.D.lT i))
        (zpos X.D (zOf X.ρ X.H.fo.zx X.H.fo.zy)) :=
      clT_gpos (scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) X.D _ X.tb _ _ _ hf
    unfold Pub34.InL3 Pub34.B2
    rw [← e, sub_eq_zero]
    exact eq_comm
  · unfold Pub34.Join Pub34.B1
    rw [sub_eq_zero]
    exact eq_comm

/-- The core of l3EndRow: where ci is -1 / eps, that ci u is g says the same as u + eps g = 0. -/
theorem row_core {ci eps u g : K} (h : ci * eps = -1) : ci * u = g ↔ u + eps * g = 0 := by
  constructor
  · intro e
    rw [← e]
    linear_combination u * h
  · intro e
    linear_combination ci * e - g * h

theorem l3EndRow (X : Pub34 K) : L3EndRow X := by
  intro Wo Mm M hh
  unfold Pub34.LeftL3
  rw [X.hKT, Aff.value_scale]
  exact row_core X.hinv

theorem l34Join (X : Pub34 K) : L34Join X := by
  intro Wo Mm M hh Hd hH h4 h3 hi
  have a := (l4EndIn X Wo Mm M hh Hd hH).mp h4
  have b2 := ((l3EndIn X Wo Mm M).1).mp hi
  have b3 : X.B3 Wo Mm M hh = 0 := sub_eq_zero.mpr h3
  rw [b2, b3, mul_zero, add_zero, add_zero] at a
  exact ((l3EndIn X Wo Mm M).2).mpr a

end OnBytes.Road.Rows
