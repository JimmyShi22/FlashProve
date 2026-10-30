-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/Ground.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE. That the hypotheses on a world can hold together:
no example is known of Opened, of OpenedBack or of IdnHold. Laws that end in IdnHold lie in other
files, each under hypotheses of its own: `idnHold_of_field` and `idnHold_full` (W/IdnOfField.lean)
and `k4_idn_mats` (Johnson/Desc/ProofFile/Honest/K4/Law/W/IdnHead.lean): ALL THREE AT THE FULL SIZE
ALONE (the library's reference sizes, four layers in a group, the field Cb.Gl.E). THAT THE RUNS OF
SLOTS WHICH Opened NAMES DO NOT OVERLAP: if two fields named one slot with two values, Opened would
be empty. Of the public hypotheses: K4Ground and K4Sizes follow where a hearing returns, from nine
facts on the plan (W/GroundOfHear.lean, W/SizesOfHear.lean); that a hearing returns is not shown in
this file. SEVEN FIELDS OF Opened AND OpenedBack RESTATE THE CLAIM THAT THEY SERVE (cl8, sqR, rt,
sc, sel, sideA, sideB): each docstring says so. Nothing on soundness, on completeness or on any
other property.

The shared variables and hypotheses of the statements "each form of a group of claims of the layers'
own rounds (sub-protocol K4) is worth 0 in a world W". A form f is worth x in W: Aff.value ρ W f = x
(OnBytes/Model/HideLaws.lean). Definitions of hypotheses, and four statements that lead from the
public ones to the library's structures Fits, TrueAt3 and NormWords and to "every table holds".

THE SHARED VARIABLES, for every file of this folder:
    K a field · ρ : Reading K · W : World K, all three free · [scl : Scl] free
    v : Env · H : Heard · hd : Level · o : Own (at the join v = o.v, H = o.H, hd = o.hd)
    D : Dim · c : Cells K · t : Cell → K · Mm : Mats K
      (at the join c = cellsAt v.y Mm, t = cellsOf D c, scl = sclOf h v.sc v.g v.y.Lam)
    the points:  low = pt ρ Z1, Z1 the last la coordinates of H.fo.zx · u = pt ρ H.ztF
      lowV = lowVOf ρ P v H · uV = uVOf ρ P v H   (coordinates of H.wpl.r)
      uP = pt ρ H.PV · uR = pt ρ H.tV.r · lowE = pt ρ H.ZE · uE = uEOf ρ v H
  A statement on a group has the form
    (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) ‹public facts›
    ‹W.slot j = a term of the library at t›
    ‹the identities at the cells (IdnHold; HotPoint, W/HotEmb.lean)›
    ‹the own claim of the group's sumcheck, as a bare hypothesis› ⊢ one field of FrontWorth or
    BackWorth (Johnson/Road/K4/WorthGroups.lean), to the letter. In W/Gated.lean EndGround
    (Johnson/Road/Rows/GatedEnds.lean) at each product layer's point stands in the place of F and
    T3: a premise on the world of its own.

  `K4Ground h pc v rd r tl H hd hd2 pts funs D`   the public facts on the verifier's layout that the
      library's trueAt_of_holds, trueAt3_of_holds, trueAt4_of_holds and fits_of_layout_true ask.
  `K4Sizes P v H hd hd2 D`   the public numbers that the statements on the groups ask.
  `lowVOf`, `uVOf`, `uEOf`   three points.
  `Opened ρ W P o D t`   which value lies under each slot that the run "front" reads: one field for
      each stretch of slots. The own claims of the sumchecks are not here, nor the slots that only
      their proofs read (W/OpenedOwn.lean). Nor the lookup's slot o.H.fo.sBit, which the second of
      its three claims reads: the lookup's three claims are hypotheses of their own (LookThree,
      W/Join.lean).
  `OpenedBack ρ W o`   the like for the two slots that the run "back" reads.
  `IdnHold D t`   the library's seventeen identities of each norm at the cells t, at every position.
  `ground`   K4Ground, and "every table holds what it says of Mm", give Fits and TrueAt3 at the last
      coordinates of H.wpl.r as the library cuts them.
  `ground_point`   the same with TrueAt3 at lowVOf and uVOf, under K4Sizes.
  `ground_words`   NormWords under the scales that sclOf makes.
  `holds_item`   in the world of every ledger and every mask row, with the entries entryTrue, every
      table holds what it says of Mm, under K4Ground at what a hearing returned. TRUE BY MAKE:
      entryTrue is defined as what the tables say of Mm (Johnson/Road/K4/EntryTrue.lean, whose
      Limits hold here); shown is that no place is owned twice. Nothing ties these entries to what a
      prover has committed.
No property is claimed.
-/
import Johnson.Road.K4.NormsReadsHolds
import Johnson.Road.K4.EntryTrue
import Johnson.Road.K4.SquaresPoint
import Johnson.Road.Rows.GatedEnds
import Johnson.Road.FormsKeysIdnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Reads Heard Pub Own TableAsk TableAt layout scalesHeld
  readsOf layTables tableAsks pointsOf funsOf)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell idnVal bS xS led lF lFe slV upV slV' upV')
open Blocks (ext)

/-- **The public facts on the layout.** This defines a hypothesis; the definition claims nothing. -/
structure K4Ground (h : Layer.Shape) (pc : List (List String)) (v : Env) (rd : Reads)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ) (tl : HTailF2) (H : Heard) (hd : Level)
    (hd2 : Option Level) (pts : List (String × Array E)) (funs : Array HFun) (D : Dim) : Prop where
  lay : layout h pc = .ok v.y
  sw : Switches h
  scales : scalesHeld h v.sc = .ok ()
  grp : v.g < v.y.NGr
  reads : readsOf v.y = .ok rd
  tables : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r
  tab : v.tab = r.1
  mats : tl.mats.map (fun M => (M.m, M.k)) = matsR v.y v.g
  NM : tl.NM = tl.mats.size
  points : pointsOf v.y H hd hd2 = some pts
  zt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF
  funs : funsOf v.y H.fo pts r.2.1 = some funs
  sized : Sized h D

/-- **The public numbers.** This defines a hypothesis; the definition claims nothing. -/
structure K4Sizes (P : Pub) (v : Env) (H : Heard) (hd : Level) (hd2 : Option Level) (D : Dim) :
    Prop where
  y : P.y = v.y
  NI : v.y.NI = D.nNu
  la : v.y.h.la = v.y.ls + D.lT
  Pd : v.y.Pd = 2 ^ v.y.lPd
  lsPd : v.y.ls ≤ v.y.lPd
  NIle : v.y.NI ≤ 2 ^ P.rd.lNI
  blocks : v.y.h.d / v.y.S2 ≤ 2 ^ (v.y.lPd - v.y.ls)
  wpl : H.wpl.r.size = P.rd.lNI + v.y.lPd - v.y.ls + v.y.h.la
  lsF : v.y.ls ≤ lF D
  lsFe : v.y.ls ≤ lFe D
  Lam : v.y.Lam = 2 ^ D.lL
  f : v.y.h.f = 2 ^ lF D
  Pf : v.y.Pf = 2 ^ lF D
  LamM : v.y.LamM = 2 ^ (D.lL - 1)
  fe : v.y.h.fe = 2 ^ lFe D
  Dfe : D.fe = 2 ^ lFe D
  hd : hd.r.size = D.lL + lF D - v.y.ls + v.y.ls + D.lT
  hd2 : ∀ o2, hd2 = some o2 → o2.r.size = D.lL - 1 + lFe D - v.y.ls + v.y.ls + D.lT

variable {K : Type} [Field K]

/-- The coordinates of the squares' point that choose a feature in its block. -/
def lowVOf (ρ : Reading K) (P : Pub) (v : Env) (H : Heard) : ℕ → K :=
  fun j => pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + j)

/-- The coordinates of the squares' point that choose a position. -/
def uVOf (ρ : Reading K) (P : Pub) (v : Env) (H : Heard) : ℕ → K :=
  fun j => pt ρ H.wpl.r (P.rd.lNI + v.y.lPd - v.y.ls + v.y.ls + j)

/-- The coordinates of the embedding's point that choose a position. -/
def uEOf (ρ : Reading K) (v : Env) (H : Heard) : ℕ → K := fun j => pt ρ H.ZE (v.y.ls + j)

/-- **WHICH HIDDEN VALUE EACH SLOT HOLDS**, each a term of the library at the cells t, or the worth
of a form in the reads. That the stretches of slots do not overlap is not shown: if two fields named
one slot with two values, no world would meet the structure. This defines a hypothesis; the
definition claims nothing. -/
structure Opened [scl : Scl] (ρ : Reading K) (W : World K) (P : Pub) (o : Own) (D : Dim)
    (t : Cell → K) : Prop where
  /-- the nine sums of each norm, at the norms' token point -/
  sums : ∀ ν, ν < D.nNu → ∀ s, s < 9 → W.slot (o.H.sW + 9 * ν + s) = wHat D t ν (pt ρ o.H.PV) s
  /-- the seven row products of each norm -/
  prods : ∀ ν, ν < D.nNu → ∀ j, j < 7 →
    W.slot (o.H.sPv + 7 * ν + j) = pHat D t ν (pt ρ o.H.PV) j
  /-- the batch of the row products. THIS FIELD RESTATES ITS CLAIM: the form of the batch is worth
  this slot less this sum (rowBatch_value, Johnson/Road/FormsKeysIdnW.lean) -/
  cl8 : W.slot o.H.tV.sCl = ∑ i ∈ range (ledNP o.v.y.h.xl * o.v.y.NI),
    ρ.val (o.H.omV.getD i zeroE) * W.slot (o.H.sPv + i)
  /-- the four end values of each norm, at the end point of the row products' sumcheck -/
  ends8 : ∀ ν, ν < D.nNu →
    W.slot (o.H.tV.sEnd + 4 * ν + 0) =
      ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) (pt ρ o.H.tV.r) ∧
    W.slot (o.H.tV.sEnd + 4 * ν + 1) =
      ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) (pt ρ o.H.tV.r) ∧
    W.slot (o.H.tV.sEnd + 4 * ν + 2) =
      ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) (pt ρ o.H.tV.r) ∧
    W.slot (o.H.tV.sEnd + 4 * ν + 3) =
      ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) (pt ρ o.H.tV.r)
  /-- the left end value of the squares' product layer -/
  sqL : W.slot o.H.wpl.sL =
    ext (P.rd.lNI + o.v.y.lPd - o.v.y.ls + o.v.y.ls + D.lT)
      (Road.K4.sqV o.v.y.NI (o.v.y.h.d / o.v.y.S2 * 2 ^ o.v.y.ls) o.v.y.lPd o.v.y.xb.nl D.lT
        (fun l => ρ.val (o.H.gp.getD l zeroE)) (fun ν l j p => bS D t ν l j p))
      (pt ρ o.H.wpl.r)
  /-- and the right one. THIS FIELD RESTATES ITS CLAIM: the squares' second form is the difference
  of the two slots -/
  sqR : W.slot o.H.wpl.sR = W.slot o.H.wpl.sL
  /-- the values that the second token sumcheck shows. THESE THREE FIELDS RESTATE THEIR CLAIMS: each
  slot holds the worth of its own form IN THE WORLD's ENTRIES OF THE READS. No term of the library
  stands here: whoever proves them shows that the entries which the honest side has read are the
  world's, and that a form's worth at the end point is the extension of its worths at the corners -/
  rt : ∀ tT, o.H.tT = some tT → ∀ i, i < o.v.y.NN * o.v.y.Lam → ∀ x, o.v.rowR "rt" i = some x →
    W.slot (tT.sEnd + i) = x.value ρ W
  sc : ∀ tT, o.H.tT = some tT → ∀ lm, lm < o.v.y.LamM → ∀ x, o.v.shA "sc" "rt" lm 0 = some x →
    W.slot (tT.sEnd + o.v.y.NN * o.v.y.Lam + lm) = x.value ρ W
  sel : ∀ tT, o.H.tT = some tT → ∀ i, i < o.v.y.LamM * o.v.y.h.NE → ∀ x,
    o.v.shA "sel" "rt" (i / o.v.y.h.NE) (i % o.v.y.h.NE) = some x →
    W.slot (tT.sEnd + o.v.y.NN * o.v.y.Lam + o.v.y.LamM + i) = x.value ρ W
  /-- the end values of the two product layers of the gated products -/
  lv1L : W.slot o.hd.sL = ext (D.lL + lF D + D.lT) (slV D t) (pt ρ o.hd.r)
  lv1R : W.slot o.hd.sR = ext (D.lL + lF D + D.lT) (upV D t) (pt ρ o.hd.r)
  lv2L : ∀ o2, o.hd2 = some o2 →
    W.slot o2.sL = ext (D.lL - 1 + lFe D + D.lT) (slV' D t) (pt ρ o2.r)
  lv2R : ∀ o2, o.hd2 = some o2 →
    W.slot o2.sR = ext (D.lL - 1 + lFe D + D.lT) (upV' D t) (pt ρ o2.r)
  /-- in the first group: the embedding's value, as the sum over the stream that comes in. Where the
  slot holds the embedding claim's value on the committed matrix, this field asks that the two sums
  agree. That follows where the stream is the embedding of the tokens (the library's identity j11),
  and from nothing else that is known: A HYPOTHESIS ON THE WITNESS -/
  emb : o.v.g = 0 → W.slot o.sVE =
    ∑ kh ∈ range (o.v.y.h.d / o.v.y.S2), ρ.val ((eqTab o.H.tkh).getD kh zeroE) *
      ∑ r ∈ range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt ρ o.H.ZE) r *
        ext D.lT (fun p => xS D t 0 (kh * 2 ^ o.v.y.ls + r) p) (uEOf ρ o.v o.H)

/-- **The two slots that the run "back" reads outside the own claims of its two sumchecks**: the two
sides' end values of the batched sumcheck are the worths of their forms IN THE WORLD's ENTRIES OF
THE READS. BOTH FIELDS RESTATE THEIR CLAIMS;
whoever proves them shows that the entries which the honest side has read are the world's. This
defines a hypothesis; the definition claims nothing. -/
structure OpenedBack (ρ : Reading K) (W : World K) (o : Own) : Prop where
  sideA : W.slot o.K.sA0 = o.K.fin.Alin.value ρ W
  sideB : W.slot o.K.sB0 = o.K.fin.Blin.value ρ W

/-- **The library's seventeen identities of each norm at the cells t, at every position.** This
defines a hypothesis; the definition claims nothing. -/
structure IdnHold [scl : Scl] (D : Dim) (t : Cell → K) : Prop where
  jn : ∀ ν, ν < D.nNu → ∀ k, k < 17 → ∀ i, i < 2 ^ D.lT →
    idnVal D t (fun _ _ => 0) (fun _ => 0) (.jn k ν i) = 0

section Ground
variable {ρ : Reading K} {W : World K} {h : Layer.Shape} {pc : List (List String)} {v : Env}
  {rd : Reads} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {H : Heard}
  {hd : Level} {hd2 : Option Level} {pts : List (String × Array E)} {funs : Array HFun} {D : Dim}

/-- **Fits and TrueAt3 from the public facts, where every table holds.** CONDITIONAL: on G, hρ, hR.
-/
theorem ground (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) (hρ : Numerals ρ) (Mm : Mats K)
    (hR : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 Mm Fn) :
    ∃ Z1 ZV, lastOf H.fo.zx v.y.h.la = .ok Z1 ∧ lastOf H.wpl.r v.y.h.la = .ok ZV ∧
      Fits (scl := sclOf h v.sc v.g v.y.Lam) ρ W v D (cellsAt v.y Mm)
        (cellsOf D (cellsAt v.y Mm)) (pt ρ Z1) (pt ρ H.ztF) ∧
      TrueAt3 ρ W v D.lT (cellsAt v.y Mm) (pt ρ ZV) (fun j => pt ρ ZV (v.y.ls + j))
        (pt ρ H.PV) (pt ρ H.tV.r) (pt ρ H.ZE) (uEOf ρ v H) := by
  letI : Scl := sclOf h v.sc v.g v.y.Lam
  obtain ⟨Z1, hZ1, T⟩ := trueAt_of_holds ρ W G.lay G.sw G.grp G.reads G.tables G.tab G.mats G.NM
    G.points G.zt G.funs Mm hR
  obtain ⟨ZV, hZV, T3⟩ := trueAt3_of_holds ρ W G.lay G.sw G.grp G.reads G.tables G.tab G.mats G.NM
    G.points G.funs Mm hR
  have sh := (admitted_of_layout G.lay G.sw.p3).shape
  rw [sh] at T
  have F := fits_of_layout_true G.lay G.sw G.scales G.grp G.reads G.tables G.tab hρ G.sized
    (cellsAt v.y Mm) (pt ρ Z1) (pt ρ H.ztF) T
  rw [F.lT] at T3
  exact ⟨Z1, ZV, hZ1, hZV, F, T3⟩

/-- **The same, with TrueAt3 at the squares' own point.** CONDITIONAL: on G, Z, hρ, hR. -/
theorem ground_point {P : Pub} (G : K4Ground h pc v rd r tl H hd hd2 pts funs D)
    (Z : K4Sizes P v H hd hd2 D) (hρ : Numerals ρ) (Mm : Mats K)
    (hR : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 Mm Fn) :
    ∃ Z1, lastOf H.fo.zx v.y.h.la = .ok Z1 ∧
      Fits (scl := sclOf h v.sc v.g v.y.Lam) ρ W v D (cellsAt v.y Mm)
        (cellsOf D (cellsAt v.y Mm)) (pt ρ Z1) (pt ρ H.ztF) ∧
      TrueAt3 ρ W v D.lT (cellsAt v.y Mm) (lowVOf ρ P v H) (uVOf ρ P v H)
        (pt ρ H.PV) (pt ρ H.tV.r) (pt ρ H.ZE) (uEOf ρ v H) := by
  obtain ⟨Z1, ZV, hZ1, hZV, F, T3⟩ := ground G hρ Mm hR
  have hla := Z.la
  have eg : H.wpl.r.size - v.y.h.la = P.rd.lNI + v.y.lPd - v.y.ls := by
    have := Z.wpl
    omega
  have c1 : ∀ j, j < v.y.ls → pt ρ ZV j = lowVOf ρ P v H j := by
    intro j hj
    rw [(Desc.First.K4.lastOf_pt (ρ := ρ) hZV (j := j) (by omega)).2, eg]
    rfl
  have c2 : ∀ j, j < D.lT → pt ρ ZV (v.y.ls + j) = uVOf ρ P v H j := by
    intro j hj
    rw [(Desc.First.K4.lastOf_pt (ρ := ρ) hZV (j := v.y.ls + j) (by omega)).2, eg,
      ← Nat.add_assoc]
    rfl
  exact ⟨Z1, hZ1, F,
    { xiV := fun b hb => Desc.First.K4.longTrue_congr c1 c2 (T3.xiV b hb)
      afV := fun b hb => Desc.First.K4.longTrue_congr c1 c2 (T3.afV b hb)
      arP := T3.arP
      arR := T3.arR
      xiE := T3.xiE }⟩

/-- **NormWords under the scales that sclOf makes.** CONDITIONAL: on G and Fits. -/
theorem ground_words {c : Cells K} {t : Cell → K} {low u : ℕ → K}
    (G : K4Ground h pc v rd r tl H hd hd2 pts funs D)
    (F : Fits (scl := sclOf h v.sc v.g v.y.Lam) ρ W v D c t low u) :
    NormWords (scl := sclOf h v.sc v.g v.y.Lam) v D := by
  letI : Scl := sclOf h v.sc v.g v.y.Lam
  have sh := (admitted_of_layout G.lay G.sw.p3).shape
  have N := normWords_sclOf v D F.NN F.Lam
  rw [sh] at N
  exact N

end Ground

/-- **Every table holds what it says, at the item's own world.** CONDITIONAL: on G. -/
theorem holds_item {h : Layer.Shape} {pc : List (List String)} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {o : Own}
    {pts : List (String × Array E)} {D : Dim}
    (G : K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D) (Mm : Mats Cb.Gl.E) (F' : Fork)
    (mask : ℕ → Cb.Gl.E) :
    ∀ Fn ∈ o.funs, Holds Reading.gl (F'.worldOf Reading.gl mask (entryTrue tl o Mm)) tl o.v.iU3
      o.v.K3 Mm Fn := by
  have hl := G.tables
  rw [← G.mats] at hl
  exact holds_entryOf Reading.gl (apart_of_run hl G.funs G.NM) _ _ Mm rfl

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.ground
#print axioms OnBytes.Road.K4.W.ground_point
#print axioms OnBytes.Road.K4.W.ground_words
#print axioms OnBytes.Road.K4.W.holds_item
