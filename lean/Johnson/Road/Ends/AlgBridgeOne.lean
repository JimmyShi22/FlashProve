-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgBridgeOne.lean: the lookup clause of a group of layers, and the seam before its
lookup, from the clause ForInG and one test.
States: (layerKeys_of_forInTest) four returns of the verifier's functions (layout, readsOf,
layTables, wsLayOf), the one test bridgeB (AlgBridgeTest.lean), hL, and ForInG P g Mz Wi
(Johnson/Road/Lane5ForInG.lean: every call's keys of kvG lie in the call's table, with the numbers n
and k of the lookup's own record) give L5.LayerKeys (Johnson/Road/Lane5SplitG.lean).
(linkOK_of_forInTest) with L5.LayerR0, the seam: L5.LinkOK at link 2 g.
(layerKeys_of_forInRecord, linkOK_of_forInRecord) THE SAME AT ONE RECORD: the public part X that the
verifier's publicOf returns, and the one test recordB X g (AlgBridgeRec.lean): there the letters
mats, rd, r, s are bound: mats is the group's own list of matrices (matsR), rd and r are what
readsOf and layTables return on X's layout, s is weightShape X.P X.y.
hL: for every call the lookup's record fo.calls[cc] has the library's table (Hd.IsLut).
(layerKeys_of_one, linkOK_of_one) WITH hL GONE: recordOneB X g is recordB X g and the test tablesB
(AlgTabs.lean), which walks through all rows of the eight tables; hL_of_tablesB draws hL from it. So
at publicOf's record the lookup clause follows from one test and the clause ForInG.
WHAT «THE TEST SAYS TRUE» RESTS ON: for the tables and the numbers, on a run of a program at one
pair of configuration files: no theorem, and usable in no proof. THE STEP FROM THE TEST TO THE
PREMISES IS A THEOREM.
Limits: those of AlgBridgeL5.lean and of Johnson/Road/Lane5ForInG.lean: kvG is a term of these
files; Mz and Wi are letters; the eight lines of calls are no test of the verifier.
Does not say: that ForInG holds of a proof that a verifier accepts; that L5.LayerR0 and ForInG hold
together of some Mz, Wi; that the tests are true anywhere (a run decides that).
-/
import Johnson.Road.Lane5ForInG
import Johnson.Road.Ends.AlgBridgeRec
import Johnson.Road.Ends.AlgTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Road.L5
open OnBytes.Model (Call WsShape wsLayOf)
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Model.Layer (Reads TableAsk TableAt layout readsOf layTables tableAsks)
open Inst.Model (Mat tbRef AcceptancePolicy)
open Inst.Model.All (DF nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (lut)

section Test

variable {h : Model.Layer.Shape} {pc : List (List String)} {P : Model.Layer.Pub} {g : ℕ}
  {rd : Reads} {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **Four returns, one test, hL and the clause ForInG give the lookup clause of the group.**
-/
theorem layerKeys_of_forInTest (hy : layout h pc = .ok P.y) (hrd : readsOf P.y = .ok rd)
    (hl : layTables mats (tableAsks P.y rd g) 0 = some r) {s : WsShape}
    (hW : wsLayOf s true kRef = .ok P.wsLay) (t : bridgeB h P g s r.1 = true)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc))
    (Mz : Mats ℤ) (Wi : Mat) (I : ForInG P g Mz Wi) : LayerKeys h P.sc P.y g Mz Wi := by
  obtain ⟨S, Zd, h8, hn, hfl⟩ := bridgeB_parts t
  refine layerKeys_of_test hy hrd hl hW t hL Mz Wi fun q hq => ?_
  have e : nG q = nF P.y.fo q := by
    unfold nG
    rw [dif_pos hq]
    exact (nF_eq_aC hy S Zd h8 hn hfl ⟨q, hq⟩).symm
  rw [e]
  exact (forInG_iff_inTables hy h8 Mz Wi).1 I q hq

/-- **The seam before the lookup of group g of layers.** -/
theorem linkOK_of_forInTest (hy : layout h pc = .ok P.y) (hrd : readsOf P.y = .ok rd)
    (hl : layTables mats (tableAsks P.y rd g) 0 = some r) {s : WsShape}
    (hW : wsLayOf s true kRef = .ok P.wsLay) (t : bridgeB h P g s r.1 = true)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc))
    (Z2 : Sized2 h DF) (hp4 : h.p4 = true) {Mz : Mats ℤ} {Wi : Mat} (hgN : g < nGr)
    (nf : Inst.Model.NormPar) (pol : AcceptancePolicy) (x : Cm.Seg.XI) (R : LayerR0 h P.sc P.y g Mz Wi x)
    (I : ForInG P g Mz Wi) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf h P.sc nf) pol) Wi x (2 * g)
      (libMZ P.y g Mz) := by
  obtain ⟨S, Zd, h8, -, -⟩ := bridgeB_parts t
  exact linkOK_of_layerSplit (C := callsG P g Mz Wi (nF P.y.fo) (kN P.y.fo)) hy S Zd Z2 hp4 hgN P.sc
    nf pol x (fun _ => layerKeys_of_forInTest hy hrd hl hW t hL Mz Wi I) R
    ((forInG_iff_inTables hy h8 Mz Wi).1 I)

end Test

section Record

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {g : ℕ}

/-- What the record and its test give: the four returns and bridgeB, at X's own letters. -/
theorem returns_of_record (h : publicOf pol KL lay = .ok X) (t : recordB X g = true) :
    layout (layerShape X.P) X.P.polCalls = .ok X.layers.y ∧
      ∃ (rd : Reads) (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ),
        readsOf X.layers.y = .ok rd ∧
        layTables (matsR X.layers.y g) (tableAsks X.layers.y rd g) 0 = some r ∧
        wsLayOf (Model.Verify.weightShape X.P X.y) true kRef = .ok X.layers.wsLay ∧
        bridgeB (layerShape X.P) X.layers g (Model.Verify.weightShape X.P X.y) r.1 = true := by
  obtain ⟨hk, rd, r, hrd, hl, tb⟩ := recordB_parts t
  have B := Hd.publicH_of_public h
  have S := (bridgeB_parts tb).1
  have A := admitted_of_layout B.lay S.p3
  have hW : wsLayOf (Model.Verify.weightShape X.P X.y) true kRef = .ok X.layers.wsLay := by
    have e := B.ws
    rw [A.shape, S.p3, hk] at e
    exact e
  exact ⟨B.lay, rd, r, hrd, hl, hW, tb⟩

/-- **At publicOf's own record: one test, hL and the clause ForInG.** -/
theorem layerKeys_of_forInRecord (h : publicOf pol KL lay = .ok X) (t : recordB X g = true)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, X.layers.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc))
    (Mz : Mats ℤ) (Wi : Mat) (I : ForInG X.layers g Mz Wi) :
    LayerKeys (layerShape X.P) X.layers.sc X.layers.y g Mz Wi := by
  obtain ⟨hy, rd, r, hrd, hl, hW, tb⟩ := returns_of_record h t
  exact layerKeys_of_forInTest (P := X.layers) hy hrd hl hW tb hL Mz Wi I

/-- **The seam at publicOf's own record.** -/
theorem linkOK_of_forInRecord (h : publicOf pol KL lay = .ok X) (t : recordB X g = true)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, X.layers.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc))
    (Z2 : Sized2 (layerShape X.P) DF) (hp4 : (layerShape X.P).p4 = true) {Mz : Mats ℤ} {Wi : Mat}
    (hgN : g < nGr) (nf : Inst.Model.NormPar) (pl : AcceptancePolicy) (x : Cm.Seg.XI)
    (R : LayerR0 (layerShape X.P) X.layers.sc X.layers.y g Mz Wi x)
    (I : ForInG X.layers g Mz Wi) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf (layerShape X.P) X.layers.sc nf) pl) Wi x
      (2 * g) (libMZ X.layers.y g Mz) := by
  obtain ⟨hy, rd, r, hrd, hl, hW, tb⟩ := returns_of_record h t
  exact linkOK_of_forInTest (P := X.layers) hy hrd hl hW tb hL Z2 hp4 hgN nf pl x R I

/-- **One test at the record X and group g**: recordB, and the eight tables (AlgTabs.lean). -/
def recordOneB (X : Public) (g : ℕ) : Bool := recordB X g && tablesB X.layers.y

/-- **At publicOf's own record: one test and the clause ForInG; no premise more.** -/
theorem layerKeys_of_one (h : publicOf pol KL lay = .ok X) (t : recordOneB X g = true)
    (Mz : Mats ℤ) (Wi : Mat) (I : ForInG X.layers g Mz Wi) :
    LayerKeys (layerShape X.P) X.layers.sc X.layers.y g Mz Wi := by
  unfold recordOneB at t
  rw [Bool.and_eq_true] at t
  exact layerKeys_of_forInRecord h t.1 (hL_of_tablesB t.2) Mz Wi I

/-- **The seam at publicOf's own record, from one test.** -/
theorem linkOK_of_one (h : publicOf pol KL lay = .ok X) (t : recordOneB X g = true)
    (Z2 : Sized2 (layerShape X.P) DF) (hp4 : (layerShape X.P).p4 = true) {Mz : Mats ℤ} {Wi : Mat}
    (hgN : g < nGr) (nf : Inst.Model.NormPar) (pl : AcceptancePolicy) (x : Cm.Seg.XI)
    (R : LayerR0 (layerShape X.P) X.layers.sc X.layers.y g Mz Wi x)
    (I : ForInG X.layers g Mz Wi) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf (layerShape X.P) X.layers.sc nf) pl) Wi x
      (2 * g) (libMZ X.layers.y g Mz) := by
  unfold recordOneB at t
  rw [Bool.and_eq_true] at t
  exact linkOK_of_forInRecord h t.1 (hL_of_tablesB t.2) Z2 hp4 hgN nf pl x R I

end Record

#print axioms layerKeys_of_forInTest
#print axioms linkOK_of_forInTest
#print axioms layerKeys_of_forInRecord
#print axioms linkOK_of_forInRecord
#print axioms layerKeys_of_one
#print axioms linkOK_of_one

end OnBytes.Road.Alg
