-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5ForInG.lean

The second clause of the lookup's in-joint at a group of layers, at a caller whose key vectors are
kvG (no such caller is written in this library), in the letters of the lookup's record: and from it
the lookup clause of the group. The lookup's block claims before itself (Cb.Fo.forIn,
OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean; written out as Port.jIn,
OnBytes/Tie/Pv/Lookup/Shift/ShiftQLay.lean): the caller's own joint R0, and for every k below h.NC:
InTable (nOf h k) (kOf h k) (the caller's key vector of call k) (the rows of call k's table off the
verifier's record). The bridge at the layers (Johnson/Road/Ends/AlgBridgeL5.lean) speaks at callsG P
g Mz Wi n k: eight calls, with n and k letters, n tied to the library's a_c. Here both are the
record's own.

This file imports none of the lookup's files. The record's readings are those of
Johnson/Road/Lane5Rec.lean (nF, tauF) and OnBytes/Tie/Pv/Lookup/Ends/Joint.lean (kN), typed with the
bodies that nOf, tauN and kOf have there by a reading; nothing here compiles the two together.

Main definitions and theorems:
* "ForInG P g Mz Wi": that clause at h := P.y.fo and the key vectors kvG
  (OnBytes/Tie/Pv/Lookup/Ends/G.lean: terms of this library, no function of the verifier's) on the
  casts of the integer matrices Mz and Wi.
* "forInG_iff_inTables": for every layout that the verifier's function layout returns with eight
  calls: ForInG is (callsG P g Mz Wi (nF P.y.fo) (kN P.y.fo)).InTables. No premise on fo: that fo
  holds the layout's records, and as many as the layout has calls, is fo_of_layout
  (Johnson/Road/FormsKeysShape.lean).
* "nF_eq_aC": the record's n of call cc is the library's a_c, by n_of_layout
  (Johnson/Road/FormsKeysLook.lean), under the lines of calls hn and the floor hfl.
* **"layerKeys_of_forIn"**: ForInG gives L5.LayerKeys, under the public premises of
  layerBridge_of_calls without the letters n, k, without hnn, and with hL's clause "k is c0's"
  gone.
* "linkOK_of_forInG": the seam: L5.LayerR0 and ForInG give L5.LinkOK at link 2 g.

Of the public premises: no theorem shows that they hold together; what a test and a run show of it
is told in the head of Johnson/Road/Lane5LayerSeamTrue.lean. The premise hn, that the eight lines of
calls name the library's families in order, is no test of the verifier: a configuration that it
admits may have other lines, and then nothing is said.

Not claimed: ForInG for a proof that a verifier accepts; all that Johnson/Road/Ends/AlgBridgeL5.lean
does not claim.

-/
import Johnson.Road.FormsKeysLook
import Johnson.Road.Ends.AlgBridgeL5
import Johnson.Road.Lane5Rec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Road.L5
open OnBytes.Model (Seg CallD Call WsShape wsLayOf)
open OnBytes.Model.Layer (Lay Shape Scales Reads TableAsk TableAt Ten layout scalesHeld readsOf
  layTables tableAsks)
open Inst.Model (Scl Tables Mat ppref tbRef AcceptancePolicy)
open Inst.Model.All (DF nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Fam fams used aC lut)

/-- **The second clause of the lookup's own in-joint, at the key vectors of group g.** -/
def ForInG (P : Model.Layer.Pub) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat) : Prop :=
  ∀ k < P.y.fo.NC, Cb.Lkp.InTable (nF P.y.fo k) (kN P.y.fo k) (G.kvG P g (cellMW Mz Wi) k)
    (fun t => ((tauF P.y.fo k t : ℕ) : Cb.Gl.E))

section

variable {h : Shape} {pc : List (List String)} {P : Model.Layer.Pub} {g : ℕ} {rd : Reads}
  {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **The lookup's clause is "every call's keys lie in its table" at callsG, with the record's own
n and k.** -/
theorem forInG_iff_inTables (hy : layout h pc = .ok P.y) (h8 : P.y.calls.size = 8) (Mz : Mats ℤ)
    (Wi : Mat) :
    ForInG P g Mz Wi ↔ (callsG P g Mz Wi (nF P.y.fo) (kN P.y.fo)).InTables := by
  obtain ⟨e1, e2, e3⟩ := fo_of_layout hy
  have hNC : P.y.fo.NC = 8 := by rw [e2, e3, h8]
  have hsz : P.y.fo.calls.size = 8 := by rw [e1, e3, h8]
  constructor
  · intro H k hk
    have hk8 : k < 8 := hk
    intro b hb
    obtain ⟨u, hu, e⟩ := H k (by rw [hNC]; exact hk8) b hb
    have e' : G.kvG P g (cellMW Mz Wi) k b = ((tauF P.y.fo k u : ℕ) : Cb.Gl.E) := e
    refine ⟨u, hu, ?_⟩
    show G.kvG P g (cellMW Mz Wi) k b = ((tauN P.y.fo k u : ℕ) : Cb.Gl.E)
    rw [e', tauF_eq (by rw [hsz]; exact hk8)]
  · intro H k hk
    have hk8 : k < 8 := by rw [hNC] at hk; exact hk
    intro b hb
    obtain ⟨u, hu, e⟩ := H k hk8 b hb
    have e' : G.kvG P g (cellMW Mz Wi) k b = ((tauN P.y.fo k u : ℕ) : Cb.Gl.E) := e
    refine ⟨u, hu, ?_⟩
    show G.kvG P g (cellMW Mz Wi) k b = ((tauF P.y.fo k u : ℕ) : Cb.Gl.E)
    rw [e', tauF_eq (by rw [hsz]; exact hk8)]

/-- **The record's n of call cc is the library's a_c.** -/
theorem nF_eq_aC (hy : layout h pc = .ok P.y) (S : Switches h) {D : Dim} (Zd : Sized h D)
    (h8 : P.y.calls.size = 8)
    (hn : ∀ (cc : Fin 8) (cd : CallD), P.y.calls[cc.val]? = some cd →
      cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) (cc : Fin 8) :
    nF P.y.fo cc.val = aC D cc := by
  have hc8 : cc.val < P.y.calls.size := by
    rw [h8]
    exact cc.isLt
  have hcq : P.y.calls[cc.val]? = some P.y.calls[cc.val] := Array.getElem?_eq_getElem hc8
  have e := n_of_layout (v := envG P 0 []) hy S Zd hcq (hn cc _ hcq) (hfl cc)
  have e' : (P.y.cl[cc.val]?).map (·.n) = some (aC D cc) := e
  unfold nF
  rw [(fo_of_layout hy).1, e']
  rfl

/-- **From the clause ForInG to the lookup clause of the group.** -/
theorem layerKeys_of_forIn (hy : layout h pc = .ok P.y) (S : Switches h)
    (hs : scalesHeld h P.sc = .ok ()) (hg : g < P.y.NGr) (hrd : readsOf P.y = .ok rd)
    (hl : layTables mats (tableAsks P.y rd g) 0 = some r) (Zd : Sized h DF)
    (hp4 : h.p4 = true) (hev : h.dh % 2 = 0)
    (hmats : ∀ (n : String) (Tn : Ten), P.y.T_ n = some Tn → Tn.mat < 4)
    (hT : P.y.T = DF.T) {s : WsShape} (ZW : SizedW s ppref)
    (hW : wsLayOf s true kRef = .ok P.wsLay)
    (hgL : ∀ l < DF.nl, g * P.y.Lam + l < ppref.layers)
    (hrope : ropeOK P DF tbRef (g * P.y.Lam) = true)
    (h8 : P.y.calls.size = 8)
    (hn : ∀ (cc : Fin 8) (cd : CallD), P.y.calls[cc.val]? = some cd →
      cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used DF cc))
    (hw : ∀ cd ∈ P.y.calls, ∃ wg, (envG P g r.1).weighedOf cd = some wg)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc) ∧ c0.k = if cc = 3 then 8 else 16)
    (Mz : Mats ℤ) (Wi : Mat) (I : ForInG P g Mz Wi) : LayerKeys h P.sc P.y g Mz Wi :=
  layerBridge_of_calls hy S hs hg hrd hl Zd hp4 hev hmats hT ZW hW hgL hrope h8 hn hfl hw
    (nF P.y.fo) (kN P.y.fo) (nF_eq_aC hy S Zd h8 hn hfl)
    (fun cc => by
      obtain ⟨c0, h0, h1, h2⟩ := hL cc
      refine ⟨c0, h0, h1, ?_, h2⟩
      unfold kN
      rw [h0]
      rfl)
    Mz Wi ((forInG_iff_inTables hy h8 Mz Wi).1 I)

/-- **The seam before the lookup of group g of layers, from the clause ForInG.** -/
theorem linkOK_of_forInG (hy : layout h pc = .ok P.y) (S : Switches h)
    (hs : scalesHeld h P.sc = .ok ()) (hg : g < P.y.NGr) (hrd : readsOf P.y = .ok rd)
    (hl : layTables mats (tableAsks P.y rd g) 0 = some r) (Zd : Sized h DF) (Z2 : Sized2 h DF)
    (hp4 : h.p4 = true) (hev : h.dh % 2 = 0)
    (hmats : ∀ (n : String) (Tn : Ten), P.y.T_ n = some Tn → Tn.mat < 4)
    (hT : P.y.T = DF.T) {s : WsShape} (ZW : SizedW s ppref)
    (hW : wsLayOf s true kRef = .ok P.wsLay)
    (hgL : ∀ l < DF.nl, g * P.y.Lam + l < ppref.layers)
    (hrope : ropeOK P DF tbRef (g * P.y.Lam) = true)
    (h8 : P.y.calls.size = 8)
    (hn : ∀ (cc : Fin 8) (cd : CallD), P.y.calls[cc.val]? = some cd →
      cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used DF cc))
    (hw : ∀ cd ∈ P.y.calls, ∃ wg, (envG P g r.1).weighedOf cd = some wg)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc) ∧ c0.k = if cc = 3 then 8 else 16)
    {Mz : Mats ℤ} {Wi : Mat} (hgN : g < nGr) (nf : Inst.Model.NormPar) (pol : AcceptancePolicy)
    (x : Cm.Seg.XI) (R : LayerR0 h P.sc P.y g Mz Wi x) (I : ForInG P g Mz Wi) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf h P.sc nf) pol) Wi x (2 * g)
      (libMZ P.y g Mz) :=
  linkOK_of_layerSplit (C := callsG P g Mz Wi (nF P.y.fo) (kN P.y.fo)) hy S Zd Z2 hp4 hgN P.sc nf
    pol x
    (fun _ => layerKeys_of_forIn hy S hs hg hrd hl Zd hp4 hev hmats hT ZW hW hgL hrope h8 hn hfl hw
      hL Mz Wi I)
    R ((forInG_iff_inTables hy h8 Mz Wi).1 I)

end

#print axioms forInG_iff_inTables
#print axioms nF_eq_aC
#print axioms layerKeys_of_forIn
#print axioms linkOK_of_forInG

end OnBytes.Road.Alg
