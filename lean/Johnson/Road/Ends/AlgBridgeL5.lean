-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgBridgeL5.lean: the bridge of AlgBridge.lean, under the names of
Johnson/Road/Lane5SplitG.lean; and the seam before the lookup of a group of layers.
States: (layerBridge_of_calls) L5.LayerBridge h P.sc P.y g Mz Wi (callsG ..): AlgBridge.lean's
layerKeys_of_calls, whose conclusion is L5.LayerKeys and whose last premise is CallsAt.InTables at
the letters callsG. (linkOK_of_layerCalls) THE SEAM: the group's meaning without its lookup clause
(L5.LayerR0) and «every call's keys lie in its table» at callsG give L5.LinkOK at link 2 g, at the
library's matrices of the group (with L5.linkOK_of_layerSplit).
What the bridge holds: the keys of callsG are G.lean's key vectors kvG, WHOLE: every product of the
cells with the eleven kinds of weight matrices of a layer, and every product of two cells, stands in
these keys. kvG (OnBytes/Tie/Pv/Lookup/Ends/G.lean) is a term of these files, not a function of the
verifier. The tables are the verifier's own records' rows (tauN).
Mz AND Wi ARE LETTERS: integer matrices of which nothing is asked here. Nothing in these files ties
Wi to a committed matrix of weights, or Mz to what a prover has committed to.
Under: the premises of layerKeys_of_calls (all public, among them hL for every call: the lookup's
record has the library's table); for the seam also Sized2 and g below the number of groups.
The eight lines of calls (h8, hn) are no test of the verifier: it takes other lists; at these this
file says nothing. n is a letter tied to the library's a_c (hnn): Johnson/Road/Lane5ForInG.lean puts
the lookup's own record's n and k there. That L5.LayerR0 and InTables hold together of some Mz, Wi
is not shown here.
Does not say: that the keys do lie in their tables; that L5.LayerR0 holds.
-/
import Johnson.Road.Lane5SplitG
import Johnson.Road.Ends.AlgBridge

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

/-- The letters of the lookup's calls of group g: eight calls; G.lean's key vectors on the casts of
Mz and Wi; the rows of the verifier's records of the calls. n, k: the logarithms of the numbers of
keys and of rows. -/
def callsG (P : Model.Layer.Pub) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat) (n k : ℕ → ℕ) : CallsAt :=
  ⟨8, n, k, fun q => G.kvG P g (cellMW Mz Wi) q, fun q u => ((tauN P.y.fo q u : ℕ) : Cb.Gl.E)⟩

section Bridge

variable {h : Shape} {pc : List (List String)} {P : Model.Layer.Pub} {g : ℕ} {rd : Reads}
  {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **The bridge, under its name.** -/
theorem layerBridge_of_calls (hy : layout h pc = .ok P.y) (S : Switches h)
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
    (n k : ℕ → ℕ) (hnn : ∀ cc : Fin 8, n cc.val = aC DF cc)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc) ∧ k cc.val = c0.k ∧ c0.k = if cc = 3 then 8 else 16)
    (Mz : Mats ℤ) (Wi : Mat) :
    LayerBridge h P.sc P.y g Mz Wi (callsG P g Mz Wi n k) :=
  fun I => layerKeys_of_calls hy S hs hg hrd hl Zd hp4 hev hmats hT ZW hW hgL hrope h8 hn hfl hw n k
    hnn hL Mz Wi I

/-- **The seam before the lookup of group g of layers, at G.lean's key vectors.** -/
theorem linkOK_of_layerCalls (hy : layout h pc = .ok P.y) (S : Switches h)
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
    (n k : ℕ → ℕ) (hnn : ∀ cc : Fin 8, n cc.val = aC DF cc)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc) ∧ k cc.val = c0.k ∧ c0.k = if cc = 3 then 8 else 16)
    {Mz : Mats ℤ} {Wi : Mat} (hgN : g < nGr) (nf : Inst.Model.NormPar) (pol : AcceptancePolicy)
    (x : Cm.Seg.XI) (R : LayerR0 h P.sc P.y g Mz Wi x) (I : (callsG P g Mz Wi n k).InTables) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol (scalesOf h P.sc nf) pol) Wi x (2 * g)
      (libMZ P.y g Mz) :=
  linkOK_of_layerSplit hy S Zd Z2 hp4 hgN P.sc nf pol x
    (layerBridge_of_calls hy S hs hg hrd hl Zd hp4 hev hmats hT ZW hW hgL hrope h8 hn hfl hw n k hnn
      hL Mz Wi) R I

end Bridge

#print axioms layerBridge_of_calls
#print axioms linkOK_of_layerCalls

end OnBytes.Road.Alg
