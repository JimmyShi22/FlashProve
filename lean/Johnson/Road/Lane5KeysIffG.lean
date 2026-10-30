-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5KeysIffG.lean

The bridge at the layers, the other way: the lookup clause of a group of layers gives "every call's
keys lie in its table"; so the two say the same, and the whole meaning of the group is: its part
without the lookup clause, and the clause ForInG. L5.LayerR0 is the light part. The keys are formed
from products: the clause ForInG, at kvG, holds every product with a weight matrix
(Johnson/Road/Lane5Split.lean). The equivalence moves that weight; it does not carry it.

The bridge (Johnson/Road/Ends/AlgIn.lean, Johnson/Road/Ends/AlgBridge.lean) rests on an equation of
vectors: the library's key vector of a call is kvG (OnBytes/Tie/Pv/Lookup/Ends/G.lean: a term of
this library, no function of the verifier's) at every index below 2^(a_c), the padding included
(keyVec_kvG, Johnson/Road/Ends/AlgKey.lean); and on Hd.IsLut: the verifier's record of the call has
the library's table, row by row. Both can be read from right to left.

Main theorems:
* "inTable_of_callKey": one call: the converse of callKey_of_inTable, under its premises.
* "calls_of_layerKeys": L5.LayerKeys gives InTable for all eight calls: the converse of
  layerKeys_of_calls, under its premises.
* **"forInG_iff_keys"**: ForInG P g Mz Wi ↔ L5.LayerKeys h P.sc P.y g Mz Wi
  (Johnson/Road/Lane5ForInG.lean: the clause on keys in the letters of the lookup's record).
* **"layerOrd_iff_forIn"**: LayerOrd h P.sc P.y g Mz Wi x ↔ L5.LayerR0 .. ∧ ForInG P g Mz Wi.
Use: from left to right it carries a witness: matrices that meet LayerOrd meet both premises of the
seam before the lookup (linkOK_of_forInG) together.

Under the public premises of layerKeys_of_forIn. No theorem shows that they hold together; what a
test and a run show of it is told in the head of Johnson/Road/Lane5LayerSeamTrue.lean. The premise
hn, that the eight lines of calls name the library's families in order, is no test of the verifier:
a configuration that it admits may have other lines, and then nothing is said.
Not claimed: all that Johnson/Road/Lane5ForInG.lean does not claim. That some matrices meet LayerOrd
is not shown here: Johnson/Road/Lane5LayerSeamTrue.lean shows it for every true request.

-/
import Johnson.Road.Lane5ForInG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Road.L5
open OnBytes.Model (Seg CallD Call WsShape wsLayOf)
open OnBytes.Model.Layer (Env Lay Shape Scales Reads TableAsk TableAt Ten layout scalesHeld readsOf
  layTables tableAsks)
open Inst.Model (Scl Tables Mat ppref tbRef AcceptancePolicy)
open Inst.Model.All (DF nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell Fam LW fams used aC lut keyVec layerR)

section One

variable [scl : Scl] {v : Env} {D : Dim} {t : Cell → Cb.Gl.E} {P : Model.Layer.Pub} {g : ℕ}
  {cell : G.NameG → Cb.Gl.E}

/-- **From the library's clause to "the keys of kvG lie in the verifier's table", at one call.** -/
theorem inTable_of_callKey {tb : Tables} {L0 : ℕ} {w : ℕ → LW Cb.Gl.E} (T : TiesG P g cell D t)
    (Wt : TiesW P g cell D t (tbG P) L0 (wOfG P g cell)) (A : AgreeW D w (wOfG P g cell))
    (B : AgreeT D tb (tbG P) L0) (hffe : D.f = D.fe + D.fe) (hch : 0 < D.P.ch) {q : ℕ}
    {cd : CallD} {weighed : Array Bool} {cc : Fin 8}
    {fam : Seg → Fam} (C : CallFits v D cd weighed cc fam)
    (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hcd : P.y.calls.getD q default = cd) (hT : P.y.T = D.T)
    {c0 : Call} (hc0 : P.y.fo.calls[q]? = some c0) (hL : Hd.IsLut c0 (lut tb cc)) {Tq : ℕ}
    (hrows : (lut tb cc).rows = 2 ^ Tq) {n k : ℕ} (hn : n = aC D cc) (hk : k = c0.k)
    (hKey : ∀ X, X < 2 ^ aC D cc → ∃ u ∈ (Cm.Seg.tabOf (lut tb cc) Tq : Cb.Tab Cb.Gl.F).set,
      keyVec D t tb L0 w cc X = algebraMap Cb.Gl.F Cb.Gl.E u) :
    Cb.Lkp.InTable n k (G.kvG P g cell q) (fun u => ((tauN P.y.fo q u : ℕ) : Cb.Gl.E)) := by
  intro X hX
  have hX' : X < 2 ^ aC D cc := by rw [← hn]; exact hX
  obtain ⟨u, hu, e⟩ := hKey X hX'
  obtain ⟨ι, hι, rfl⟩ := (Cm.Seg.mem_tabOf_iff hrows u).mp hu
  obtain ⟨m, hm1, hm2⟩ := hL.row ι hι
  have ht : tauN P.y.fo q ι = (c0.tauAt ι).toNat := by
    unfold tauN
    rw [hc0]
    rfl
  refine ⟨ι, by rw [hk, hL.rows]; exact hι, ?_⟩
  rw [← keyVec_kvG T Wt A B hffe hch C HS hcd hT (padG_of_isLut hc0 hL) X hX', e]
  show algebraMap Cb.Gl.F Cb.Gl.E (((lut tb cc).row ι : ℤ) : Cb.Gl.F) =
    ((tauN P.y.fo q ι : ℕ) : Cb.Gl.E)
  rw [ht, hm1, word_cast, map_intCast, ← hm2, Int.cast_natCast]

end One

section All

variable {h : Shape} {pc : List (List String)} {P : Model.Layer.Pub} {g : ℕ} {rd : Reads}
  {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **From the lookup clause of the group to the calls' tables.** -/
theorem calls_of_layerKeys (hy : layout h pc = .ok P.y) (S : Switches h)
    (hs : scalesHeld h P.sc = .ok ()) (hg : g < P.y.NGr) (hrd : readsOf P.y = .ok rd)
    (hl : layTables mats (tableAsks P.y rd g) 0 = some r) (Zd : Sized h Dim.ref)
    (hp4 : h.p4 = true) (hev : h.dh % 2 = 0)
    (hmats : ∀ (n : String) (Tn : Ten), P.y.T_ n = some Tn → Tn.mat < 4)
    (hT : P.y.T = Dim.ref.T) {s : WsShape} (ZW : SizedW s ppref)
    (hW : wsLayOf s true kRef = .ok P.wsLay)
    (hgL : ∀ l < Dim.ref.nl, g * P.y.Lam + l < ppref.layers)
    (hrope : ropeOK P Dim.ref tbRef (g * P.y.Lam) = true)
    (h8 : P.y.calls.size = 8)
    (hn : ∀ (cc : Fin 8) (cd : CallD), P.y.calls[cc.val]? = some cd →
      cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used Dim.ref cc))
    (hw : ∀ cd ∈ P.y.calls, ∃ wg, (envG P g r.1).weighedOf cd = some wg)
    (n k : ℕ → ℕ) (hnn : ∀ cc : Fin 8, n cc.val = aC Dim.ref cc)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc) ∧ k cc.val = c0.k ∧ c0.k = if cc = 3 then 8 else 16)
    (Mz : Mats ℤ) (Wi : Mat) (hK : LayerKeys h P.sc P.y g Mz Wi) :
    (callsG P g Mz Wi n k).InTables := by
  intro q hq
  have hq8 : q < 8 := hq
  obtain ⟨c, rfl⟩ : ∃ c : Fin 8, c.val = q := ⟨⟨q, hq8⟩, rfl⟩
  have hch : 0 < ppref.ch := by decide
  obtain ⟨hLam, hffe, Ti, Wt, Aw⟩ := ties_of_lines (D := Dim.ref) rfl rfl hch hy S hs hg hrd hl Zd
    hp4 hev hmats ZW hW hgL Mz Wi
  letI : Scl := sclOf h P.sc g 4
  have B := agreeT_of_ropeOK hrope
  have hc8 : c.val < P.y.calls.size := by
    rw [h8]
    exact c.isLt
  obtain ⟨cd, hcq⟩ : ∃ cd, P.y.calls[c.val]? = some cd := ⟨_, Array.getElem?_eq_getElem hc8⟩
  have hmem : cd ∈ P.y.calls := Array.mem_of_getElem? hcq
  obtain ⟨wg, hwg⟩ := hw cd hmem
  obtain ⟨C, HS⟩ := callFits_of_layout (v := envG P g r.1) hy S Zd hmem (hn c cd hcq) (hfl c) hwg
  obtain ⟨c0, hc0, hLc, hk, hk16⟩ := hL c
  have hrows : (lut tbRef c).rows = 2 ^ (if c = 3 then 8 else 16) := by
    rw [← hLc.rows, hk16]
  have hcdP : P.y.calls.getD c.val default = cd := by
    rw [Array.getD_eq_getD_getElem?, hcq]
    rfl
  have hKey : ∀ X, X < 2 ^ aC Dim.ref c →
      ∃ u ∈ (Cm.Seg.tabOf (lut tbRef c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
        keyVec Dim.ref (cellsOf Dim.ref (cG P (cellMW Mz Wi))) tbRef (g * P.y.Lam)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (g * P.y.Lam + l))
            c X = algebraMap Cb.Gl.F Cb.Gl.E u := by
    intro X hX
    rw [cellsOf_congr Dim.ref (cG_cellsAt P (M := fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun _ _ _ => rfl)), hLam, Nat.mul_comm g 4]
    exact hK c X hX
  exact inTable_of_callKey Ti Wt Aw B hffe hch C HS hcdP hT hc0 hLc hrows (hnn c) hk hKey

/-- **The clause ForInG at a group of layers is the lookup clause of the group.** -/
theorem forInG_iff_keys (hy : layout h pc = .ok P.y) (S : Switches h)
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
    (Mz : Mats ℤ) (Wi : Mat) : ForInG P g Mz Wi ↔ LayerKeys h P.sc P.y g Mz Wi :=
  ⟨layerKeys_of_forIn hy S hs hg hrd hl Zd hp4 hev hmats hT ZW hW hgL hrope h8 hn hfl hw hL Mz Wi,
    fun hK => (forInG_iff_inTables hy h8 Mz Wi).2
      (calls_of_layerKeys hy S hs hg hrd hl Zd hp4 hev hmats hT ZW hW hgL hrope h8 hn hfl hw
        (nF P.y.fo) (kN P.y.fo) (nF_eq_aC hy S Zd h8 hn hfl)
        (fun cc => by
          obtain ⟨c0, h0, h1, h2⟩ := hL cc
          refine ⟨c0, h0, h1, ?_, h2⟩
          unfold kN
          rw [h0]
          rfl)
        Mz Wi hK)⟩

/-- **A group of layers is in order if and only if its part without the lookup clause holds and the
clause ForInG holds.** -/
theorem layerOrd_iff_forIn (hy : layout h pc = .ok P.y) (S : Switches h)
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
    (Mz : Mats ℤ) (Wi : Mat) (x : Cm.Seg.XI) :
    LayerOrd h P.sc P.y g Mz Wi x ↔ LayerR0 h P.sc P.y g Mz Wi x ∧ ForInG P g Mz Wi := by
  rw [layerOrd_iff_split, forInG_iff_keys hy S hs hg hrd hl Zd hp4 hev hmats hT ZW hW hgL hrope h8
    hn hfl hw hL Mz Wi]

end All

#print axioms inTable_of_callKey
#print axioms calls_of_layerKeys
#print axioms forInG_iff_keys
#print axioms layerOrd_iff_forIn

end OnBytes.Road.Alg
