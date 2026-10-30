-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgBridge.lean: the bridge from a lookup's calls to the key vectors of a group of
layers.
G.lean is OnBytes/Tie/Pv/Lookup/Ends/G.lean: a file of terms written for these files over the
verifier's records; no function of the verifier returns them.
States: (layerKeys_of_calls) **If every call's keys of G.lean's key vectors lie in the verifier's
table of that call, the lookup clause of a group of layers holds**: the clause «key» of LayerOrd
(Johnson/Road/FormsKeysLinkL.lean; L5.LayerKeys of Johnson/Road/Lane5SplitG.lean), written out
(Johnson/Road/Ends/AlgBridgeL5.lean concludes it under that name): at the library's reference sizes,
tables and layout of the weights, on the casts of integer matrices Mz (the group's list) and Wi (the
weights).
G.lean's reading is cellMW Mz Wi: the casts at G.lean's own names.
No world stands in the statement: the record Fits is met inside at the world worldAt
(fits_of_layout), and only what it says of public numbers and of places is used (ties_of_fits).
Discharged inside: TiesG (ties_of_fits), TiesW (tiesW_of_laid, ten_of), AgreeW (agreeW_layerR),
AgreeT (agreeT_of_ropeOK), CallFits and SegFits (callFits_of_layout), the padding keys, cG = cellsAt
on the six matrices that a cell's name can reach (cG_cellsAt, cellsOf_congr).
Left as premises, all public: four returns of the verifier's functions (layout, scalesHeld, readsOf,
layTables); the switches; the group's number; sizes that agree with the shape; profile 4; an even
width of a head; every tensor in one of the four families; as many tokens; SizedW and wsLayOf's
return; the group's layers below the model's; ropeOK (one Bool); the eight lines of calls, the floor
hfl, weighedOf's returns (at envG: weighedOf reads of an environment its layout alone:
OnBytes/Model/LayerForms.lean); the letters n, k; and hL. No theorem shows that they hold together.
Those that a program can decide are one test with its theorem (recordOneB,
Johnson/Road/Ends/AlgBridgeOne.lean), and a run of it:
Johnson/Road/Ends/GuardRec.lean.
mats is a free letter: any array for which layTables returns will do; of what layTables returns only
the tables' places r.1 are used.
hL: for every call the lookup's record fo.calls[cc] has the library's table (Hd.IsLut), k is its k,
and that is 8 at call 3 and 16 elsewhere. Johnson/Road/Ends/AlgBridgeTest.lean concludes the two
clauses on k from Hd.IsLut; Johnson/Road/Ends/AlgTabs.lean draws Hd.IsLut of the eight records from
one test that walks through all rows of the tables.
The eight lines of calls (h8, hn) are no test of the verifier: it takes other lists; at these this
file says nothing.
n is the library's a_c (hnn); that the lookup's record has it is not said here: nF_eq_aC
(Johnson/Road/Lane5ForInG.lean). That hIn holds of some Mz, Wi is not shown here: for every true
request, Johnson/Road/Lane5LayerSeamTrue.lean.
Mind: hfl fails at the small example's shape for four calls; at the full size it is hfl_ref
(Johnson/Road/FormsKeysRef.lean).
What the verifier's own key forms are worth beside G.lean's terms, with the products left out:
Johnson/Road/Ends/AlgRun.lean [not in this library] (alg_call_run).
Does not say: that the keys do lie in their tables; anything on identities or on smallness.
-/
import Johnson.Road.FormsKeysKV
import Johnson.Road.Ends.AlgIn
import Johnson.Road.Ends.AlgW
import Johnson.Road.Ends.AlgRope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Model (Reading Seg CallD Call WsShape wsLayOf)
open OnBytes.Model.Layer (Env Lay Shape Reads TableAsk TableAt Ten layout scalesHeld readsOf
  layTables tableAsks)
open Inst.Model (Scl Tables Mat ppref tbRef)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Fam fams used aC lut keyVec layerR)

/-- G.lean's reading from integer matrices: the casts of the group's list and of the weights. -/
def cellMW (Mz : Mats ℤ) (Wi : Mat) : G.NameG → Cb.Gl.E
  | .cell a r c => ((Mz a r c : ℤ) : Cb.Gl.E)
  | .w r c => ((Wi r c : ℤ) : Cb.Gl.E)

/-- The environment of group g with P's layout and scales; no point, no array of reads. -/
def envG (P : Model.Layer.Pub) (g : ℕ) (tab : List TableAt) : Env := ⟨P.y, P.sc, g, 0, 0, tab, #[]⟩

section Cells

variable {K : Type} [Field K]

omit [Field K] in
/-- G.lean's place of a feature in a family of matrices, in the letters of cellsAt. -/
theorem cellAt_eq' {cell : G.NameG → K} {M : Mats K} (hc : ∀ a r c, cell (.cell a r c) = M a r c)
    (M0 m k T φ i : ℕ) :
    cell (G.cellAt M0 m k T φ i) =
      M (M0 + φ / (m / T) / k) (φ % (m / T) * T + i) (φ / (m / T) % k) := by
  unfold G.cellAt
  rw [hc, Nat.div_div_eq_div_mul, Nat.mul_comm k]

omit [Field K] in
/-- **G.lean's places are those of cellsAt**, on the six matrices. -/
theorem cG_cellsAt (P : Model.Layer.Pub) {cell : G.NameG → K} {M : Mats K}
    (hc : ∀ a r c, cell (.cell a r c) = M a r c) :
    ∀ mat < 6, ∀ φ i, cG P cell mat φ i = cellsAt P.y M mat φ i := by
  intro mat hm φ i
  interval_cases mat
  · exact cellAt_eq' hc _ _ _ _ φ i
  · exact cellAt_eq' hc _ _ _ _ φ i
  · exact cellAt_eq' hc _ _ _ _ φ i
  · exact cellAt_eq' hc _ _ _ _ φ i
  · exact cellAt_eq' hc _ _ _ _ φ i
  · exact cellAt_eq' hc _ _ _ _ φ i

omit [Field K] in
/-- An array's matrix is one of the six. -/
theorem mx_lt (X : Inst.Model.FFSeg.Arr) : mxNo X.mx < 6 := by cases X <;> decide

omit [Field K] in
/-- The library's names of cells reach the six matrices alone. -/
theorem cellsOf_congr (D : Dim) {c c' : Cells K}
    (h : ∀ mat < 6, ∀ φ i, c mat φ i = c' mat φ i) : cellsOf D c = cellsOf D c' := by
  funext q
  exact h _ (mx_lt q.X) _ _

end Cells

/-- Every tensor of the layout lies in one of the four families of matrices: from one Bool. -/
theorem hmats_of_all {y : Lay} (h : (y.ten.all fun t => decide (t.mat < 4)) = true) :
    ∀ (n : String) (Tn : Ten), y.T_ n = some Tn → Tn.mat < 4 := by
  intro n Tn hT
  have hm : Tn ∈ y.ten := List.mem_of_find?_eq_some hT
  simpa using List.all_eq_true.mp h Tn hm

section Bridge

variable {h : Shape} {pc : List (List String)} {P : Model.Layer.Pub} {g : ℕ} {rd : Reads}
  {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- The ties at the casts of Mz and Wi, from public lines alone: four layers in a group, f = 2 fe,
TiesG, TiesW, AgreeW. The record Fits is met at the world worldAt. The sizes D, the
parameters Pp and the number lk of column bits are letters here. -/
theorem ties_of_lines {D : Dim} {Pp : Inst.Model.Params} {lk : ℕ} (hDP : D.P = Pp)
    (hlL : D.lL = 2) (hch : 0 < Pp.ch) (hy : layout h pc = .ok P.y) (S : Switches h)
    (hs : scalesHeld h P.sc = .ok ()) (hg : g < P.y.NGr) (hrd : readsOf P.y = .ok rd)
    (hl : layTables mats (tableAsks P.y rd g) 0 = some r) (Zd : Sized h D)
    (hp4 : h.p4 = true) (hev : h.dh % 2 = 0)
    (hmats : ∀ (n : String) (Tn : Ten), P.y.T_ n = some Tn → Tn.mat < 4)
    {s : WsShape} (ZW : SizedW s Pp) (hW : wsLayOf s true lk = .ok P.wsLay)
    (hgL : ∀ l < D.nl, g * P.y.Lam + l < Pp.layers) (Mz : Mats ℤ) (Wi : Mat) :
    P.y.Lam = 4 ∧ D.f = D.fe + D.fe ∧
      TiesG (scl := sclOf h P.sc g 4) P g (cellMW Mz Wi) D (cellsOf D (cG P (cellMW Mz Wi))) ∧
      TiesW P g (cellMW Mz Wi) D (cellsOf D (cG P (cellMW Mz Wi))) (tbG P) (g * P.y.Lam)
        (wOfG P g (cellMW Mz Wi)) ∧
      AgreeW D (fun l => layerR Pp lk (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (g * P.y.Lam + l))
        (wOfG P g (cellMW Mz Wi)) := by
  have A := admitted_of_layout hy S.p3
  have hLam : P.y.Lam = 4 := by
    rw [A.laid.Lam, A.shape, ← Zd.lL, hlL]
    rfl
  letI : Scl := sclOf h P.sc g 4
  have F0 := fits_of_layout (v := envG P g r.1) hy S hs hg hrd hl rfl Zd (cG P (cellMW Mz Wi))
    (fun _ => 0) (fun _ => 0)
  have F : Fits Reading.gl (worldAt (envG P g r.1) (cG P (cellMW Mz Wi)) (fun _ => 0) fun _ => 0)
      (envG P g r.1) D (cG P (cellMW Mz Wi)) (cellsOf D (cG P (cellMW Mz Wi)))
      (fun _ => 0) (fun _ => 0) := by
    have e : (envG P g r.1).y.Lam = 4 := hLam
    rw [e] at F0
    exact F0
  have Ti := ties_of_fits F rfl rfl rfl hmats A.laid.xb
  have S' : Switches P.y.h := by
    rw [A.shape]
    exact S
  have Z' : Sized P.y.h D := by
    rw [A.shape]
    exact Zd
  have hp4' : P.y.h.p4 = true := by
    rw [A.shape]
    exact hp4
  have hev' : P.y.h.dh % 2 = 0 := by
    rw [A.shape]
    exact hev
  obtain ⟨ten, hTo, hmo, hno, -⟩ := ten_of A.laid S' .o (Or.inr ⟨rfl, hp4'⟩)
  have hm4 : ten.mat < 4 := by
    rw [hmo]
    decide
  have Wt := tiesW_of_laid g (cellMW Mz Wi) A.laid S' Z' hp4' (Or.inr ⟨rfl, hp4'⟩) hTo hno hm4 hev'
  have hdh : P.y.h.dh = Pp.ch := by
    rw [← Z'.ch, hDP]
  have hdq : P.y.dq = Pp.nq * Pp.ch := by
    rw [A.laid.dq, ← Z'.nq, ← Z'.ch, hDP]
  have hge : g * P.y.Lam % 2 = 0 := by
    rw [hLam]
    omega
  have Aw := agreeW_layerR (cell := cellMW Mz Wi) (Wc := fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) ZW hW
    (fun _ _ => rfl) hDP g hge hgL S'.p3 hdh hdq hch
  exact ⟨hLam, F.ffe, Ti, Wt, Aw⟩

/-- **The bridge from a lookup's calls to the group's key vectors.** -/
theorem layerKeys_of_calls (hy : layout h pc = .ok P.y) (S : Switches h)
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
    (Mz : Mats ℤ) (Wi : Mat)
    (hIn : ∀ q < 8, Cb.Lkp.InTable (n q) (k q) (G.kvG P g (cellMW Mz Wi) q)
      (fun u => ((tauN P.y.fo q u : ℕ) : Cb.Gl.E))) :
    ∀ c : Fin 8, ∀ X, X < 2 ^ aC Dim.ref c →
      ∃ u ∈ (Cm.Seg.tabOf (lut tbRef c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h P.sc g 4) Dim.ref
            (cellsOf Dim.ref (cellsAt P.y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u := by
  intro c X hX
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
  have key := callKey_of_inTable Ti Wt Aw B hffe hch C HS hcdP hT hc0 hLc hrows (hnn c) hk
    (hIn c.val c.isLt) X hX
  rw [cellsOf_congr Dim.ref (cG_cellsAt P (M := fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
    (fun _ _ _ => rfl)), hLam, Nat.mul_comm g 4] at key
  exact key

end Bridge

#print axioms cG_cellsAt
#print axioms hmats_of_all
#print axioms ties_of_lines
#print axioms layerKeys_of_calls

end OnBytes.Road.Alg
