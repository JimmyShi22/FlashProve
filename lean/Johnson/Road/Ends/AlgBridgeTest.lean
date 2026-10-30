-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgBridgeTest.lean: the public premises of layerKeys_of_calls
(Johnson/Road/Ends/AlgBridge.lean) that a program can decide, as one test, with its theorem.
States: (layerKeys_of_test) if four functions of the verifier have returned (layout, readsOf,
layTables, wsLayOf), the test bridgeB says true, and hL holds in its shortest form (for every call
the lookup's record fo.calls[cc] has the library's table: Hd.IsLut), then the conclusion of
layerKeys_of_calls holds, at the letters nG (the library's a_c) and kN (the records' own k). That k
is the record's, 8 at call 3 and 16 elsewhere, is concluded from Hd.IsLut (rows_ref).
(hL_of_cl) hL follows from Hd.IsLut of the layout's records y.cl.getD cc {}.
Johnson/Road/Ends/AlgTabs.lean draws hL from one test.
bridgeB gathers: the eleven switches; scalesHeld returns; the group's number; the nine numbers of
Sized and the nine of SizedW; profile 4; an even width of a head; every tensor in one of the four
families of matrices; as many tokens; the group's layers below the model's; ropeOK; eight calls;
their eight lines; the floor hfl; weighedOf returns for every call.
Does not say: that bridgeB is true anywhere (a run of recordB, which holds bridgeB:
Johnson/Road/Ends/GuardRec.lean); all that Johnson/Road/Ends/AlgBridge.lean
does not say.
-/
import Johnson.Road.FormsKeysShape
import Johnson.Road.Ends.AlgBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Model (Seg CallD Call WsShape wsLayOf)
open OnBytes.Model.Layer (Env Lay Shape Scales Reads TableAsk TableAt Ten layout scalesHeld readsOf
  layTables tableAsks)
open Inst.Model (Scl Tables Mat ppref tbRef)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Fam fams used aC lut keyVec layerR)

/-- The eleven switches, as a test. -/
def switchesB (h : Shape) : Bool :=
  h.p3 && h.gcl && h.rcl && h.xl == 5 && h.hq == 2 && h.hv == 1 && h.ho == 1 && h.hgD == 1 &&
    h.huD == 1 && h.hdD == 1 && h.hr == 1

/-- If the test says true, the switches are set. -/
theorem switches_of_B {h : Shape} (t : switchesB h = true) : Switches h := by
  simp only [switchesB, Bool.and_eq_true, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩ := t
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩

/-- The nine numbers in which sizes agree with a shape, as a test. -/
def sizedB (h : Shape) (D : Dim) : Bool :=
  D.P.d == h.d && D.P.f == h.f && D.P.fe == h.fe && D.P.nexp == h.NE && D.P.nq == h.H &&
    D.P.nkv == h.Gk && D.P.ch == h.dh && D.lT == h.lt && D.lL == h.ll

/-- If the test says true, the sizes agree with the shape. -/
theorem sized_of_B {h : Shape} {D : Dim} (t : sizedB h D = true) : Sized h D := by
  simp only [sizedB, Bool.and_eq_true, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := t
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

/-- The nine numbers in which a shape of the weights agrees with the library's parameters. -/
def sizedWB (s : WsShape) (Pp : Inst.Model.Params) : Bool :=
  s.L == Pp.layers && s.d == Pp.d && s.dh == Pp.ch && s.dq == Pp.nq * Pp.ch &&
    s.dkv == Pp.nkv * Pp.ch && s.f == Pp.f && s.fe == Pp.fe && s.NE == Pp.nexp && s.V == Pp.V

/-- If the test says true, they agree. -/
theorem sizedW_of_B {s : WsShape} {Pp : Inst.Model.Params} (t : sizedWB s Pp = true) :
    SizedW s Pp := by
  simp only [sizedWB, Bool.and_eq_true, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := t
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

/-- The eight lines of calls name the library's families, in order: as a test. -/
def linesB (y : Lay) : Bool :=
  (List.finRange 8).all fun cc =>
    match y.calls[cc.val]? with
    | some cd => cd.segs.map (·.name) == (fams cc).map segName
    | none => true

/-- If the test says true, they do. -/
theorem lines_of_B {y : Lay} (t : linesB y = true) (cc : Fin 8) (cd : CallD)
    (hc : y.calls[cc.val]? = some cd) : cd.segs.map (·.name) = (fams cc).map segName := by
  have h1 := List.all_eq_true.mp t cc (List.mem_finRange cc)
  rw [hc] at h1
  simpa using h1

/-- **The public premises that a program can decide, as one test.** tab: the places of the tables,
as layTables has returned them. -/
def bridgeB (h : Shape) (P : Model.Layer.Pub) (g : ℕ) (s : WsShape) (tab : List TableAt) : Bool :=
  switchesB h && (scalesHeld h P.sc).isOk && decide (g < P.y.NGr) && sizedB h Dim.ref && h.p4 &&
    h.dh % 2 == 0 && (P.y.ten.all fun t => decide (t.mat < 4)) && P.y.T == Dim.ref.T &&
    sizedWB s ppref &&
    ((List.range Dim.ref.nl).all fun l => decide (g * P.y.Lam + l < ppref.layers)) &&
    ropeOK P Dim.ref tbRef (g * P.y.Lam) && P.y.calls.size == 8 && linesB P.y &&
    ((List.finRange 8).all fun cc =>
      decide (h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used Dim.ref cc))) &&
    (P.y.calls.toList.all fun cd => ((envG P g tab).weighedOf cd).isSome)

/-- The library's logarithm of the number of keys of call q; 0 from 8 on. -/
def nG (q : ℕ) : ℕ := if hq : q < 8 then aC Dim.ref ⟨q, hq⟩ else 0

/-- The library's reference tables have 2^8 rows in call 3 and 2^16 in the seven others. -/
theorem rows_ref (cc : Fin 8) : (lut tbRef cc).rows = 2 ^ (if cc = 3 then 8 else 16) := by
  fin_cases cc <;> rfl

/-- Five of the parts of the test: the switches; the sizes; eight calls; their eight lines; the
floor. -/
theorem bridgeB_parts {h : Shape} {P : Model.Layer.Pub} {g : ℕ} {s : WsShape} {tab : List TableAt}
    (t : bridgeB h P g s tab = true) :
    Switches h ∧ Sized h Dim.ref ∧ P.y.calls.size = 8 ∧
      (∀ (cc : Fin 8) (cd : CallD),
        P.y.calls[cc.val]? = some cd → cd.segs.map (·.name) = (fams cc).map segName) ∧
      ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used Dim.ref cc) := by
  unfold bridgeB at t
  simp only [Bool.and_eq_true] at t
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, -⟩, -⟩, b4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, b12⟩, b13⟩, b14⟩, -⟩ := t
  exact ⟨switches_of_B b1, sized_of_B b4, by simpa using b12, lines_of_B b13, fun cc => by
    simpa using List.all_eq_true.mp b14 cc (List.mem_finRange cc)⟩

/-- **hL from the layout's own records**: the lookup's records of the calls are the layout's
(fo_of_layout), so if each of the layout's eight records has the library's table, hL holds. -/
theorem hL_of_cl {h : Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
    (h8 : y.calls.size = 8)
    (hC : ∀ cc : Fin 8, Hd.IsLut (y.cl.getD cc.val {}) (lut tbRef cc)) :
    ∀ cc : Fin 8, ∃ c0 : Call, y.fo.calls[cc.val]? = some c0 ∧ Hd.IsLut c0 (lut tbRef cc) := by
  intro cc
  obtain ⟨e1, -, e3⟩ := fo_of_layout hy
  have hlt : cc.val < y.cl.size := by
    rw [e3, h8]
    exact cc.isLt
  refine ⟨y.cl.getD cc.val {}, ?_, hC cc⟩
  rw [e1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  rfl

section Test

variable {h : Shape} {pc : List (List String)} {P : Model.Layer.Pub} {g : ℕ} {rd : Reads}
  {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **The bridge, from four returns, one test and hL.** -/
theorem layerKeys_of_test (hy : layout h pc = .ok P.y) (hrd : readsOf P.y = .ok rd)
    (hl : layTables mats (tableAsks P.y rd g) 0 = some r) {s : WsShape}
    (hW : wsLayOf s true kRef = .ok P.wsLay) (t : bridgeB h P g s r.1 = true)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc))
    (Mz : Mats ℤ) (Wi : Mat)
    (hIn : ∀ q < 8, Cb.Lkp.InTable (nG q) (kN P.y.fo q) (G.kvG P g (cellMW Mz Wi) q)
      (fun u => ((tauN P.y.fo q u : ℕ) : Cb.Gl.E))) :
    ∀ c : Fin 8, ∀ X, X < 2 ^ aC Dim.ref c →
      ∃ u ∈ (Cm.Seg.tabOf (lut tbRef c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h P.sc g 4) Dim.ref
            (cellsOf Dim.ref (cellsAt P.y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u := by
  unfold bridgeB at t
  simp only [Bool.and_eq_true] at t
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, b12⟩, b13⟩, b14⟩,
    b15⟩ := t
  have hs : scalesHeld h P.sc = .ok () := by
    cases e : scalesHeld h P.sc with
    | ok u => rfl
    | error m =>
      rw [e] at b2
      cases b2
  have hgL : ∀ l < Dim.ref.nl, g * P.y.Lam + l < ppref.layers := fun l hl' => by
    simpa using List.all_eq_true.mp b10 l (List.mem_range.mpr hl')
  have hfl : ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used Dim.ref cc) := fun cc => by
    simpa using List.all_eq_true.mp b14 cc (List.mem_finRange cc)
  have hw : ∀ cd ∈ P.y.calls, ∃ wg, (envG P g r.1).weighedOf cd = some wg := fun cd hcd =>
    Option.isSome_iff_exists.mp (List.all_eq_true.mp b15 cd (Array.mem_toList_iff.mpr hcd))
  have hnn : ∀ cc : Fin 8, nG cc.val = aC Dim.ref cc := fun cc => by
    unfold nG
    rw [dif_pos cc.isLt]
  have hL' : ∀ cc : Fin 8, ∃ c0 : Call, P.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc) ∧ kN P.y.fo cc.val = c0.k ∧
      c0.k = if cc = 3 then 8 else 16 := fun cc => by
    obtain ⟨c0, e0, L0⟩ := hL cc
    refine ⟨c0, e0, L0, ?_, ?_⟩
    · unfold kN
      rw [e0]
      rfl
    · exact Nat.pow_right_injective (le_refl 2) (L0.rows.trans (rows_ref cc))
  exact layerKeys_of_calls hy (switches_of_B b1) hs (by simpa using b3) hrd hl (sized_of_B b4) b5
    (by simpa using b6) (hmats_of_all b7) (by simpa using b8) (sizedW_of_B b9) hW hgL b11
    (by simpa using b12) (lines_of_B b13) hfl hw nG (kN P.y.fo) hnn hL' Mz Wi hIn

end Test

#print axioms bridgeB_parts
#print axioms hL_of_cl
#print axioms layerKeys_of_test

end OnBytes.Road.Alg
