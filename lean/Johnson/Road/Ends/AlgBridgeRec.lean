-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgBridgeRec.lean: the bridge of Johnson/Road/Ends/AlgBridge.lean at one record:
the public part X that the verifier's own function publicOf returns on the configuration files.
States: (layerKeys_of_record) if publicOf has returned X, the test recordB X g says true, and hL
holds (for every call the lookup's record has the library's table), then the conclusion of
layerKeys_of_calls holds at X's own letters: the shape layerShape X.P, the layers' public record
X.layers, group g.
recordB X g: the number of column bits of the weights is the library's; readsOf and layTables return
on X's layout (at the group's own list of matrices, matsR); bridgeB
(Johnson/Road/Ends/AlgBridgeTest.lean) says true.
That layout and wsLayOf have returned X's layout and X's layout of the weights is no premise: it is
publicH_of_public (Johnson/Road/HeadMade.lean).
Does not say: that recordB is true at any X (a run of it, in every group:
Johnson/Road/Ends/GuardRec.lean); all that Johnson/Road/Ends/AlgBridge.lean
does not say.
-/
import Johnson.Road.HeadMade
import Johnson.Road.Ends.AlgBridgeTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Model (Call WsShape wsLayOf)
open OnBytes.Model.Verify (Public publicOf layerShape weightShape)
open OnBytes.Model.Layer (Reads TableAsk TableAt readsOf layTables tableAsks)
open Inst.Model (Mat ppref tbRef)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim aC lut keyVec layerR)

/-- **The public premises of the bridge at the record X and group g, as one test.** -/
def recordB (X : Public) (g : ℕ) : Bool :=
  X.P.lkW == kRef &&
    match readsOf X.layers.y with
    | .ok rd =>
      match layTables (matsR X.layers.y g) (tableAsks X.layers.y rd g) 0 with
      | some r => bridgeB (layerShape X.P) X.layers g (weightShape X.P X.y) r.1
      | none => false
    | .error _ => false

/-- What the test holds. -/
theorem recordB_parts {X : Public} {g : ℕ} (t : recordB X g = true) :
    X.P.lkW = kRef ∧ ∃ (rd : Reads) (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ),
      readsOf X.layers.y = .ok rd ∧
      layTables (matsR X.layers.y g) (tableAsks X.layers.y rd g) 0 = some r ∧
      bridgeB (layerShape X.P) X.layers g (weightShape X.P X.y) r.1 = true := by
  unfold recordB at t
  rw [Bool.and_eq_true] at t
  obtain ⟨tk, t⟩ := t
  refine ⟨beq_iff_eq.mp tk, ?_⟩
  cases hrd : readsOf X.layers.y with
  | error e =>
    simp only [hrd] at t
    cases t
  | ok rd =>
    simp only [hrd] at t
    cases hl : layTables (matsR X.layers.y g) (tableAsks X.layers.y rd g) 0 with
    | none =>
      simp only [hl] at t
      cases t
    | some r =>
      simp only [hl] at t
      exact ⟨rd, r, rfl, hl, t⟩

/-- **The bridge at one record and one test.** -/
theorem layerKeys_of_record {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) {g : ℕ} (t : recordB X g = true)
    (hL : ∀ cc : Fin 8, ∃ c0 : Call, X.layers.y.fo.calls[cc.val]? = some c0 ∧
      Hd.IsLut c0 (lut tbRef cc))
    (Mz : Mats ℤ) (Wi : Mat)
    (hIn : ∀ q < 8, Cb.Lkp.InTable (nG q) (kN X.layers.y.fo q)
      (G.kvG X.layers g (cellMW Mz Wi) q)
      (fun u => ((tauN X.layers.y.fo q u : ℕ) : Cb.Gl.E))) :
    ∀ c : Fin 8, ∀ Y, Y < 2 ^ aC Dim.ref c →
      ∃ u ∈ (Cm.Seg.tabOf (lut tbRef c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf (layerShape X.P) X.layers.sc g 4) Dim.ref
            (cellsOf Dim.ref (cellsAt X.layers.y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c Y =
          algebraMap Cb.Gl.F Cb.Gl.E u := by
  obtain ⟨hk, rd, r, hrd, hl, tb⟩ := recordB_parts t
  have B := Hd.publicH_of_public h
  have S := (bridgeB_parts tb).1
  have A := admitted_of_layout B.lay S.p3
  have hW : wsLayOf (weightShape X.P X.y) true kRef = .ok X.layers.wsLay := by
    have e := B.ws
    rw [A.shape, S.p3, hk] at e
    exact e
  exact layerKeys_of_test (P := X.layers) B.lay hrd hl hW tb hL Mz Wi hIn

#print axioms recordB_parts
#print axioms layerKeys_of_record

end OnBytes.Road.Alg
