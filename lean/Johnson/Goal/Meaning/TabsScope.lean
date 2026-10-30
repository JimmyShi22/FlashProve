-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/TabsScope.lean: at all public files in the goals' scope, the records of the
eight calls of a layer sub-proof's lookup have the library's reference tables.

  hL_in_scope: the premise hL of layerBridge_of_calls (Johnson/Road/Ends/AlgBridgeL5.lean:59): for
    every call cc: X.y.fo.calls[cc] is there, has the table lut tbRef cc (Hd.IsLut), and has 2^8
    rows at cc = 3 and 2^16 rows otherwise.
The tables R16, R8, FC: isLut_R16, isLut_R8, isLut_FC (Johnson/Road/HeadTabs.lean). FL
and FS: Johnson/Meaning/GateLut.lean. That the lookup's calls are the layout's records:
fo_of_layout (Johnson/Road/FormsKeysShape.lean).
-/
import Johnson.Goal.Meaning.PadScope
import Johnson.Meaning.GateLut
import Johnson.Road.FormsKeysShape

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape layout layoutLook gateTables rowFS)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (tbRef)
open Inst.Model.FFSeg (lut)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- hL: THE EIGHT CALLS' RECORDS HAVE THE LIBRARY's REFERENCE TABLES, at all public files in the
goals' scope. -/
theorem hL_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (cc : Fin 8) :
    ∃ c0 : Call, X.y.fo.calls[cc.val]? = some c0 ∧ Hd.IsLut c0 (lut tbRef cc) ∧
      c0.k = if cc = 3 then 8 else 16 := by
  have B := Hd.publicH_of_public h
  have hl := B.lay
  have S := Hd.switches_of_core (Hd.core_of_scope hZ hR h)
  have hsh := shape_in_scope hZ hR h
  have heg : (layerShape X.P).eg = 8 := by
    rw [hsh]
    rfl
  have hsm : (layerShape X.P).smax = 4095 := by
    rw [hsh]
    rfl
  have hk := kinds_of_layout hl (by rw [(Hd.calls_of_scope hZ hR h).1]; rfl)
  rw [(Hd.calls_of_scope hZ hR h).1, callsRef_kinds] at hk
  have hsz : X.y.calls.size = 8 := by
    have := congrArg List.length hk
    simpa using this
  obtain ⟨tFL, tFS⟩ := tables_of_layout hl
  rw [heg, hsm, S.p3, S.gcl] at tFL
  rw [heg, hsm, S.p3, S.gcl, if_pos rfl] at tFS
  have tFC := Hd.tauFC_of_layout hl
  have hcalls : X.y.fo.calls = X.y.cl := (fo_of_layout hl).1
  have hrec : X.y.cl[cc.val]? = some (X.y.callRecord cc.val (X.y.calls.getD cc.val default)) := by
    rw [cl_of_layout hl]
    simp [Array.getD, hsz, cc.isLt]
  have hkind := kind_at hk (k := cc.val) cc.isLt
  refine ⟨_, by rw [hcalls]; exact hrec, ?_⟩
  generalize X.y.calls.getD cc.val default = cd at hkind ⊢
  have rk : ∀ q, (X.y.callRecord q cd).k = if cd.kind == "R8" then 8 else 16 := fun _ => rfl
  have rt : ∀ q, (X.y.callRecord q cd).tau = X.y.tauOf cd.kind := fun _ => rfl
  have r0 : ∀ q, (X.y.callRecord q cd).t0 =
      if cd.kind == "FC" || cd.kind == "FL" || cd.kind == "FS" then 32768 else 0 := fun _ => rfl
  fin_cases cc
  all_goals
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hkind
  · exact ⟨Hd.isLut_R16 (by rw [rt, hkind]; rfl) (by rw [rk, hkind]; rfl) (by rw [r0, hkind]; rfl),
      by rw [rk, hkind]; rfl⟩
  · exact ⟨Hd.isLut_R16 (by rw [rt, hkind]; rfl) (by rw [rk, hkind]; rfl) (by rw [r0, hkind]; rfl),
      by rw [rk, hkind]; rfl⟩
  · exact ⟨Hd.isLut_R16 (by rw [rt, hkind]; rfl) (by rw [rk, hkind]; rfl) (by rw [r0, hkind]; rfl),
      by rw [rk, hkind]; rfl⟩
  · exact ⟨Hd.isLut_R8 (by rw [rt, hkind]; rfl) (by rw [rk, hkind]; rfl) (by rw [r0, hkind]; rfl),
      by rw [rk, hkind]; rfl⟩
  · exact ⟨Hd.isLut_FC (by rw [rt, hkind, ← tFC]; rfl) (by rw [rk, hkind]; rfl)
      (by rw [r0, hkind]; rfl), by rw [rk, hkind]; rfl⟩
  · exact ⟨Gate.isLut_FS (by rw [rt, hkind]; exact congrArg some tFS) (by rw [rk, hkind]; rfl)
      (by rw [r0, hkind]; rfl), by rw [rk, hkind]; rfl⟩
  · exact ⟨Gate.isLut_FL (by rw [rt, hkind]; exact congrArg some tFL) (by rw [rk, hkind]; rfl)
      (by rw [r0, hkind]; rfl), by rw [rk, hkind]; rfl⟩
  · exact ⟨Hd.isLut_R16 (by rw [rt, hkind]; rfl) (by rw [rk, hkind]; rfl) (by rw [r0, hkind]; rfl),
      by rw [rk, hkind]; rfl⟩

#print axioms hL_in_scope

end Meaning.P34
