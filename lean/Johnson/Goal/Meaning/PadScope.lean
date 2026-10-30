-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PadScope.lean: the field hpad of the record Pub34
(Johnson/Road/Rows/LayerEnds34.lean:182 ff.) at all public files in the goals' scope: for each of
the eight calls of a layer sub-proof's lookup, the verifier's padding key reads as the library's.

The verifier's padding key of a call is row t0 of the call's table (Lay.callRecord,
OnBytes/Model/LayerLayout.lean:572): row 0 of a range table, row 32768 of the tables FC, FL, FS. The
library's is the field pad of its table (lut, Inst/Model/FF/Index.lean:336).

Main theorems.
  takeCalls_kinds, kinds_of_layout: the kinds of a layout's calls are the call lines' second words.
  tables_of_layout: the fields tauFL and tauFS, in the letters of layoutBase.
  siluWord_mid: entry 32768 of the table SILU is 4096, whatever the step and the bound are.
  padB_in_scope: the test padB (Johnson/Road/FormsKeysRef.lean:581) says yes at X.y and the
    library's reference tables. hpad_in_scope: the field, by hpad_of_B.
Asked beside the three facts on the files: Numerals ρ.
-/
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Road.FormsKeysRef
import Johnson.Road.HeadTabs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape layout layoutBase takeCalls takeSegments gateTables siluWord
  fsWord rowFS rowFC clampHalf roundD roundHalfUp)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (tbRef)
open Inst.Model.FFSeg (lut)

/-! ## The kinds of a layout's calls -/

/-- The calls that the lines give have the lines' second words as their kinds. -/
theorem takeCalls_kinds (sd : List (String × String × ℕ × Bool)) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List (String × String × List SegAsk) × List String),
      takeCalls sd lines names seen = .ok r →
      r.1.map (·.2.1) = lines.map (·.getD 1 "")
  | [], _, _, _, h => by
    cases h
    rfl
  | ln :: rest, names, seen, r, h => by
    rcases ln with _ | ⟨name, _ | ⟨kind, _ | ⟨s, more⟩⟩⟩
    · cases h
    · cases h
    · cases h
    · have h : (do
          refuseIf (names.contains name) "policy-call-list"
          refuseIf (["V", "a", "b", "E"].contains name) "policy-call-list"
          let a ← takeSegments sd kind (s :: more) seen
          let r ← takeCalls sd rest (name :: names) a.2
          pure ((name, kind, a.1) :: r.1, r.2)) = .ok r := h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨a', h1, h⟩ := ok_of_bind h
      obtain ⟨r', h2, h⟩ := ok_of_bind h
      cases h
      show kind :: r'.1.map (·.2.1) = kind :: rest.map (·.getD 1 "")
      rw [takeCalls_kinds sd rest (name :: names) a'.2 r' h2]

/-- The kinds of the calls of a layout that the verifier returns on call lines that are there. -/
theorem kinds_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (hpc : pc.isEmpty = false) :
    y.calls.toList.map (·.kind) = pc.map (·.getD 1 "") := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  obtain ⟨taken, ht, hc⟩ := calls_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  show y0.calls.toList.map _ = _
  rw [hpc, if_neg (by decide)] at ht
  rw [hc, ← takeCalls_kinds _ _ _ _ _ ht, List.map_map]
  rfl

/-! ## Two tables -/

/-- The first half of the layout lays tauFL and tauFS so. -/
theorem tables_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) :
    y.tauFL = (Array.range 65536).map (fun t =>
      (t + (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 * 2 ^ 28).toUInt64) ∧
    y.tauFS = if h.p3 then (Array.range 65536).map (fun t =>
      (rowFS h.gcl (gateTables h.eg h.smax h.p3 h.gcl).2 t).toUInt64) else #[] := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy ⊢
  obtain ⟨silu, fs⟩ := gt
  cases hy
  exact ⟨rfl, rfl⟩

/-- The second half keeps them. -/
theorem tables_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) :
    y.tauFL = (Array.range 65536).map (fun t =>
      (t + (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 * 2 ^ 28).toUInt64) ∧
    y.tauFS = if h.p3 then (Array.range 65536).map (fun t =>
      (rowFS h.gcl (gateTables h.eg h.smax h.p3 h.gcl).2 t).toUInt64) else #[] := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have L := tables_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact L

/-- Entry 32768 of the table SILU, the entry of the argument 0, is 4096. -/
theorem siluWord_mid (eg smax : ℕ) (X : Array ℕ) : siluWord eg smax X 32768 = 4096 := by
  simp [siluWord, roundD, roundHalfUp]

/-- Entry 32768 of the first of the gate's two tables. -/
theorem silu_mid (eg smax : ℕ) (p3 gcl : Bool) :
    (gateTables eg smax p3 gcl).1.getD 32768 0 = 4096 := by
  unfold gateTables
  dsimp only
  rw [Hd.getD_rangeMap _ _ _ (by decide), siluWord_mid]

/-- Entry 32768 of the second, with routed experts and the gate's clamp. -/
theorem fs_mid (eg smax : ℕ) : (gateTables eg smax true true).2.getD 32768 0 = 1 := by
  unfold gateTables
  dsimp only
  rw [if_pos rfl, Hd.getD_rangeMap _ _ _ (by decide)]
  rfl

/-- Row 32768 of the table FS, with the gate's clamp. -/
theorem rowFS_mid (fs : Array ℕ) :
    rowFS true fs 32768 = 32768 + fs.getD 32768 0 * 2 ^ 28 + 2 ^ 40 := by
  unfold rowFS
  rw [if_pos (by decide)]

/-! ## The padding key of a call -/

/-- The padding key of a call's record, as a function of the call's kind alone. -/
def padOf (y : Lay) (kind : String) : UInt64 :=
  match y.tauOf kind with
  | none => (if kind == "FC" || kind == "FL" || kind == "FS" then 32768 else 0 : ℕ).toUInt64
  | some a => a.getD (if kind == "FC" || kind == "FL" || kind == "FS" then 32768 else 0) 0

theorem record_pad (y : Lay) (q : ℕ) (cd : CallD) :
    (y.callRecord q cd).tauAt (y.callRecord q cd).t0 = padOf y cd.kind := rfl

theorem pad_R16 (y : Lay) : padOf y "R16" = 0 := by
  simp [padOf, Layer.Lay.tauOf]

theorem pad_R8 (y : Lay) : padOf y "R8" = 0 := by
  simp [padOf, Layer.Lay.tauOf]

theorem pad_FC (y : Lay) : padOf y "FC" = y.tauFC.getD 32768 0 := by
  simp [padOf, Layer.Lay.tauOf]

theorem pad_FL (y : Lay) : padOf y "FL" = y.tauFL.getD 32768 0 := by
  simp [padOf, Layer.Lay.tauOf]

theorem pad_FS (y : Lay) : padOf y "FS" = y.tauFS.getD 32768 0 := by
  simp [padOf, Layer.Lay.tauOf]

/-- The kind of call number k, from the list of the kinds. -/
theorem kind_at {calls : Array CallD} {l : List String} (h : calls.toList.map (·.kind) = l)
    {k : ℕ} (hk : k < l.length) : (calls.getD k default).kind = l.getD k "" := by
  subst h
  have hk' : k < calls.size := by simpa using hk
  simp [Array.getD, hk', List.getD_eq_getElem?_getD]

/-- The stored example's call lines have these kinds. -/
theorem callsRef_kinds : VerifierAndGoals.Lines.callsRef.map (·.getD 1 "") =
    ["R16", "R16", "R16", "R8", "FC", "FS", "FL", "R16"] := by decide

/-! ## Closed numbers -/

theorem num_FC : (rowFC 32768).toUInt64 = fOfNat (Inst.Model.FC.pad).toNat ∧
    0 ≤ Inst.Model.FC.pad := by decide +kernel

theorem num_FL : (32768 + 4096 * 2 ^ 28 : ℕ).toUInt64 = fOfNat ((Inst.Model.FL tbRef).pad).toNat ∧
    0 ≤ (Inst.Model.FL tbRef).pad := by decide +kernel

theorem num_FS : (32768 + 1 * 2 ^ 28 + 2 ^ 40 : ℕ).toUInt64 =
    fOfNat ((Inst.Model.FS tbRef).pad).toNat ∧ 0 ≤ (Inst.Model.FS tbRef).pad := by decide +kernel

theorem num_R : (0 : UInt64) = fOfNat (Inst.Model.R16.pad).toNat ∧ 0 ≤ Inst.Model.R16.pad ∧
    (0 : UInt64) = fOfNat (Inst.Model.R8.pad).toNat ∧ 0 ≤ Inst.Model.R8.pad := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- The test padB on the padding keys says yes, at all public files in the goals' scope. -/
theorem padB_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : padB X.y tbRef = true := by
  have B := Hd.publicH_of_public h
  have hl := B.lay
  have S := Hd.switches_of_core (Hd.core_of_scope hZ hR h)
  have hk := kinds_of_layout hl (by rw [(Hd.calls_of_scope hZ hR h).1]; rfl)
  rw [(Hd.calls_of_scope hZ hR h).1, callsRef_kinds] at hk
  have hsz : X.y.calls.size = 8 := by
    have := congrArg List.length hk
    simpa using this
  obtain ⟨tFL, tFS⟩ := tables_of_layout hl
  have eFC : X.y.tauFC.getD 32768 0 = (rowFC 32768).toUInt64 := by
    rw [Hd.tauFC_of_layout hl]
    exact Hd.getD_rangeMap _ _ _ (by decide)
  have eFL : X.y.tauFL.getD 32768 0 = (32768 + 4096 * 2 ^ 28 : ℕ).toUInt64 := by
    rw [tFL, Hd.getD_rangeMap _ _ _ (by decide), silu_mid]
  have eFS : X.y.tauFS.getD 32768 0 = (32768 + 1 * 2 ^ 28 + 2 ^ 40 : ℕ).toUInt64 := by
    rw [tFS, if_pos S.p3, Hd.getD_rangeMap _ _ _ (by decide), S.gcl, S.p3, rowFS_mid, fs_mid]
  have hrec : ∀ k, k < 8 → (X.y.cl.getD k {}).tauAt (X.y.cl.getD k {}).t0 =
      padOf X.y (["R16", "R16", "R16", "R8", "FC", "FS", "FL", "R16"].getD k "") := by
    intro k hk8
    have e : X.y.cl.getD k {} = X.y.callRecord k (X.y.calls.getD k default) := by
      rw [cl_of_layout hl]
      simp [Array.getD, hsz, hk8]
    rw [e, record_pad, kind_at hk hk8]
  unfold padB
  rw [List.all_eq_true]
  intro k _
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hrec k.val k.isLt]
  obtain ⟨r1, r2, r3, r4⟩ := num_R
  fin_cases k
  · exact ⟨r2, (pad_R16 _).trans r1⟩
  · exact ⟨r2, (pad_R16 _).trans r1⟩
  · exact ⟨r2, (pad_R16 _).trans r1⟩
  · exact ⟨r4, (pad_R8 _).trans r3⟩
  · exact ⟨num_FC.2, (pad_FC _).trans (eFC.trans num_FC.1)⟩
  · exact ⟨num_FS.2, (pad_FS _).trans (eFS.trans num_FS.1)⟩
  · exact ⟨num_FL.2, (pad_FL _).trans (eFL.trans num_FL.1)⟩
  · exact ⟨r2, (pad_R16 _).trans r1⟩

/-- hpad, at all public files in the goals' scope. -/
theorem hpad_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ)
    (k : Fin 8) :
    ρ.val (ofF ((X.y.cl.getD k.val {}).tauAt (X.y.cl.getD k.val {}).t0)) =
      (((lut tbRef k).pad : ℤ) : K) :=
  hpad_of_B hρ (padB_in_scope hZ hR h) k

#print axioms kinds_of_layout
#print axioms tables_of_layout
#print axioms siluWord_mid
#print axioms num_FC
#print axioms num_FL
#print axioms num_FS
#print axioms num_R
#print axioms padB_in_scope
#print axioms hpad_in_scope

end Meaning.P34
