-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/EmbScope.lean: the public premises of Spec.embWeight
(Johnson/Meaning/EmbWeight.lean) at all public files in the goals' scope, and the law there with no
public premise left.

Spec.embWeight asks: EmbNums of the layer sub-proof's layout; SizedW of the shape of the weights;
that wsLayOf returns the environment's layout at the switch true and at kRef column bits; and it
stands at the library's vocabulary. Here all four are paid from the three facts of
Johnson/Goal/Meaning/ScopeTop.lean: VerifierAndGoals.InScope Z = true, VerifierAndGoals.readFiles Z = .ok pp,
publicOf Z.pol Z.KL lay = .ok X.

Main theorems.
  lPd_of_layout: the layout's lPd is ceilLog2 of the shape's d (a line of layoutBase).
  embNums_of_layout: EmbNums from a return of the layers' layout, the switch p3 and two numbers.
  sizedW_of_core: the nine equations from the 41 numbers (Hd.PublicCore) and the layout's return.
  lkW_of_scope: the parameter file's number of column bits is the library's kRef.
  emb_public_in_scope: the four premises.
  embWeight_in_scope: the law at X's own layouts and vocabulary.
Still asked there: the two lengths of ZE and tkh, and that claimE returns.
Not claimed: that the three facts hold together at any files.
-/
import Johnson.Meaning.EmbWeightProof
import Johnson.Goal.Meaning.ScopeScanTies
import Johnson.Road.HeadMade
import Johnson.Road.FormsKeysLaid
import Johnson.Road.FormsKeysAddr
import Johnson.Road.FormsKeysPos
import Johnson.Thin.Link.PlanV

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Emb

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv Lay Shape layout layoutBase)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (embR)

/-- The first half of the layout lays lPd := ceilLog2 d. -/
theorem lPd_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) : y.lPd = ceilLog2 h.d := by
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
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  rfl

/-- The second half keeps it. -/
theorem lPd_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : y.lPd = ceilLog2 h.d := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have L := lPd_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact L

/-- EmbNums from a return of the layers' layout, for a shape with routed experts, the library's
number of layers and the library's width. -/
theorem embNums_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (hp3 : h.p3 = true) (hL : h.L = ppref.layers)
    (hd : h.d = ppref.d) : EmbNums y := by
  obtain ⟨eh, L⟩ := laid_of_layout hy hp3
  have L2 := laid2_of_layout hy
  have hl := lPd_of_layout hy
  have cap : y.h.d ≤ 2 ^ y.lPd := by
    rw [hl, eh, ceilLog2_eq_clog]
    exact Nat.le_pow_clog (by decide) _
  have hpos : 0 < y.h.d := by
    rw [eh, hd]
    decide
  exact {
    L := by rw [eh]; exact hL
    d := by rw [eh]; exact hd
    S2 := L.S2
    blocks := by rw [← L.S2]; exact Nat.div_mul_cancel L.bd
    T := L2.T
    ls := by
      have h1 : 2 ^ y.ls ≤ y.h.d := by
        rw [← L.S2]
        exact Nat.le_of_dvd hpos L.bd
      exact (Nat.pow_le_pow_iff_right (by decide)).mp (h1.trans cap)
    cap := cap }

/-- The nine equations of SizedW, from the 41 numbers and the layout's return. -/
theorem sizedW_of_core {P : PolScan} {y : Lay} (A : Hd.PublicCore P)
    (hy : layout (layerShape P) P.polCalls = .ok y) : SizedW (weightShape P y) ppref := by
  obtain ⟨eh, L⟩ := laid_of_layout hy (Hd.switches_of_core A).p3
  have eH : P.h.H = 40 := A.num 5
  have eG : P.h.Gk = 8 := A.num 6
  have eD : P.h.dh = 128 := A.num 7
  exact {
    L := A.num 2
    d := A.num 4
    dh := A.num 7
    dq := by
      show y.dq = _
      rw [L.dq, eh]
      show P.h.H * P.h.dh = _
      rw [eH, eD]
      rfl
    dkv := by
      show y.dkv = _
      rw [L.dkv, eh]
      show P.h.Gk * P.h.dh = _
      rw [eG, eD]
      rfl
    f := A.num 8
    fe := A.num 9
    NE := A.num 10
    V := A.num 11 }

/-- The stored example's first 32 lines say 18 column bits. -/
theorem lkW_ref : VerifierAndGoals.Lines.frameRef.blockLog = kRef := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- At all public files in the goals' scope the number of column bits is the library's. -/
theorem lkW_of_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.P.lkW = kRef := by
  rw [Hd.scan_of_scope hZ hR h]
  exact lkW_ref

/-- THE FOUR PUBLIC PREMISES, at all public files in the goals' scope. -/
theorem emb_public_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    EmbNums X.y ∧ SizedW (weightShape X.P X.y) ppref ∧
      wsLayOf (weightShape X.P X.y) true kRef = .ok X.layers.wsLay ∧ X.layers.V = ppref.V := by
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.publicH_of_public h
  have hp3 := (Hd.switches_of_core A).p3
  obtain ⟨eh, -⟩ := laid_of_layout B.lay hp3
  have hws := B.ws
  rw [eh, hp3, lkW_of_scope hZ hR h] at hws
  exact ⟨embNums_of_layout B.lay hp3 (A.num 2) (A.num 4), sizedW_of_core A B.lay, hws,
    (Cb.Thin.Link.publicOf_V h).trans (A.num 11)⟩

/-- THE LAW AT ALL PUBLIC FILES IN THE GOALS' SCOPE, with no public premise left: for every
environment of claims with X's layout of the layer sub-proofs and X's layout of the weights, and
X's own vocabulary. -/
theorem embWeight_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {K : Type} [Field K] (ρ : Reading K) (c : ClaimEnv)
    (hy : c.v.y = X.y) (hw : c.wsLay = X.layers.wsLay) {ZE tkh : Array E} {tokv : Array ℕ}
    {cl : WsClaim} (hZE : ZE.size = c.v.y.ls + c.v.y.h.lt) (hk : tkh.size = c.v.y.lPd - c.v.y.ls)
    (hc : c.claimE ZE tkh X.layers.V tokv = some cl) (M : Wm K) :
    Rows.EmbWeight ρ c.wsLay M cl (fun kh => ρ.val ((eqTab tkh).getD kh zeroE))
      (c.v.y.h.d / c.v.y.S2) c.v.y.ls c.v.y.h.lt (pt ρ ZE) (fun j => pt ρ ZE (c.v.y.ls + j))
      (embR ppref kRef M) (fun p => tokv.getD p 0) := by
  obtain ⟨N, S, W, V⟩ := emb_public_in_scope hZ hR h
  rw [V] at hc
  exact embWeight K ρ c _ S (by rw [hw]; exact W) (by rw [hy]; exact N) ZE tkh tokv cl hZE hk hc M

#print axioms lPd_of_layout
#print axioms embNums_of_layout
#print axioms sizedW_of_core
#print axioms lkW_ref
#print axioms lkW_of_scope
#print axioms emb_public_in_scope
#print axioms embWeight_in_scope

end Meaning.Emb
