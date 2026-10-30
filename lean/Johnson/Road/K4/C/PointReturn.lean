-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PointReturn.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck's panels: the laws of
TensorsThere.lean, StreamReturn.lean and ReachPlan.lean at ANY point's name, and the five families
of tables that the panels' sides read beside the six of the lookup's point: af and the stream that
comes in at the point Y, ad and ar at the point rt, and the short tables of qa at the token point.
Two definitions of hypotheses; statements and proofs.

  `LongP v X Z i n`  tensor X is found with its long tables at the point Z, and blocks 0 to n - 1
                      of layer i are there. `StrmP v Z sg`: the like for the residual stream.
  `short_at`, `long_at`   an array's tensor at a point, from the family's entries.
  `SxsA_at`           the stream's sum returns.
  **`reach_five`**      the five families are found, and all their entries are there.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. UNDER THE
LIBRARY's ELEVEN SWITCHES ALONE, at profile 4. That the reads' array has a column (hK) and that the
row of the first free entry behind the reads fits 32 bits (hb) are hypotheses on the plan's tree.
Public data alone: whether a form IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.TensorsThere
import Johnson.Road.K4.C.StreamReturn
import Johnson.Road.FormsKeysTrue2
import Johnson.Road.FormsKeysCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Reads TableAsk TableAt layTables tableAsks layout readsOf sumForms)
open OnBytes.Desc.First.K4.Total (sumForms_all)
open Inst.Model.FFSeg (Dim Arr Cell)

variable {v : Env} {D : Dim}

/-- **Tensor X is found with its long tables at the point Z, and blocks 0 to n - 1 of layer i are
there.** This defines a hypothesis; the definition claims nothing. -/
def LongP (v : Env) (X Z : String) (i n : ℕ) : Prop :=
  ∃ t tb, v.tensorAt X Z = some (t, tb) ∧ ∀ jh, jh < n → (v.longA tb t i jh).isSome = true

/-- **The table of the residual stream after write number sg, at the point Z, is found, and its
blocks are there.** This defines a hypothesis; the definition claims nothing. -/
def StrmP (v : Env) (Z : String) (sg : ℕ) : Prop :=
  ∃ tb txs,
    v.tabAt ((if sg == 0 then "xbI" else if sg == v.y.NW * v.y.Lam then "xbO" else "af") ++ "@" ++
      Z) = some tb ∧ v.y.T_ "xs" = some txs ∧
    ∀ xh, xh < v.y.h.d / v.y.S2 →
      (if (sg == 0 || sg == v.y.NW * v.y.Lam) = true then v.xbA tb xh
        else v.longA tb txs (sg - 1) xh).isSome = true

/-- The stream's sum returns. -/
theorem SxsA_at {Z : String} {sg : ℕ} (S : StrmP v Z sg) (wh : Array E) :
    (v.SxsA wh Z sg).isSome = true := by
  obtain ⟨tb, txs, e1, e2, H⟩ := S
  unfold Env.SxsA
  dsimp only
  rw [e1, e2]
  show (sumForms (v.y.h.d / v.y.S2) fun xh =>
    (if (sg == 0 || sg == v.y.NW * v.y.Lam) = true then v.xbA tb xh
      else v.longA tb txs (sg - 1) xh).map fun a => (a, wh.getD xh zeroE)).isSome = true
  rw [sumForms_all, List.all_eq_true]
  intro xh hx
  rw [Option.isSome_map]
  exact H xh (List.mem_range.mp hx)

/-- **An array's tensor is found with its matrix's short tables at the point Pn, and all entries of
each of its layers are there.** -/
theorem short_at (L : Laid v.y) (L2 : Laid2 v.y) (S : Switches v.y.h) (Z : Sized v.y.h D)
    (hp4 : v.y.h.p4 = true) (Pn : String) (X : Arr) (hX : inList v.y.h X)
    (R : ∃ tb, v.tabAt (Env.mname (matNo X) ++ "@" ++ Pn) = some tb ∧
      Reach v tb (partsM v.y (matNo X) * (colsM v.y (matNo X) * (rowsM v.y (matNo X) / v.y.T))))
    {i : ℕ} (hi : i < X.cnt D) : Short v (arrName X) Pn i (X.width D) := by
  obtain ⟨ten, hT, hm, hnl, -, -, -⟩ := ten_of L S X hX
  obtain ⟨tb, htb, R⟩ := R
  refine ⟨ten, tb, ?_, fun j hj => shortA_some R fun l hl => ?_⟩
  · unfold Env.tensorAt
    rw [hT]
    show (v.tabAt (Env.mname ten.mat ++ "@" ++ Pn) >>= fun tb => pure (ten, tb)) = _
    rw [hm, htb]
    rfl
  · rw [(place_eq_feat L S Z X hX hT l i j).1]
    have hv : (⟨X, l, i, j, 0⟩ : Cell).Valid D :=
      ⟨hnl ▸ hl, hi, hj, Inst.Model.FFSeg.IndexFacts.T_pos D⟩
    obtain ⟨-, hlt⟩ := valid_inMat L2 S Z hp4 hv
    rw [← matNo_eq, Nat.mul_assoc] at hlt
    exact hlt

/-- **An array of the matrices af, qa: its tensor is found with its long tables at the point Pn,
and all blocks of each of its layers are there.** -/
theorem long_at (L : Laid v.y) (L2 : Laid2 v.y) (S : Switches v.y.h) (Z : Sized v.y.h D)
    (hp4 : v.y.h.p4 = true) (hla : v.y.h.la = v.y.ls + v.y.h.lt) (Pn : String) (X : Arr)
    (hX : inList v.y.h X) (hm03 : matNo X = 0 ∨ matNo X = 3)
    (R : ∃ tb, v.tabAt (Env.mname (matNo X) ++ "@" ++ Pn) = some tb ∧
      Reach v tb
        (partsM v.y (matNo X) * (colsM v.y (matNo X) * (rowsM v.y (matNo X) / 2 ^ v.y.h.la))))
    {i : ℕ} (hi : i < X.cnt D) : LongP v (arrName X) Pn i (X.width D / v.y.S2) := by
  obtain ⟨ten, hT, hm, hnl, -, -, -⟩ := ten_of L S X hX
  obtain ⟨tb, htb, R⟩ := R
  have hS2 : 0 < v.y.S2 := by
    rw [L.S2]
    exact Nat.two_pow_pos _
  have hfc : fcM v.y (matNo X) = rowsM v.y (matNo X) / 2 ^ v.y.h.la * v.y.S2 :=
    fc_blocks L L2 hla (by rcases hm03 with e | e <;> rw [e] <;> simp)
  refine ⟨ten, tb, ?_, fun jh hj => longA_some R fun l hl => ?_⟩
  · unfold Env.tensorAt
    rw [hT]
    show (v.tabAt (Env.mname ten.mat ++ "@" ++ Pn) >>= fun tb => pure (ten, tb)) = _
    rw [hm, htb]
    rfl
  · have hjw : jh * v.y.S2 < X.width D := by
      have h1 := (Nat.le_div_iff_mul_le hS2).mp (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at h1
      omega
    have hv : (⟨X, l, i, jh * v.y.S2, 0⟩ : Cell).Valid D :=
      ⟨hnl ▸ hl, hi, hjw, Inst.Model.FFSeg.IndexFacts.T_pos D⟩
    obtain ⟨-, hlt⟩ := valid_inMat L2 S Z hp4 hv
    rw [← (place_eq_feat L S Z X hX hT l i (jh * v.y.S2)).1, ← matNo_eq, hfc] at hlt
    have e0 : tenCell ten.place l i (jh * v.y.S2) = tenCell ten.place l i 0 + jh * v.y.S2 := rfl
    rw [e0] at hlt
    have e1 : (tenCell ten.place l i 0 + jh * v.y.S2) / v.y.S2 =
        tenCell ten.place l i 0 / v.y.S2 + jh := Nat.add_mul_div_right _ _ hS2
    rw [← e1]
    apply Nat.div_lt_of_lt_mul
    calc tenCell ten.place l i 0 + jh * v.y.S2
        < partsM v.y (matNo X) * colsM v.y (matNo X) *
            (rowsM v.y (matNo X) / 2 ^ v.y.h.la * v.y.S2) := hlt
      _ = v.y.S2 * (partsM v.y (matNo X) *
            (colsM v.y (matNo X) * (rowsM v.y (matNo X) / 2 ^ v.y.h.la))) := by ring

/-- **THE FIVE FURTHER FAMILIES ARE FOUND, AND ALL THEIR ENTRIES ARE THERE.** CONDITIONAL: on the
verifier's lines, the switches, profile 4, hK and hb. The pairs: a family's name and its matrix's
number; long tables first. -/
theorem reach_five {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} (hy : layout h pc = .ok v.y)
    (S : Switches h) (h4 : h.p4 = true) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (hK : v.K3 ≠ 0) (hb : r.2.2 / v.K3 < 2 ^ 32) :
    (∀ p ∈ [("af" ++ "@" ++ "Y", 0), ("xbI" ++ "@" ++ "Y", 4)], ∃ tb, v.tabAt p.1 = some tb ∧
      Reach v tb (partsM v.y p.2 * (colsM v.y p.2 * (rowsM v.y p.2 / 2 ^ v.y.h.la)))) ∧
    (∀ p ∈ [("ad" ++ "@" ++ "rt", 1), ("ar" ++ "@" ++ "rt", 2), ("qa" ++ "@" ++ "zt", 3)],
      ∃ tb, v.tabAt p.1 = some tb ∧
        Reach v tb (partsM v.y p.2 * (colsM v.y p.2 * (rowsM v.y p.2 / v.y.T)))) := by
  obtain ⟨p1, p2, p3, p4⟩ := points2_of_layout hy S hrd
  obtain ⟨⟨a0, m0, b0, c0, d0, e0, -⟩, ⟨a4, m4, b4, c4, d4, e4, -⟩, ⟨a1, m1, b1, c1, d1, e1, -⟩,
    ⟨a2, m2, b2, c2, d2, e2, -⟩⟩ := four_numbers v.y rd v.g p1 p2 p3 p4
  have es := (admitted_of_layout hy S.p3).shape
  subst es
  have s3 : HasSeg v.y "O" := hasSeg_of_layout hy S .O
  have hQS : "zt" ∈ rd.rdQS :=
    readsOf_short_qa hrd (anyZ_of_seg s3 (by rw [h4]; simp [Model.Layer.readsZ]))
  obtain ⟨a3, m3, b3, c3, d3, e3, -⟩ := qaShort_numbers v.y rd v.g h4 hQS
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact reach_family hg hrd hl ht hK hb _ 0 _ (by omega) ⟨a0, m0, b0, c0, d0, e0⟩
    · exact reach_family hg hrd hl ht hK hb _ 4 _ (by omega) ⟨a4, m4, b4, c4, d4, e4⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact reach_family hg hrd hl ht hK hb _ 1 _ (by omega) ⟨a1, m1, b1, c1, d1, e1⟩
    · exact reach_family hg hrd hl ht hK hb _ 2 _ (by omega) ⟨a2, m2, b2, c2, d2, e2⟩
    · exact reach_family hg hrd hl ht hK hb _ 3 _ (by omega) ⟨a3, m3, b3, c3, d3, e3⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.SxsA_at
#print axioms OnBytes.Road.K4.C.short_at
#print axioms OnBytes.Road.K4.C.long_at
#print axioms OnBytes.Road.K4.C.reach_five
