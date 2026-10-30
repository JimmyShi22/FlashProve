-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PanRdOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck's panels: WHAT THE
PANELS' SIDES READ IS THERE (PanRd, PansWalkA.lean): the entries of the tensors m, a and o at the
lookup's token point, of a, m, lr and xr at the second token point, and the blocks of the residual
stream at the point Y after each write but the last. From the verifier's lines that make the
layout, the reads and the tables' places, by the laws for all arrays at any point
(PointReturn.lean) over the five further families of tables (reach_five). Statements and proofs.
General in the sizes.

  `strmY_of`      the residual stream at the point Y.
  **`panRd_of`**    PanRd v.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. UNDER THE
LIBRARY's ELEVEN SWITCHES ALONE, at profile 4. That the reads' array has a column (hK), and that the
row of the first free entry behind the reads fits 32 bits (hb), are hypotheses on the plan's tree.
THE STREAM AT Y IS SHOWN BELOW THE LAST WRITE ALONE: the stream that goes out need not have a table
at Y. Public data alone: whether a form IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.PansWalkA
import Johnson.Road.K4.C.JoinBOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Reads TableAsk TableAt layTables tableAsks layout readsOf)
open Inst.Model.FFSeg (Arr)

variable {v : Env}

/-- **The table of the residual stream at the point Y after a write but the last is found, and its
blocks are there.** RL: the two long families at Y. -/
theorem strmY_of (B : PlanRd v)
    (RL : ∀ p ∈ [("af" ++ "@" ++ "Y", 0), ("xbI" ++ "@" ++ "Y", 4)], ∃ tb,
      v.tabAt p.1 = some tb ∧
        Reach v tb (partsM v.y p.2 * (colsM v.y p.2 * (rowsM v.y p.2 / 2 ^ v.y.h.la))))
    {sg : ℕ} (h : sg < v.y.NW * v.y.Lam) : StrmP v "Y" sg := by
  obtain ⟨txs, hT, hmat, -⟩ := ten_of B.L B.S .xs (Or.inl rfl)
  have hT' : v.y.T_ "xs" = some txs := hT
  have hmat' : txs.mat = 0 := hmat
  have c1 : (sg == v.y.NW * v.y.Lam) = false := by
    have : sg ≠ v.y.NW * v.y.Lam := Nat.ne_of_lt h
    simpa using this
  by_cases h0 : sg = 0
  · subst h0
    obtain ⟨tb, htb, R⟩ := RL ("xbI" ++ "@" ++ "Y", 4) (by simp)
    exact ⟨tb, txs, htb, hT', fun xh hx => xb_there B (by simp) (cap_stream B.L2) R hx⟩
  · have c0 : (sg == 0) = false := by simpa using h0
    have hi : sg - 1 < 2 * 2 ^ v.y.h.ll - 1 := by
      have e := B.L.NW
      have e' := B.L.Lam
      rw [e, e'] at h
      omega
    obtain ⟨t, tb, ht, H⟩ := long_at B.L B.L2 B.S (sized_dimOf _) B.p4 B.la "Y" .xs (Or.inl rfl)
      (Or.inl rfl) (RL ("af" ++ "@" ++ "Y", 0) (by simp)) (i := sg - 1) hi
    obtain ⟨a1, a2⟩ := tensorAt_inv ht
    have et : t = txs := Option.some.inj (a1.symm.trans hT')
    subst et
    refine ⟨tb, t, ?_, hT', fun xh hx => ?_⟩
    · rw [c0, c1]
      rw [hmat'] at a2
      exact a2
    · rw [c0, c1]
      exact H xh hx

/-- **WHAT THE PANELS' SIDES READ IS THERE.** CONDITIONAL: on the verifier's lines, the switches,
profile 4, hK and hb. -/
theorem panRd_of {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} (hy : layout h pc = .ok v.y)
    (S : Switches h) (h4 : h.p4 = true) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (hK : v.K3 ≠ 0) (hb : r.2.2 / v.K3 < 2 ^ 32) : PanRd v := by
  have B := planRd_of hy S h4 hg hrd hl ht hK hb
  obtain ⟨RL, RS⟩ := reach_five hy S h4 hg hrd hl ht hK hb
  have hLam : ∀ {lam : ℕ}, lam < v.y.Lam → lam < 2 ^ v.y.h.ll := fun {lam} hl => by
    rw [← B.L.Lam]
    exact hl
  have hLamM : ∀ {lm : ℕ}, lm < v.y.LamM → lm < 2 ^ v.y.h.ll / 2 := fun {lm} hl => by
    rw [← B.L.LamM]
    exact hl
  exact {
    m_zt := fun lam hl => rd_ad B .m rfl rfl (hLam hl)
    a_zt := fun lam hl => rd_ad B .a rfl rfl (hLam hl)
    o_zt := fun lam hl => by
      rw [B.L.dq]
      exact short_at B.L B.L2 B.S (sized_dimOf _) B.p4 "zt" .o (Or.inr ⟨rfl, B.p4⟩)
        (RS ("qa" ++ "@" ++ "zt", 3) (by simp)) (hLam hl)
    a_rt := fun lam hl => short_at B.L B.L2 B.S (sized_dimOf _) B.p4 "rt" .a (Or.inl rfl)
      (RS ("ad" ++ "@" ++ "rt", 1) (by simp)) (hLam hl)
    m_rt := fun lam hl => short_at B.L B.L2 B.S (sized_dimOf _) B.p4 "rt" .m (Or.inl rfl)
      (RS ("ad" ++ "@" ++ "rt", 1) (by simp)) (hLam hl)
    lr_rt := fun lm hl => short_at B.L B.L2 B.S (sized_dimOf _) B.p4 "rt" .lr (Or.inl rfl)
      (RS ("ar" ++ "@" ++ "rt", 2) (by simp)) (hLamM hl)
    xr_rt := fun lm hl => short_at B.L B.L2 B.S (sized_dimOf _) B.p4 "rt" .xr (Or.inl rfl)
      (RS ("ad" ++ "@" ++ "rt", 1) (by simp)) (hLamM hl)
    strY := fun sg hs => strmY_of B RL hs
    odd := fun i hi => by
      have h1 := hLamM hi
      rw [B.L.Lam]
      omega }

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.strmY_of
#print axioms OnBytes.Road.K4.C.panRd_of
