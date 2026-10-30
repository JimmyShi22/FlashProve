-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ReadsLawPub.lean: at a public record Pub34 of a layers' sub-proof: where every table
of the reads holds what it says of the matrices M (ReadsTrue), the three tables of the lookup's
planes obey the lookup's own law of the reads (Fo.ReadsLaw,
OnBytes/Tie/Pv/Lookup/Port/FoReads.lean), at the planes' cells that are the entries of the planes'
matrix in M.

OnBytes/Tie/Pv/Lookup/Ends/FoReadsLayer.lean shows this for what `verify-on-bytes`'s
Layer.hearOwn returns. Here the same tools are laid at the record's own lines: layTables has laid
the families (hl, ht), funsOf has made the list of tables (hfun).

Main names:
  `readsAll_of_holds`: Holds at every table of a list (Johnson/Road/FormsKeysMat.lean) gives the law
    of the reads at all tables in the lookup's words (Fo.ReadsAll,
    OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean). A table whose matrix is not in the list of matrices, or
    whose runs have length 0, has no entry, so nothing is asked of it.
  `planeTabs_pub`: the three tables of the planes are among the record's tables, at the first
    entries that its environment finds under their names, with the weights that the lookup's law
    names at the record's two points.
  `readsLaw_pub`: Fo.ReadsLaw at these first entries.
Limits. Premises: ReadsTrue; that the planes' matrix has its rows in one run of 2 ^ lmb (h1) and at
least the planes' columns (h2); that the planes' cells are the matrix's entries (h4). Nothing on
what a prover has committed, on a draw, on soundness or on hiding.


-/
import Johnson.Road.Rows.LayerEnds34
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open Finset OnBytes.Model OnBytes.Model.Layer _root_.Fo Cb.Fo

variable {K : Type} [Field K]

/-- Holds at every table gives the law of the reads at all tables. -/
theorem readsAll_of_holds (ρ : Reading K) {W : World K} {tl : HTailF2} {funs : Array HFun}
    {iU3 K3 : ℕ} {M : Mats K} (hNM : tl.NM = tl.mats.size)
    (H : ∀ Fn ∈ funs, Holds ρ W tl iU3 K3 M Fn) :
    _root_.Fo.ReadsAll ρ tl.mats funs W.entry iU3 K3 M := by
  intro f hf _ col hcol
  have hk : 0 < (tl.mats.getD f.mat {}).k := by
    rcases Nat.eq_zero_or_pos (tl.mats.getD f.mat {}).k with h0 | h0
    · rw [h0, Nat.zero_mul] at hcol
      exact absurd hcol (Nat.not_lt_zero _)
    · exact h0
  have hpos : 0 < (tl.mats.getD f.mat {}).m / f.len := by
    rcases Nat.eq_zero_or_pos ((tl.mats.getD f.mat {}).m / f.len) with h0 | h0
    · rw [h0, Nat.mul_zero] at hcol
      exact absurd hcol (Nat.not_lt_zero _)
    · exact h0
  have hlen : f.len ≠ 0 := by
    intro e
    rw [e, Nat.div_zero] at hpos
    exact absurd hpos (Nat.lt_irrefl _)
  have hmat : f.mat < tl.NM := by
    rw [hNM]
    by_contra hn
    have e : tl.mats.getD f.mat {} = {} := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hn)]
      rfl
    rw [e] at hk
    exact absurd hk (Nat.lt_irrefl _)
  have hc : col / ((tl.mats.getD f.mat {}).m / f.len) < (tl.mats.getD f.mat {}).k :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol)
  have hsg : col % ((tl.mats.getD f.mat {}).m / f.len) < (tl.mats.getD f.mat {}).m / f.len :=
    Nat.mod_lt _ hpos
  have ht : tl.tabAt f (col / ((tl.mats.getD f.mat {}).m / f.len))
      (col % ((tl.mats.getD f.mat {}).m / f.len)) = some (f.start + col) := by
    have hb : (f.len != 0) = true := bne_iff_ne.mpr hlen
    unfold HTailF2.tabAt
    simp only [hmat, hb, hc, hsg, decide_true, Bool.and_self, if_true]
    rw [Nat.add_assoc, Nat.div_add_mod']
  exact H f (Array.mem_toList_iff.mp hf) _ _ _ ht

/-- **The three tables of the planes at a public record.** -/
theorem planeTabs_pub (X : Rows.Pub34 K) (mats : Array TMat) (cellM : ℕ → ℕ → ℕ → K) (ν : Pl → K)
    (h1 : (mats.getD (matIx X.p.v.y).iB {}).m / 2 ^ X.p.v.y.h.lmb = 1)
    (h2 : planeCols X.H.fo.shape X.p.v.y.h.lmb ≤ (mats.getD (matIx X.p.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ X.p.v.y.h.lmb, ∀ c < planeCols X.H.fo.shape X.p.v.y.h.lmb,
      cellM (matIx X.p.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP f0 f1 fP, X.p.v.tabAt "b-bits-0" = some tB0 ∧
      X.p.v.tabAt "b-bits-1" = some tB1 ∧ X.p.v.tabAt "b-pin" = some tP ∧
      PlaneTab X.ρ mats X.funs cellM f0 tB0
        (fun r => (phiBK X.H.fo.shape X.p.v.y.h.lmb (rdL X.ρ X.H.fo.zb0)).getD r 0)
        X.H.fo.shape X.p.v.y.h.lmb ν ∧
      PlaneTab X.ρ mats X.funs cellM f1 tB1
        (fun r => (phiBK X.H.fo.shape X.p.v.y.h.lmb (rdL X.ρ X.H.fo.zb1)).getD r 0)
        X.H.fo.shape X.p.v.y.h.lmb ν ∧
      PlaneTab X.ρ mats X.funs cellM fP tP (fun r => (2 : K) ^ (r % 32)) X.H.fo.shape
        X.p.v.y.h.lmb ν := by
  have hf := X.hfun
  have hl : layTables (matsR X.p.v.y X.p.v.g) (preAsks X.p.v.y X.rd X.p.v.g ++
      [planeAsk X.p.v.y "b-bits-0", planeAsk X.p.v.y "b-bits-1", planeAsk X.p.v.y "b-pin"]) 0 =
      some (X.p.v.tab, X.r.2.1, X.r.2.2) := by
    rw [X.ht, ← tableAsks_eq]
    exact X.hl
  have hl1 : layTables (matsR X.p.v.y X.p.v.g)
      ((preAsks X.p.v.y X.rd X.p.v.g ++ [planeAsk X.p.v.y "b-bits-0"]) ++
        planeAsk X.p.v.y "b-bits-1" :: [planeAsk X.p.v.y "b-pin"]) 0 =
      some (X.p.v.tab, X.r.2.1, X.r.2.2) := by
    rw [List.append_assoc]
    exact hl
  have hl2 : layTables (matsR X.p.v.y X.p.v.g)
      ((preAsks X.p.v.y X.rd X.p.v.g ++
        [planeAsk X.p.v.y "b-bits-0", planeAsk X.p.v.y "b-bits-1"]) ++
        planeAsk X.p.v.y "b-pin" :: []) 0 = some (X.p.v.tab, X.r.2.1, X.r.2.2) := by
    rw [List.append_assoc]
    exact hl
  have n0 : ∀ b ∈ preAsks X.p.v.y X.rd X.p.v.g, b.name ≠ "b-bits-0" :=
    fun b hb => ask_ne hb "b-bits-0" (by decide)
  have n1 : ∀ b ∈ preAsks X.p.v.y X.rd X.p.v.g ++ [planeAsk X.p.v.y "b-bits-0"],
      b.name ≠ "b-bits-1" := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact ask_ne hb "b-bits-1" (by decide)
    · rw [List.mem_singleton.mp hb]
      show "b-bits-0" ≠ "b-bits-1"
      decide
  have n2 : ∀ b ∈ preAsks X.p.v.y X.rd X.p.v.g ++
      [planeAsk X.p.v.y "b-bits-0", planeAsk X.p.v.y "b-bits-1"], b.name ≠ "b-pin" :=
    fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact ask_ne hb "b-pin" (by decide)
    · rcases List.mem_cons.mp hb with rfl | hb
      · show "b-bits-0" ≠ "b-pin"
        decide
      · rw [List.mem_singleton.mp hb]
        show "b-bits-1" ≠ "b-pin"
        decide
  obtain ⟨_, _, q0⟩ := lay_find _ (planeAsk X.p.v.y "b-bits-0") rfl _ _ 0 _ _ _ n0 hl
  obtain ⟨b0, z0, _⟩ := funs_mem _ _ _ _ _ hf _ _ _ q0
  obtain ⟨_, _, q1⟩ := lay_find _ (planeAsk X.p.v.y "b-bits-1") rfl _ _ 0 _ _ _ n1 hl1
  obtain ⟨b1, z1, _⟩ := funs_mem _ _ _ _ _ hf _ _ _ q1
  have y0 : Forest.phiB X.H.fo X.p.v.y.h.lmb 0 = some b0 := z0
  have y1 : Forest.phiB X.H.fo X.p.v.y.h.lmb 1 = some b1 := z1
  obtain ⟨tB0, f0, a0, T0⟩ := layer_planeTab X.ρ "b-bits-0" hl n0 hf b0 z0 mats cellM
    (fun r => (phiBK X.H.fo.shape X.p.v.y.h.lmb (rdL X.ρ X.H.fo.zb0)).getD r 0) X.H.fo.shape ν
    h1 h2 (fun j _ => by
      rw [rdL_getD, phiB_val X.ρ X.H.fo X.p.v.y.h.lmb 0 b0 y0]
      rfl) h4
  obtain ⟨tB1, f1, a1, T1⟩ := layer_planeTab X.ρ "b-bits-1" hl1 n1 hf b1 z1 mats cellM
    (fun r => (phiBK X.H.fo.shape X.p.v.y.h.lmb (rdL X.ρ X.H.fo.zb1)).getD r 0) X.H.fo.shape ν
    h1 h2 (fun j _ => by
      rw [rdL_getD, phiB_val X.ρ X.H.fo X.p.v.y.h.lmb 1 b1 y1]
      rfl) h4
  obtain ⟨tP, fP, a2, TP⟩ := layer_planeTab X.ρ "b-pin" hl2 n2 hf
    (Forest.phiP X.p.v.y.h.lmb) rfl mats cellM _ X.H.fo.shape ν h1 h2
    (fun j hj => phiP_val X.ρ X.p.v.y.h.lmb j hj) h4
  exact ⟨tB0, tB1, tP, f0, f1, fP, a0, a1, a2, T0, T1, TP⟩

/-- **The lookup's law of the reads at the planes' three tables, on true reads.** -/
theorem readsLaw_pub (X : Rows.Pub34 K) (W : World K) (M : Mats K) (hRd : X.ReadsTrue W M)
    (ν : Pl → K)
    (h1 : (X.tl.mats.getD (matIx X.p.v.y).iB {}).m / 2 ^ X.p.v.y.h.lmb = 1)
    (h2 : planeCols X.H.fo.shape X.p.v.y.h.lmb ≤ (X.tl.mats.getD (matIx X.p.v.y).iB {}).k)
    (h4 : ∀ r < 2 ^ X.p.v.y.h.lmb, ∀ c < planeCols X.H.fo.shape X.p.v.y.h.lmb,
      M (matIx X.p.v.y).iB r c = ν (.cell r c))
    {tB0 tB1 tP : ℕ} (t0 : X.p.v.tabAt "b-bits-0" = some tB0)
    (t1 : X.p.v.tabAt "b-bits-1" = some tB1) (t2 : X.p.v.tabAt "b-pin" = some tP) :
    ReadsLaw X.H.fo.shape X.p.v.y.h.lmb (rdL X.ρ X.H.fo.zb0) (rdL X.ρ X.H.fo.zb1) ν W.entry
      X.p.v.iU3 X.p.v.K3 tB0 tB1 tP := by
  obtain ⟨tB0', tB1', tP', f0, f1, fP, a0, a1, a2, T0, T1, TP⟩ :=
    planeTabs_pub X X.tl.mats M ν h1 h2 h4
  obtain rfl : tB0' = tB0 := Option.some.inj (a0.symm.trans t0)
  obtain rfl : tB1' = tB1 := Option.some.inj (a1.symm.trans t1)
  obtain rfl : tP' = tP := Option.some.inj (a2.symm.trans t2)
  exact readsLaw_of_readsAll X.ρ (readsAll_of_holds X.ρ X.hNM hRd) T0 T1 TP

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.readsAll_of_holds
#print axioms OnBytes.Road.K4.planeTabs_pub
#print axioms OnBytes.Road.K4.readsLaw_pub
