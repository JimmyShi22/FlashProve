-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OnOutOfLeft.lean: the kind "lookup" (K3): FROM WHAT A YES OF THE HEARING LEAVES
(K3Left, Johnson/Top/H/K3LeftStatement.lean; PadExact, Johnson/Top/H/Keep/PadExact.lean) TO THE
PROMISE BEHIND THE LOOKUP's PLACE AS THE TABLE OF JOINTS WRITES IT (k3OnOut,
Johnson/Desc/First/Look/K3Borders.lean: a Bool on the carried record). One end theorem, general in
the seat. A tie: no error term.

OBJECT: no text that runs: Desc.K3.k3OnOut, the table of joints' Bool on the carried record.
USER: k3_calls_lookOut (Johnson/Desc/First/Look/K3CallsLookOut.lean).
LETTERS: p, s', h, lm, F, F', g, rs free: general in the seat.
BUILT ON Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean.

Why. k3OnOut is a conjunction of thirteen tests on the heard record and the ledger. Each is a field
of K3Left, of the library's PadLeft inside it, or of PadExact, or follows from one; that the leaves'
stretch is free behind wants that the lookup's slots were free in front, which is the promise in
front's own test.

Main names:
  `sameShapeAll_refl`: the table's test "the same shape" says yes of a shape and itself.
  `sizedB_of`: the library's Sized gives the table's test on the three arrays' sizes.
  `freeB_leaves`: the leaves' stretch is free behind, where the lookup's slots were free in front.
  `k3OnOut_of_left`: THE END.

ITS PREMISES. hs: the place has the shape h. hh, hf: what the record behind holds at the seat and as
its ledger. L, E: what the hearing leaves. hn: the ledger in front stood at the place's first slot.
hfree: the lookup's slots were free in front (k3OnIn's last test). hok: the library's bounds on the
shape.

Limits. It says nothing on who gives L and E at a seat (at the calls: k3LeavesAtCalls,
Johnson/Top/H/K3CEnd.lean; decide_exact), nor on the rest of the table's promise.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Borders
import Johnson.Top.H.K3LeftPoint
import Johnson.Top.H.Keep.PadExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open OnBytes.PscRun
open VerifiableInference.Desc.K3 (sameCall sameShapeAll sizedB freeB heardAt k3OnOut)

/-! ## The table's small tests -/

theorem sameCall_refl (c : Call) : sameCall c c = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := c
  simp [sameCall]

theorem zipAll_refl : ∀ l : List Call, (l.zip l).all (fun x => sameCall x.1 x.2) = true
  | [] => rfl
  | a :: l => by
    rw [List.zip_cons_cons, List.all_cons, sameCall_refl, zipAll_refl l]
    rfl

theorem sameShapeAll_refl (h : Forest.Shape) : sameShapeAll h h = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  simp [sameShapeAll, zipAll_refl]

theorem sizedB_of {G : Fork} (h : Sized G) : sizedB G = true := by
  unfold sizedB
  rw [h.1, h.2.1, h.2.2]
  simp

/-- A mark that reads "free" with the default "filled" lies inside the array. -/
theorem getD_in (a : Array Bool) (i : ℕ) (h : a.getD i true = false) : a.getD i false = false := by
  by_cases hi : i < a.size
  · simp only [Array.getD, dif_pos hi] at h ⊢
    exact h
  · simp only [Array.getD, dif_neg hi] at h
    cases h

theorem getD_out (a : Array Bool) (i : ℕ) (hi : i < a.size) (h : a.getD i false = false) :
    a.getD i true = false := by
  simp only [Array.getD, dif_pos hi] at h ⊢
  exact h

/-- What the test freeB says. -/
theorem freeB_iff (G : Fork) (first n : ℕ) :
    freeB G first n = true ↔
      first + n ≤ G.ns ∧ ∀ j, j < n → G.gotF.getD (first + j) true = false := by
  unfold freeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true']

/-! ## The leaves' stretch -/

theorem freeB_leaves {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard}
    (P : PadLeft h F F' g) (E : Fo.Tp.PadExact h F F' g)
    (hfree : freeB F F.next (Forest.elems h) = true) :
    freeB F' g.leaves.first (1 + 2 * h.d + 5) = true := by
  obtain ⟨f1, f2⟩ := (freeB_iff F F.next (Forest.elems h)).1 hfree
  refine (freeB_iff F' _ _).2 ⟨?_, fun j hj => ?_⟩
  · rw [P.rest.2.1]
    exact Nat.le_trans E.within f1
  · have hin : g.leaves.first + j < F'.gotF.size := by
      rw [P.fit.2.2, P.rest.2.1]
      have := E.within
      omega
    refine getD_out _ _ hin ?_
    have hF : ¬ Filled F (g.leaves.first + j) := by
      intro hc
      have e : F.next + (g.leaves.first + j - F.next) = g.leaves.first + j := by
        have := E.first
        omega
      have q := f2 (g.leaves.first + j - F.next) (by
        have := E.first
        have := E.within
        omega)
      rw [e] at q
      have q' := getD_in _ _ q
      unfold Filled at hc
      rw [q'] at hc
      cases hc
    have hF' : ¬ Filled F' (g.leaves.first + j) := by
      intro hc
      rcases (E.marks _).1 hc with h1 | ⟨-, -, h3⟩
      · exact hF h1
      · exact h3 ⟨Nat.le_add_right _ _, by omega⟩
    unfold Filled at hF'
    cases hv : F'.gotF.getD (g.leaves.first + j) false with
    | false => rfl
    | true => exact absurd hv hF'

/-! ## The end -/

theorem k3OnOut_of_left {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K}
    (p : Desc.First.Look.P) (s' : Desc.First.S) {h : Forest.Shape} {lm : ℕ} {F F' : Fork}
    {g : Forest.Heard} {rs : Rounds K} (hs : p.shape = some h)
    (hh : heardAt p.digits s' = some g) (hf : s'.fork? = some F')
    (L : K3Left ρ h lm F F' g rs) (E : Fo.Tp.PadExact h F F' g) (hn : F.next = p.first)
    (hfree : freeB F p.first (Forest.elems h) = true) (hok : FoNums.ok h = true) :
    k3OnOut p s' = true := by
  have hNC : h.calls.size = h.NC := (Cb.Fo.ok_parts hok).1.2.2.2.2.2.2
  have c1 : sameShapeAll g.shape h = true := by
    rw [L.shape]
    exact sameShapeAll_refl h
  have c2 : (h.calls.size == h.NC) = true := by
    rw [hNC]
    exact beq_self_eq_true _
  have c3 : (g.zx.size == h.dT) = true := by
    rw [L.zx]
    exact beq_self_eq_true _
  have c4 : (g.zy.size == h.rK) = true := by
    rw [L.zy]
    exact beq_self_eq_true _
  have c5 : (g.zk.size == h.NC) = true := by
    rw [L.zkSize]
    exact beq_self_eq_true _
  have c6 : ((List.range h.calls.size).all fun c =>
      (g.zk.getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0) = true := by
    rw [List.all_eq_true]
    intro c hc
    rw [L.zkLen c (by rw [← hNC]; exact List.mem_range.1 hc)]
    exact beq_self_eq_true _
  have c7 : decide (p.first + Forest.elems h ≤ F'.next) = true := by
    rw [E.next, hn]
    exact decide_eq_true (Nat.le_refl _)
  have c8 : sizedB F' = true := sizedB_of L.padLeft.fit
  have c9 : freeB F' g.leaves.first (1 + 2 * h.d + 5) = true :=
    freeB_leaves L.padLeft E (by rw [hn]; exact hfree)
  have c10 : decide (p.first ≤ g.leaves.first) = true := by
    rw [← hn]
    exact decide_eq_true E.first
  have c11 : decide (g.leaves.first + (1 + 2 * h.d + 5) ≤ p.first + Forest.elems h) = true := by
    rw [← hn]
    exact decide_eq_true E.within
  have c12 : ((g.zb 0).size == h.kT + h.cK + 5) = true := by
    have e : g.zb 0 = g.zb0 := rfl
    rw [e, L.zb_size.1]
    exact beq_self_eq_true _
  have c13 : ((g.zb 1).size == h.kT + h.cK + 5) = true := by
    have e : g.zb 1 = g.zb1 := rfl
    rw [e, L.zb_size.2]
    exact beq_self_eq_true _
  unfold k3OnOut
  rw [hs, hh, hf]
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, Bool.and_self]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.sameShapeAll_refl
#print axioms VerifiableInference.OnPublicFiles.freeB_leaves
#print axioms VerifiableInference.OnPublicFiles.k3OnOut_of_left
