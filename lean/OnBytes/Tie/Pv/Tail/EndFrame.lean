-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndFrame.lean: that a table's vector is another array than those of the digits,
of the planes, of the symbols and of the lookup's pieces follows from the verifier's own test of the
weights (`HTailF2.tileSelfTestF`, OnBytes/Model/Tail.lean) and the vector's shape.

Definitions, and theorems with their proofs. The test's public conditions say of each of these
arrays something that is false of a vector of one row with one virtual row: the array of the digits
has at least four virtual rows, that of the planes three, a symbol array is of the kind «symbols»,
and every piece lies in the array of the digits.

Main names:
  `UShape F tU cols`: the state has array tU; it is of the kind «table», with one row, cols columns
    and one virtual row.
  `tileSelfTest_shapes`: what the test's public conditions say of the arrays' shapes.
  `pieces_zz`: every piece of the two lookup calls lies in the array of the digits.
  `uApart_tested`: `UApart` (OnBytes/Tie/Pv/Tail/EndCoef.lean) at the state before the row weights
    are set.
  `unitRow_tested`: so a vector of that shape has the weight 1 on its one row (`UnitRow`,
    OnBytes/Tie/Pv/Tail/EndRaw.lean) at the state at which the test runs.

Limits: the vector's shape and its number in the list of the tables' vectors are premises.


-/
import OnBytes.Tie.Pv.Tail.EndChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port Finset

/-- The state has array tU: a table of one row, cols columns and one virtual row. -/
structure UShape (F : Fork) (tU cols : Nat) : Prop where
  inside : tU < F.trees.size
  shape : shapeAt F tU = (HKind.table, 1, cols, 1)

/-- What the test's public conditions say of the arrays' shapes. -/
theorem tileSelfTest_shapes (tl : HTailF2) (F G : Fork) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : tl.tileSelfTestF F c = .ok (((), G), c')) :
    ∃ g nbW W, tl.wants = some (nbW, W) ∧ 1 ≤ nbW ∧
      (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * nbW + 2 ∧
      ([0, 1].all (tl.callHeld g nbW)) = true ∧ tl.piecesTile F W = true ∧
      (∀ mu, mu < tl.NM → tl.tieShapeHeld F mu = true) ∧ tl.planesShapeHeld F g = true := by
  unfold HTailF2.tileSelfTestF at h
  simp only [bind_ok, get_ok, ask_ok, lift_ok, mustAs_ok, Option.some.injEq] at h
  obtain ⟨g, _, _, ⟨_, rfl, rfl⟩, jo, _, _, ⟨_, rfl, rfl⟩, w, _, _, ⟨hw, rfl, rfl⟩,
    _, _, _, ⟨rfl, rfl, rfl⟩, _, _, _, ⟨⟨h5, rfl⟩, rfl⟩, _, _, _, ⟨rfl, rfl, rfl⟩,
    _, _, _, ⟨⟨h7, rfl⟩, rfl⟩, _, _, _, ⟨h8, rfl⟩, h⟩ := h
  rw [testAs_ok _ _ _ _ _ hd] at h8
  obtain ⟨_, rfl⟩ := h8
  obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨h10, rfl⟩, h⟩ := h
  rw [testAs_ok _ _ _ _ _ hd] at h10
  obtain ⟨_, rfl⟩ := h10
  obtain ⟨_, _, _, ⟨rfl, rfl, rfl⟩, _, _, _, ⟨⟨h12, rfl⟩, rfl⟩, _⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h5
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h12
  have hn : 1 ≤ w.1 := by
    unfold HTailF2.wants at hw
    simp only [] at hw
    split at hw
    · simp at hw
    · rw [← Option.some.inj hw]
      show 1 ≤ if _ then 2 else 1
      split <;> omega
  exact ⟨g, w.1, w.2, hw, hn, h5.1.1, h5.2, h7, h12.1.1.2, h12.2⟩

/-- Every piece of the two lookup calls lies in the array of the digits. -/
theorem pieces_zz (tl : HTailF2) (F : Fork) (g : Forest.Heard) (nbW : Nat)
    (W : List HTailF2.Want) (hw : tl.wants = some (nbW, W))
    (hc : ([0, 1].all (tl.callHeld g nbW)) = true) (hp : tl.piecesTile F W = true) :
    ∀ q p, p ∈ (tl.zOf q).pieces.toList → p.tree = tl.ix.ZZ := by
  -- the wanted pieces: (call q, index i) for q = 0, 1 and i below nbW
  have hW : ∀ q, q < 2 → ∀ i, i < nbW → ∃ w ∈ W, w.call = q ∧ w.i = i := by
    unfold HTailF2.wants at hw
    simp only [] at hw
    split at hw
    · simp at hw
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
      intro q hq i hi
      have hq' : q ∈ [0, 1] := by
        rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> simp
      by_cases h2 : (tl.tau - 2 ^ Nat.log2 tl.tau != 0) = true
      · rw [if_pos h2] at hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact ⟨_, List.mem_flatMap.2 ⟨q, hq', List.mem_cons_self⟩, rfl, rfl⟩
        · refine ⟨⟨q, 1, (q * if (tl.tau - 2 ^ Nat.log2 tl.tau != 0) = true then 2 else 1) + 1,
            2 ^ Nat.log2 tl.tau, tl.tau - 2 ^ Nat.log2 tl.tau, q * tl.mz, tl.mz⟩,
            List.mem_flatMap.2 ⟨q, hq', List.mem_cons_of_mem _ ?_⟩, rfl, rfl⟩
          simp only [h2, if_true]
          exact List.mem_cons_self
      · rw [if_neg h2] at hi
        obtain rfl : i = 0 := by omega
        exact ⟨_, List.mem_flatMap.2 ⟨q, hq', List.mem_cons_self⟩, rfl, rfl⟩
  simp only [HTailF2.piecesTile, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hp
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hc
  have hsz : ∀ q, q < 2 → (tl.zOf q).pieces.size = nbW := by
    intro q hq
    have hcq : tl.callHeld g nbW q = true := by
      rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
      · exact hc.1
      · exact hc.2
    simp only [HTailF2.callHeld, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcq
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hs⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcq
    exact hs
  have main : ∀ q, q < 2 → ∀ p, p ∈ (tl.zOf q).pieces.toList → p.tree = tl.ix.ZZ := by
    intro q hq p hpm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpm
    have hi' : i < nbW := by
      rw [← hsz q hq, ← Array.length_toList]
      exact hi
    obtain ⟨w, hwm, rfl, rfl⟩ := hW q hq i hi'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hp.2 w hwm
    have hlt : w.i < (tl.zOf w.call).pieces.size := by rw [hsz _ hq]; exact hi'
    have e : (tl.zOf w.call).pieces.getD w.i {} = (tl.zOf w.call).pieces.toList[w.i] := by
      simp [Array.getD, hlt]
    rw [← e]
    exact h1
  intro q p hpm
  by_cases h0 : q = 0
  · subst h0
    exact main 0 (by omega) p hpm
  · have e : tl.zOf q = tl.zOf 1 := by
      unfold HTailF2.zOf
      rw [if_neg (by simpa using h0), if_neg (by decide)]
    rw [e] at hpm
    exact main 1 (by omega) p hpm

/-- `UApart` at the state before the row weights are set, from the later test and the vector's
shape. -/
theorem uApart_tested (tl : HTailF2) (n0 tU cols : Nat) (F1 F2 F2' : Fork) (c1 c1' c2 c2' : Ctx)
    (hn : n0 < 4) (hU : tl.ix.U.getD n0 none = some tU) (hs : UShape F2 tU cols)
    (h1 : tl.coefficientsF F1 c1 = .ok (((), F2), c1')) (hd : c2.ch.dry = false)
    (h2 : tl.tileSelfTestF F2 c2 = .ok (((), F2'), c2')) : UApart tl n0 tU F1 := by
  obtain ⟨g, nbW, W, hw, hnb, hz, hc, hp, ht, hb⟩ := tileSelfTest_shapes tl F2 F2' c2 c2' hd h2
  obtain ⟨hsh, hsize⟩ := coefficientsF_shape tl F1 F2 c1 c1' h1
  have e1 : shapeAt F1 tU = (HKind.table, 1, cols, 1) := (hsh tU).symm.trans hs.shape
  have k2 : (F2.trees.getD tU {}).kind = HKind.table := congrArg (·.1) hs.shape
  have r2 : (F2.trees.getD tU {}).rows.size = 1 := congrArg (·.2.2.2) hs.shape
  have hZ : tl.ix.ZZ ≠ tU := by
    rintro rfl
    omega
  refine ⟨hn, hU, ⟨by rw [← hsize]; exact hs.inside, ?_⟩, ?_, hZ, ?_, ?_, ?_⟩
  · have : (F1.trees.getD tU {}).rows.size = 1 := congrArg (·.2.2.2) e1
    omega
  · have : (F1.trees.getD tU {}).kind = HKind.table := congrArg (·.1) e1
    rw [this]
    rfl
  · rintro rfl
    simp only [HTailF2.planesShapeHeld, Bool.and_eq_true, beq_iff_eq] at hb
    have := hb.1.1.1.1.1.1.1.1
    omega
  · intro mu hmu e
    have h3 := ht mu hmu
    simp only [HTailF2.tieShapeHeld, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    have hk : (F2.trees.getD (tl.gtTree.getD mu 0) {}).kind = HKind.symbols := by
      have := h3
      simp only [and_assoc] at this
      exact this.1
    rw [e, k2] at hk
    exact absurd hk (by decide)
  · intro q p hpm e
    exact hZ ((pieces_zz tl F2 g nbW W hw hc hp q p hpm).symm.trans e)

/-- A vector of that shape has the weight 1 on its one row at the state at which the test runs. -/
theorem unitRow_tested (tl : HTailF2) (n0 tU cols : Nat) (F1 F2 F2' : Fork)
    (c1 c1' c2 c2' : Ctx) (hn : n0 < 4) (hU : tl.ix.U.getD n0 none = some tU)
    (hs : UShape F2 tU cols) (h1 : tl.coefficientsF F1 c1 = .ok (((), F2), c1'))
    (hd : c2.ch.dry = false) (h2 : tl.tileSelfTestF F2 c2 = .ok (((), F2'), c2')) :
    UnitRow F2 tU := by
  have A := uApart_tested tl n0 tU cols F1 F2 F2' c1 c1' c2 c2' hn hU hs h1 hd h2
  have e1 : shapeAt F1 tU = (HKind.table, 1, cols, 1) :=
    ((coefficientsF_shape tl F1 F2 c1 c1' h1).1 tU).symm.trans hs.shape
  exact unitRow_run tl n0 tU F1 F2 c1 c1' A (congrArg (·.2.1) e1) h1

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.pieces_zz
#print axioms OnBytes.Tie.Pv.Tail.uApart_tested
#print axioms OnBytes.Tie.Pv.Tail.unitRow_tested
