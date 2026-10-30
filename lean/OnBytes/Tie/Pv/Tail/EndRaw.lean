-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndRaw.lean: the equations of a smallness test use virtual rows: sums of an
array's rows under row weights that the verifier's state holds. This file shows, under the premises
below, that the virtual rows in use are sums of the arrays' own entries under powers of the batching
element: the four equations `RawRows` (OnBytes/Tie/Pv/Tail/EndAll.lean), at the batching element of
the state at which the test runs. EndAll.lean asks them at that of the state behind `objectsF`: this
file does not join the two.
States. `rawRows_run`: `RawRows` holds where the verifier's own test of the weights
(`HTailF2.tileSelfTestF`, OnBytes/Model/Tail.lean) returns. `rawWorld_reads`: values that meet
premise (1) exist. The other statements are steps towards the first.
Under, for `rawRows_run`, six premises: (1) `ReadsRaw`: each entry of a virtual row in use is the
sum of its array's entries under the state's row weights; (2) the run is not dry
(`c.ch.dry = false`); (3) the test returns; (4), (5) the two of line 1 below; (6) all values are
read in a commutative ring K through a map ρ that respects 0, 1, sums, differences and products.
Does not show.
 1. Two premises on public numbers stay: the array of the digits has the virtual rows that the first
    computation puts there (two for each block, and two), and each table's vector is one row with
    the weight 1 that holds every position that a read names.
 2. Nothing on the product form of a row's weights, which is what the chain takes.

Notes in full, with every limit at length, stand at the end of this file.
-/
import OnBytes.Tie.Pv.Tail.EndAll
import OnBytes.Tie.Pv.Tail.EndTested

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port Finset

/-- What the test's first public conditions say. -/
theorem tileSelfTest_tiles (tl : HTailF2) (F G : Fork) (c c' : Ctx)
    (h : tl.tileSelfTestF F c = .ok (((), G), c')) :
    ∃ g nbW W, tl.heard = some g ∧ tl.wants = some (nbW, W) ∧
      ([0, 1].all (tl.callHeld g nbW)) = true ∧ tl.piecesTile F W = true := by
  unfold HTailF2.tileSelfTestF at h
  simp only [bind_ok, get_ok, ask_ok, lift_ok, mustAs_ok, Option.some.injEq] at h
  obtain ⟨g, _, _, ⟨hg, rfl, rfl⟩, jo, _, _, ⟨_, rfl, rfl⟩, w, _, _, ⟨hw, rfl, rfl⟩,
    _, _, _, ⟨rfl, rfl, rfl⟩, _, _, _, ⟨⟨h5, rfl⟩, rfl⟩, _, _, _, ⟨rfl, rfl, rfl⟩,
    _, _, _, ⟨⟨h7, rfl⟩, rfl⟩, _⟩ := h
  simp only [Bool.and_eq_true] at h5
  exact ⟨g, w.1, w.2, hg, hw, h5.2, h7⟩

/-- The array of the digits has as many rows as there are combinations. -/
theorem zz_rows (tl : HTailF2) (F : Fork) (W : List HTailF2.Want) (h : tl.piecesTile F W = true) :
    (F.trees.getD tl.ix.ZZ {}).R = tl.tau := by
  simp only [HTailF2.piecesTile, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.2

/-- There are fewer than 2^41 combinations: the first piece of the first call has 2^floor(log2 tau)
rows, and a piece has at most 2^40. -/
theorem tau_lt (tl : HTailF2) (F : Fork) (g : Forest.Heard) (nbW : Nat) (W : List HTailF2.Want)
    (hw : tl.wants = some (nbW, W)) (hc : tl.callHeld g nbW 0 = true)
    (hp : tl.piecesTile F W = true) : tl.tau < 2 ^ 41 := by
  let w0 : HTailF2.Want :=
    { call := 0, i := 0, row := 0 * nbW, r0 := 0, Rp := 2 ^ Nat.log2 tl.tau,
      c0 := 0 * tl.mz, Cp := tl.mz }
  have hW : w0 ∈ W ∧ 1 ≤ nbW := by
    unfold HTailF2.wants at hw
    simp only [] at hw
    split at hw
    · simp at hw
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
      refine ⟨List.mem_flatMap.2 ⟨0, by simp, List.mem_cons_self⟩, ?_⟩
      split <;> omega
  simp only [HTailF2.piecesTile, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h4⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hp.2 w0 hW.1
  simp only [HTailF2.callHeld, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hsz⟩, _⟩, _⟩, _⟩, hall⟩, _⟩, _⟩, _⟩ := hc
  have h0 : 0 < (tl.zOf 0).pieces.size := by omega
  have hmem : (tl.zOf 0).pieces.getD 0 {} ∈ (tl.zOf 0).pieces := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h0]
    exact Array.getElem_mem h0
  have hph := (Array.all_eq_true_iff_forall_mem.1 hall) _ hmem
  simp only [HTailF2.pieceHeld, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hph
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, ha⟩, hpow⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hph
  have e : 2 ^ ((tl.zOf 0).pieces.getD 0 {}).a = 2 ^ Nat.log2 tl.tau := hpow.trans h4
  have e' := Nat.pow_right_injective (le_refl 2) e
  have hl : Nat.log2 tl.tau ≤ 40 := by omega
  calc tl.tau < 2 ^ (Nat.log2 tl.tau + 1) := Nat.lt_log2_self
    _ ≤ 2 ^ 41 := Nat.pow_le_pow_right (by decide) (by omega)

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- Array t has one row, and its first virtual row has the weight 1 on it. -/
def UnitRow (F : Fork) (t : Nat) : Prop :=
  (F.trees.getD t {}).R = 1 ∧ ((F.trees.getD t {}).rows.getD 0 {}).coef.getD 0 zeroE = oneE

/-- In the world W an entry of virtual row r of array t is the combination of the array's rows,
whose entries are A t R i, under the row weights that the state F holds. -/
def ReadsRow (F : Fork) (W : World K) (A : Nat → Nat → Nat → K) (t r : Nat) : Prop :=
  ∀ i, W.entry t r i = ∑ R ∈ range (F.trees.getD t {}).R,
    ρ.val (((F.trees.getD t {}).rows.getD r {}).coef.getD R zeroE) * A t R i

/-- So it is at the virtual rows that the ties and the reads use: the two last of the array of the
digits, the one of each symbol array, the first of each table's vector. -/
structure ReadsRaw (tl : HTailF2) (funs : Array HFun) (F : Fork) (W : World K)
    (A : Nat → Nat → Nat → K) : Prop where
  ties : ReadsRow ρ F W A tl.ix.ZZ tl.zzRowTies
  reads : ReadsRow ρ F W A tl.ix.ZZ tl.zzRowReads
  syms : ∀ mu, mu < tl.NM → ReadsRow ρ F W A (tl.gtTree.getD mu 0) 0
  tabs : ∀ x ∈ readsList tl funs, ReadsRow ρ F W A (uOf tl x.1) 0

/-- The world with these entries, and any values under the slots. -/
def rawWorld (F : Fork) (slot : Nat → K) (A : Nat → Nat → Nat → K) : World K where
  slot := slot
  entry := fun t r i => ∑ R ∈ range (F.trees.getD t {}).R,
    ρ.val (((F.trees.getD t {}).rows.getD r {}).coef.getD R zeroE) * A t R i

/-- That world reads the rows so. -/
theorem rawWorld_reads (tl : HTailF2) (funs : Array HFun) (F : Fork) (slot : Nat → K)
    (A : Nat → Nat → Nat → K) : ReadsRaw ρ tl funs F (rawWorld ρ F slot A) A :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- The number of blocks of the first computation is the second's, where the array of the digits has
the virtual rows that the first computation lays: two for each block, and two. -/
theorem blocks_eq (tl : HTailF2) (F : Fork) (h : SelfTested tl F)
    (hrows : (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2) :
    ∀ nbW Wn, tl.wants = some (nbW, Wn) → nbW = tl.zzBlocks := by
  intro nbW Wn hw
  obtain ⟨nbW', Wn', hw', hs, -⟩ := h.wants
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hw.symm.trans hw'))
  omega

/-- The four equations, from what the test's success says, in every such world. -/
theorem rawRows_tested (tl : HTailF2) (F G : Fork) (funs : Array HFun) (W : World K)
    (A : Nat → Nat → Nat → K) (hW : ReadsRaw ρ tl funs F W A) (h : SelfTested tl F)
    (hR : (F.trees.getD tl.ix.ZZ {}).R = tl.tau) (ht : tl.tau ≤ 2 ^ 64)
    (hb : ∀ nbW Wn, tl.wants = some (nbW, Wn) → nbW = tl.zzBlocks)
    (hU : ∀ x ∈ readsList tl funs, UnitRow F (uOf tl x.1) ∧
      ∀ d, d < (tl.mats.getD x.1.mat {}).k → posOf tl x.1 x.2 d < colsU G (uOf tl x.1)) :
    RawRows W tl G funs (ρ.val F.theta) A := by
  obtain ⟨nbW, Wn, hw, _, hsh, hu, hwt, _, _⟩ := h.wants
  have e := hb nbW Wn hw
  subst e
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [hW.ties, hR]
    apply Finset.sum_congr rfl
    intro u hu'
    simp only [HTailF2.zzRowTies]
    rw [(hu u (Finset.mem_range.1 hu')).2, ρ.pow]
  · intro i
    rw [hW.reads, hR]
    apply Finset.sum_congr rfl
    intro u hu'
    simp only [HTailF2.zzRowReads]
    rw [(hu u (Finset.mem_range.1 hu')).1, ρ.pow]
  · intro mu hmu p
    have hs := hsh mu hmu
    simp only [HTailF2.tieShapeHeld, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    have hw' := hwt mu hmu
    have hXR : (F.trees.getD (tl.gtTree.getD mu 0) {}).R = (tl.shp.getD mu {}).mS := by
      omega
    have hsR : (tl.shp.getD mu {}).R = (tl.shp.getD mu {}).mS := by
      omega
    rw [hW.syms mu hmu, hXR]
    apply Finset.sum_congr rfl
    intro i' hi'
    rw [tie_rowWeight ρ tl F _ mu hw' (tie_R_le tl F _ mu hw') i'
      (by rw [hsR]; exact Finset.mem_range.1 hi'), pow2Again_tau tl ht]
  · intro x hx d hd
    obtain ⟨⟨h1, h2⟩, hp⟩ := hU x hx
    have hlt := hp d hd
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, hW.tabs x hx, h1]
    simp only [Finset.sum_range_one, h2, ρ.one, one_mul]

/-- The four equations, in a world that reads the rows so (ReadsRaw), from a run of the verifier's
own test of the weights on a view that is not dry, under the two premises on public numbers (hrows,
hU). -/
theorem rawRows_run (tl : HTailF2) (F F' G : Fork) (c c' : Ctx) (funs : Array HFun)
    (W : World K) (A : Nat → Nat → Nat → K) (hW : ReadsRaw ρ tl funs F W A) (hd : c.ch.dry = false)
    (h : tl.tileSelfTestF F c = .ok (((), F'), c'))
    (hrows : (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2)
    (hU : ∀ x ∈ readsList tl funs, UnitRow F (uOf tl x.1) ∧
      ∀ d, d < (tl.mats.getD x.1.mat {}).k → posOf tl x.1 x.2 d < colsU G (uOf tl x.1)) :
    RawRows W tl G funs (ρ.val F.theta) A := by
  obtain ⟨g, nbW, Wn, -, hw, hc, hp⟩ := tileSelfTest_tiles tl F F' c c' h
  have hc0 : tl.callHeld g nbW 0 = true := by
    simp only [List.all_cons, Bool.and_eq_true] at hc
    exact hc.1
  have ht := tau_lt tl F g nbW Wn hw hc0 hp
  exact rawRows_tested ρ tl F G funs W A hW (tileSelfTest_ok tl F F' c c' hd h).2.2
    (zz_rows tl F Wn hp) (Nat.le_of_lt (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide)
      (by decide)))) (blocks_eq tl F (tileSelfTest_ok tl F F' c c' hd h).2.2 hrows) hU

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.tileSelfTest_tiles
#print axioms OnBytes.Tie.Pv.Tail.tau_lt
#print axioms OnBytes.Tie.Pv.Tail.rawRows_tested
#print axioms OnBytes.Tie.Pv.Tail.rawRows_run

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Tie/Pv/Tail/EndRaw.lean: in every world in which an entry of a virtual row is the
combination of its array's rows under the row weights that the state holds, the virtual rows that
the ties and the reads of the smallness test use are sums of the arrays' own entries under powers of
the batching element.

Theorems with their proofs. The verifier's own test of the weights (`HTailF2.tileSelfTestF`,
OnBytes/Model/Tail.lean) compares the row weights entry by entry with a second computation, right
before the one equation is passed on. So on a run on a view on which that test succeeds, the row
weights have the closed form, whoever has set them.

Main names:
  `tileSelfTest_tiles`: what the test's first public conditions say: the pieces of the two lookup
    calls are the expected ones.
  `zz_rows`: the array of the digits has as many rows as there are combinations.
  `tau_lt`: there are fewer than 2^41 combinations.
  `UnitRow F t`: array t has one row, and its first virtual row has the weight 1 on it.
  `ReadsRow`, `ReadsRaw`: W is such a world, at the state F and the arrays' entries A, at the
    virtual rows that the ties and the reads use; `rawWorld`, `rawWorld_reads`: there is one.
  `blocks_eq`: the first computation's number of blocks is the second's.
  `rawRows_tested`: the four equations (`RawRows`, OnBytes/Tie/Pv/Tail/EndAll.lean) hold in such a
    world.
  `rawRows_run`: the same from a run of the test.

Limits: two premises on public numbers stay: the array of the digits has the virtual rows that the
first computation lays (two for each block, and two), and each table's vector is one row with the
weight 1 that holds every place that a read names. Nothing on the product form of a row's weights,
which is what the chain takes.


-/
