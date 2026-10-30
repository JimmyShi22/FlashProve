-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CoefsFit.lean: «EVERY VIRTUAL ROW OF EVERY ARRAY OF THE LEDGER HAS A
WEIGHT FOR EACH OF ITS ARRAY's ROWS»: THE FOURTH SHARE OF THE PUBLIC TEST `totalIn`
(Johnson/Desc/First/Batch/FormsIn.lean), AT THE VERIFIER's STATE BEHIND A YES OF THE APPROXIMATE
RANGE PROOF's RUN OF SELF TESTS (`k8Tests`, Johnson/Desc/First/Batch/Law/K8Tests.lean). Definitions
and theorems. No text already in the library turns.

What is said.
  `RowsFit X`: each virtual row of the array X has as many weights as X has rows. `CoefsFit F`: so
    at every array of the ledger F; `coefsFit_trees`: it reads the arrays alone.
  `wants_rows`: the pieces that the test by a second computation expects name every virtual row of
    the digits' array in front of its last two.
  `fit_digits`, `fit_planes`, `fit_symbols`: **a yes of the test by a second computation
    (`rkSelfTestP`) gives `RowsFit` at the digits' array, the planes' array, each matrix's array of
    symbols**: by its own guards (`rk_all`, Johnson/Desc/First/TailClaims/EquationsSelf.lean).
  `oneRowLook sh t`: A TEST ON THE LOOKS: number t is of the kind "table", with one row and ONE
    virtual row. `fit_table`: **NO TEST OF THE RUN READS A TABLE's VECTOR's WEIGHTS' NUMBER: IT
    FOLLOWS BY THE MAKE**: the step that lays the weights lays the one weight 1 there
    (`coefficientsF_unit`, OnBytes/Tie/Pv/Tail/EndCoef.lean), where the vector's array is another
    than the digits', the planes', the symbols' and the pieces'; the looks give one row.
  `tableAtB sh tl t`, `sortsB sh tl`: TESTS ON THE LOOKS AND THE RANGE PROOF's PLANNED NUMBERS: t is
    such a table's vector; every number below sh's length is the digits', the planes', a symbols'
    array's, or such a vector's.
  `fit_tests`: **behind a yes of `k8Tests`: the ledger has the looks still, and `RowsFit` at every
    array.** `totalIn_tests`: **so the public test there, from its three other shares.**
  A MEMBER AND NEGATIVE TESTS. `rowsFit_toy`, `rowsFit_toy_no`, `oneRow_toy`.
Limits. (1) `sortsB` is evaluated at the small configuration's five sub-proofs alone
(LooksAtSmall.lean [not in this library]); no theorem at any plan. (2) The looks in front of the
run are a premise
(Johnson/Desc/First/Link/Law/LooksAre.lean says who makes and keeps them). (3) AT THE STATE BEHIND
THE RUN OF SELF TESTS ALONE: a run that stands behind it in a link's order must leave the arrays
(`coefsFit_trees`): not shown of any. (4) The three other shares are premises. Nothing on soundness.
Words. "The ledger": the structure Fork.
-/
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.First.Batch.Law.K8CoefAll
import Johnson.Desc.First.TailClaims.EquationsSelf
import OnBytes.Tie.Pv.Tail.EndCoef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (hasRow coefAt UApart coefficientsF_unit bind_ok get_ok modify_ok)
open VerifiableInference.Desc.First.TailClaims (rkSelfTestP coefBody)
open VerifiableInference.Desc.First.TailClaims.Law (rk_all coefBody_all)
open VerifiableInference.Desc.K9 (atS totalIn maskSeat arrayIn)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)

/-! ## 1 The property -/

/-- Each virtual row has as many weights as the array has rows. -/
def RowsFit (X : HTree) : Prop := ∀ R ∈ X.rows, R.coef.size = X.R

/-- So at every array of the ledger. -/
def CoefsFit (F : Fork) : Prop := ∀ i, i < F.trees.size → RowsFit (F.trees.getD i {})

theorem coefsFit_trees {F G : Fork} (h : G.trees = F.trees) (hF : CoefsFit F) : CoefsFit G := by
  unfold CoefsFit at hF ⊢
  rw [h]
  exact hF

theorem rowsFit_of_getD (X : HTree) (n : ℕ) (hn : X.rows.size = n)
    (h : ∀ i, i < n → (X.rows.getD i {}).coef.size = X.R) : RowsFit X := by
  intro R hR
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hR
  have e := h i (hn ▸ hi)
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at e

/-! ## 2 What the test by a second computation gives -/

/-- The expected pieces name every virtual row in front of the last two. -/
theorem wants_rows (tl : HTailF2) (nbW : ℕ) (Wn : List Want) (hw : tl.wants = some (nbW, Wn)) :
    ∀ i, i < 2 * nbW → ∃ w ∈ Wn, w.row = i := by
  unfold HTailF2.wants at hw
  simp only at hw
  split at hw
  · exact nomatch hw
  · obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj hw)
    subst e1
    subst e2
    intro i hi
    by_cases hr : (tl.tau - 2 ^ Nat.log2 tl.tau != 0) = true
    · simp only [hr, if_true] at hi ⊢
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp
    · simp only [hr, Bool.false_eq_true, if_false] at hi ⊢
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;> simp

/-- **The digits' array.** -/
theorem fit_digits (tl : HTailF2) (F : Fork) (h : rkSelfTestP tl F = .ok ()) :
    RowsFit (F.trees.getD tl.ix.ZZ {}) := by
  obtain ⟨g, jo, nbW, Wn, _, _, hw, g1, g2, _, _, g5, _⟩ := rk_all tl F h
  simp only [Bool.and_eq_true] at g1 g5
  unfold HTailF2.piecesTile at g2
  simp only [Bool.and_eq_true] at g2
  have hsize : (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * nbW + 2 := beq_iff_eq.1 g1.1.1
  have hR : (F.trees.getD tl.ix.ZZ {}).R = tl.tau := beq_iff_eq.1 g2.1.1.1.1.2
  refine rowsFit_of_getD _ _ hsize fun i hi => ?_
  by_cases h1 : i < 2 * nbW
  · obtain ⟨w, hwm, rfl⟩ := wants_rows tl nbW Wn hw i h1
    have hx := List.all_eq_true.1 g2.2 w hwm
    simp only [Bool.and_eq_true] at hx
    exact beq_iff_eq.1 hx.1.2
  · have : i = 2 * nbW ∨ i = 2 * nbW + 1 := by omega
    rcases this with rfl | rfl
    · rw [hR]
      exact beq_iff_eq.1 g5.1.1.1.1.1.1.1
    · rw [hR]
      exact beq_iff_eq.1 g5.1.1.1.1.1.1.2

/-- **The planes' array.** -/
theorem fit_planes (tl : HTailF2) (F : Fork) (h : rkSelfTestP tl F = .ok ()) :
    RowsFit (F.trees.getD tl.ix.BZ {}) := by
  obtain ⟨g, jo, nbW, Wn, _, _, _, _, _, _, _, g5, _⟩ := rk_all tl F h
  simp only [Bool.and_eq_true] at g5
  have hp := g5.2
  unfold HTailF2.planesShapeHeld at hp
  simp only [Bool.and_eq_true] at hp
  have hsize : (F.trees.getD tl.ix.BZ {}).rows.size = 3 := beq_iff_eq.1 hp.1.1.1.1.1.1.1.1
  have hR : (F.trees.getD tl.ix.BZ {}).R = 32 := beq_iff_eq.1 hp.1.1.1.1.1.1.1.2
  refine rowsFit_of_getD _ _ hsize fun i hi => ?_
  have hx := List.all_eq_true.1 hp.1.1.2 i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at hx
  rw [hR]
  exact beq_iff_eq.1 hx.1

/-- **Each matrix's array of symbols.** -/
theorem fit_symbols (tl : HTailF2) (F : Fork) (h : rkSelfTestP tl F = .ok ()) (mu : ℕ)
    (hmu : mu < tl.NM) : RowsFit (F.trees.getD (tl.gtTree.getD mu 0) {}) := by
  obtain ⟨g, jo, nbW, Wn, _, _, _, _, _, _, _, g5, _⟩ := rk_all tl F h
  simp only [Bool.and_eq_true] at g5
  have hp := List.all_eq_true.1 g5.1.1.2 mu (List.mem_range.2 hmu)
  unfold HTailF2.tieShapeHeld at hp
  simp only [Bool.and_eq_true] at hp
  have hsize : (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.size = 1 := beq_iff_eq.1
      hp.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hR : (F.trees.getD (tl.gtTree.getD mu 0) {}).R = (tl.shp.getD mu {}).Rr :=
    beq_iff_eq.1 hp.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  refine rowsFit_of_getD _ _ hsize fun i hi => ?_
  obtain rfl : i = 0 := by omega
  rw [hR]
  exact beq_iff_eq.1 hp.1.1.1.2

/-! ## 3 A table's vector: by the make -/

/-- **A test on the looks**: of the kind "table", one row, ONE virtual row. -/
def oneRowLook (sh : List Look) (t : ℕ) : Bool :=
  match sh[t]? with
  | some x => x.1 == HKind.table && x.2.1 == 1 && x.2.2.2 == 1
  | none => false

theorem oneRow_spec {sh : List Look} {t : ℕ} (h : oneRowLook sh t = true) :
    ∃ K, sh[t]? = some (HKind.table, 1, K, 1) := by
  unfold oneRowLook at h
  cases e : sh[t]? with
  | none =>
    rw [e] at h
    exact nomatch h
  | some x =>
    rw [e] at h
    have h' : (x.1 == HKind.table && x.2.1 == 1 && x.2.2.2 == 1) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨k, R, K, n⟩ := x
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h'
    exact ⟨K, rfl⟩

theorem unit_of_oneRow {sh : List Look} {t : ℕ} (h : oneRowLook sh t = true) :
    unitLook sh t = true := by
  obtain ⟨K, e⟩ := oneRow_spec h
  unfold unitLook
  rw [e]
  rfl

/-- **The step that lays the weights lays the one weight 1 on a table's one row.** -/
theorem fit_table {sh : List Look} (tl : HTailF2) (g : Forest.Heard) (hg : tl.heard = some g)
    (F : Fork) (hl : LooksAre sh F) (n0 tU : ℕ) (h0 : n0 < 4)
    (hU : tl.ix.U.getD n0 none = some tU) (h1 : oneRowLook sh tU = true)
    (uZZ : tl.ix.ZZ ≠ tU) (uBZ : tl.ix.BZ ≠ tU)
    (uS : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tU)
    (uP : ∀ q p, p ∈ (tl.zOf q).pieces.toList → p.tree ≠ tU) :
    RowsFit ((coefBody tl g F).trees.getD tU {}) := by
  obtain ⟨s1, s2, _⟩ := shape_at hl tU (unit_of_oneRow h1)
  let c : Ctx := { ch := { dry := false, entries := [] } }
  have hrun : tl.coefficientsF F c = .ok (((), Fo.coefAll tl g F), c) := by
    rw [Fo.coefficientsF_eq]
    exact (bind_ok _ _ F c _).2 ⟨g, F, c, (get_ok _ F F c c g).2 ⟨hg, rfl, rfl⟩,
      (modify_ok _ F _ c c ()).2 ⟨rfl, rfl⟩⟩
  have hc : coefAt (coefBody tl g F) tU 0 = #[oneE] := by
    rw [coefBody_all]
    exact coefficientsF_unit tl n0 tU F _ c c ⟨h0, hU, s1, s2, uZZ, uBZ, uS, uP⟩ hrun
  obtain ⟨K, e⟩ := oneRow_spec h1
  obtain ⟨_, e2⟩ := looks_get ((looks_rests sh).coef tl g F hl) tU _ e
  have hn : ((coefBody tl g F).trees.getD tU {}).rows.size = 1 := congrArg (·.2.2.2) e2
  have hR : ((coefBody tl g F).trees.getD tU {}).R = 1 := congrArg (·.2.1) e2
  refine rowsFit_of_getD _ _ hn fun i hi => ?_
  obtain rfl : i = 0 := by omega
  have hc' : (((coefBody tl g F).trees.getD tU {}).rows.getD 0 {}).coef = #[oneE] := hc
  rw [hc', hR]
  rfl

/-! ## 4 Every array is of one of four sorts -/

/-- **A test on the looks and the planned numbers**: t is a table's vector, of one row and one
virtual row, and another array than the digits', the planes', the symbols' and the pieces'. -/
def tableAtB (sh : List Look) (tl : HTailF2) (t : ℕ) : Bool :=
  ((List.range 4).any fun n => tl.ix.U.getD n none == some t) && oneRowLook sh t &&
    tl.ix.ZZ != t && tl.ix.BZ != t && ((List.range tl.NM).all fun mu => tl.gtTree.getD mu 0 != t) &&
    (tl.z1.pieces.toList.all fun p => p.tree != t) && tl.z2.pieces.toList.all fun p => p.tree != t

/-- **Every number below the looks' length is of one of the four sorts.** -/
def sortsB (sh : List Look) (tl : HTailF2) : Bool :=
  (List.range sh.length).all fun t =>
    t == tl.ix.ZZ || t == tl.ix.BZ || ((List.range tl.NM).any fun mu => tl.gtTree.getD mu 0 == t) ||
      tableAtB sh tl t

/-- **Behind the step that lays the weights and a yes of the test by a second computation.** -/
theorem fit_all {sh : List Look} (tl : HTailF2) (g : Forest.Heard) (hg : tl.heard = some g)
    (F : Fork) (hl : LooksAre sh F) (hB : sortsB sh tl = true)
    (hrk : rkSelfTestP tl (coefBody tl g F) = .ok ()) :
    ∀ i, i < sh.length → RowsFit ((coefBody tl g F).trees.getD i {}) := by
  intro i hi
  have hx := List.all_eq_true.1 hB i (List.mem_range.2 hi)
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at hx
  rcases hx with ((rfl | rfl) | ⟨mu, hmu, rfl⟩) | ht
  · exact fit_digits tl _ hrk
  · exact fit_planes tl _ hrk
  · exact fit_symbols tl _ hrk mu hmu
  · unfold tableAtB at ht
    simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
      bne_iff_ne, ne_eq] at ht
    obtain ⟨⟨⟨⟨⟨⟨⟨n0, h0, hU⟩, h1⟩, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩ := ht
    refine fit_table tl g hg F hl n0 i h0 hU h1 a1 a2 a3 fun q p hp => ?_
    unfold HTailF2.zOf at hp
    split at hp
    · exact a4 p hp
    · exact a5 p hp

/-- **BEHIND A YES OF THE RUN OF SELF TESTS.** -/
theorem fit_tests (sh : List Look) (nU : Array ℕ) (e t : S) (h : k8Tests nU e = .ok t)
    (hl : HasFork (LooksAre sh) e) (hB : ∀ tl, e.tl? = some tl → sortsB sh tl = true) :
    ∃ G, t.fork? = some G ∧ LooksAre sh G ∧ CoefsFit G := by
  obtain ⟨F, tl, g, hF, htl, hg, _, hrk, rfl⟩ := k8Tests_ok nU e t h
  obtain ⟨F', hF', hl⟩ := hl
  obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
  have hl' := (looks_rests sh).coef tl g F hl
  refine ⟨_, fork_put e tl F _ hF, hl', fun i hi => ?_⟩
  exact fit_all tl g hg F hl (hB tl htl) hrk i (looks_size hl' ▸ hi)

/-- **THE PUBLIC TEST THERE, FROM ITS THREE OTHER SHARES.** -/
theorem totalIn_tests (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ) (e t : S)
    (a : K9.Part) (h : k8Tests nU e = .ok t) (ha : atS.get? t = some a)
    (hl : HasFork (LooksAre sh) e) (hB : ∀ tl, e.tl? = some tl → sortsB sh tl = true)
    (t1 : a.F.LS.size = a.F.ns ∧ a.F.vp.size = a.F.ns ∧ a.F.mf.size = a.F.ns)
    (t2 : (maskSeat own a).isSome = true)
    (t3 : ∀ i, i < sh.length → (arrayIn own a i).isSome = true) : totalIn own t = true := by
  obtain ⟨G, hG, hl', hc⟩ := fit_tests sh nU e t h hl hB
  obtain rfl : G = a.F := Option.some.inj (hG.symm.trans (fork_part t a ha))
  refine totalIn_of_looks sh own t a ha ⟨_, hG, hl'⟩ t1 t2 t3 fun i x hx R hR => ?_
  obtain ⟨hi, e2⟩ := looks_get hl' i x hx
  rw [hc i hi R hR, ← e2]
  rfl

/-! ## 5 A member, and negative tests -/

theorem rowsFit_toy : RowsFit { R := 1, K := 3, rows := #[{ coef := #[oneE] }] } := by
  intro R hR
  simp at hR
  subst hR
  rfl

/-- NEGATIVE: a virtual row without a weight. -/
theorem rowsFit_toy_no : ¬ RowsFit { R := 1, K := 3, rows := #[{}] } := by
  intro h
  have e := h {} (by simp)
  simp at e

/-- One yes; NEGATIVE: two virtual rows · two rows · the kind "symbols". -/
theorem oneRow_toy : oneRowLook [(HKind.table, 1, 3, 1)] 0 = true ∧
    oneRowLook [(HKind.table, 1, 3, 2)] 0 = false ∧ oneRowLook [(HKind.table, 2, 3, 1)] 0 = false ∧
    oneRowLook [(HKind.symbols, 1, 3, 1)] 0 = false := ⟨rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.wants_rows
#print axioms VerifiableInference.Desc.LinkJoin.fit_digits
#print axioms VerifiableInference.Desc.LinkJoin.fit_planes
#print axioms VerifiableInference.Desc.LinkJoin.fit_symbols
#print axioms VerifiableInference.Desc.LinkJoin.fit_table
#print axioms VerifiableInference.Desc.LinkJoin.fit_all
#print axioms VerifiableInference.Desc.LinkJoin.fit_tests
#print axioms VerifiableInference.Desc.LinkJoin.totalIn_tests
#print axioms VerifiableInference.Desc.LinkJoin.rowsFit_toy
#print axioms VerifiableInference.Desc.LinkJoin.rowsFit_toy_no
#print axioms VerifiableInference.Desc.LinkJoin.oneRow_toy
