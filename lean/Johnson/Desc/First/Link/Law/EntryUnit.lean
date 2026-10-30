-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/EntryUnit.lean: THE PLAIN PAYERS' PREMISE ON THE ENTRIES OF VIRTUAL ROWS
(hFu), BROUGHT DOWN, ONCE FOR ALL OF THEM, TO TWO NAMED CLAUSES, at every virtual row
whose weights are fixed before the draw; the unit rows are a case. Theorems: tools. IT PAYS NEITHER
CLAUSE.

Why. K4Run.lean, K11Run.lean and StillRun.lean (beside this file), and the files that build on
them, each take hFu: «at a full state that goes on from q the entries of virtual rows that the run's
forms name are `ent q y`». An entry is a sum over its array's rows under the virtual row's weights,
and these weights are laid, and some of them turned, BEHIND the draw
(Johnson/Desc/First/TailClaims/Coefficients.lean): so «goes on from q» cannot pin them. But where
virtual row r has the weight 1 on the array's row r and 0 on the others (`UnitAt`), its entry IS the
array's own cell (r, i).

What is said.
  `UnitAt F t r`: the array t has a row r, and virtual row r's weights are 1 there and 0 elsewhere.
    `unitAt_of_row`: `UnitRow F t` (OnBytes/Tie/Pv/Tail/EndRaw.lean: one row; the first virtual
    row's weight is 1) is `UnitAt F t 0`. `entry_unit`: at such a row entry i is cell (r, i) of the
    array, off the data. `entUnit q y`: the cells by the snapshot's list of arrays. `entry_fixed`:
    **at a state that goes on from q, at such a row, the entry is `entUnit q y`.**
  `hFu_of`: **hFu for whatever entries a kind names** (a letter `Named q x`), from: h1, ON WHAT IS
    FIXED: each named entry stands in a row that q marks (`Un q tree row`); h2, ON «FULL»: at a full
    state that goes on from q every marked row is a unit.
  `WeightsAre F t r n w`, `entBy`, `entry_by`, `hFu_by`: **the general form**: the array has n rows
    and virtual row r's weights on them are w, n and w being functions of q: a row that nobody lays
    (no weight: the entry is 0), a unit row, a row of weights made of what was heard before the
    draw.

Limits. IT PAYS NEITHER h1 NOR h2. h1 is a test on the forms: each kind's. h2 IS NO FACT ON THE
LEDGER THAT «GOES ON» GIVES: of the arrays «goes on» keeps the widths alone: so all of `UnitAt` must
come out of «full»: it is a clause of what «full» MEANS (the marks must be readable off the state
too: «goes on» keeps the walk's record). The debt then stands where «full» is owed: behind the last
move of the batching's row (`hend`): there the smallness test must show that its step lays these
weights and that no later move of the row turns them. A form that names a row whose weights hang on
the batching element falls outside h1, and hFu holds of it at no `ent` (by reading: no theorem).
Whether the entries that the layers', attention's, the head's and the merge's forms name stand at
unit rows is held by reading alone; of the layers' it is not held: they name row e / K3. Nothing on
soundness.

-/
import Johnson.Desc.First.Batch.Law.Raw
import Johnson.Desc.First.Batch.Law.FitsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.EntryUnit
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail (UnitRow)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)

/-- The array t has a row r, and virtual row r has the weight 1 on it and 0 on the others. -/
def UnitAt (F : Fork) (t r : ℕ) : Prop :=
  r < (F.trees.getD t {}).R ∧ ∀ j < (F.trees.getD t {}).R,
    ((F.trees.getD t {}).rows.getD r {}).coef.getD j zeroE = if j = r then oneE else zeroE

theorem unitAt_of_row {F : Fork} {t : ℕ} (h : UnitRow F t) : UnitAt F t 0 := by
  refine ⟨by rw [h.1]; exact Nat.one_pos, fun j hj => ?_⟩
  rw [h.1] at hj
  obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
  simpa using h.2

variable {α K : Type} [CommRing K] (ρ : Reading K)

/-- At a virtual row that is a unit the entries are the array's own cells. -/
theorem entry_unit (L : LinkCtx) (F : Fork) (D : Bound K) (t r i : ℕ) (h : UnitAt F t r) :
    (worldAt ρ L F D).entry t r i = cellsOf L D t r i := by
  rw [worldAt_readsRow ρ L F D t r i, Finset.sum_eq_single r]
  · rw [h.2 r h.1, if_pos rfl, ρ.one, one_mul]
  · intro j hj hne
    rw [h.2 j (Finset.mem_range.1 hj), if_neg hne, ρ.zero, zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 h.1) hn

/-- The cells by the snapshot's list of arrays. -/
def entUnit (q : α × Option Pub9) (y : Bound K) : ℕ → ℕ → ℕ → K := fun t r i =>
  match q.2 with
  | some u => y.cell (u.arrayOf.getD t (0, "")).1 (u.arrayOf.getD t (0, "")).2 r i
  | none => 0

/-- **At a state that goes on from q, at such a row, the entry is fixed by q and the data.** -/
theorem entry_fixed (φ : S → α) (Ok : α × Option Pub9 → Prop) (q : α × Option Pub9) (t : S)
    (b : K9.Part) (y : Bound K) (hf : Fx9 φ Ok q t) (hb : atS.get? t = some b) (k r i : ℕ)
    (hU : UnitAt b.F k r) : (worldAt ρ b.L b.F y).entry k r i = entUnit q y k r i := by
  obtain ⟨_, _, u, b', hu, hb', g⟩ := hf
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  rw [entry_unit ρ b.L b.F y k r i hU]
  simp only [entUnit, hu, cellsOf, g.2.2.2.1]

/-- **hFu, FOR WHATEVER ENTRIES A KIND NAMES, FROM TWO CLAUSES.** -/
theorem hFu_of (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (Named : α × Option Pub9 → Ent → Prop) (Un : α × Option Pub9 → ℕ → ℕ → Prop)
    (h1 : ∀ q x, Ok q → Named q x → Un q x.tree x.row)
    (h2 : ∀ q t b, Fx9 φ Ok q t → Fu t → atS.get? t = some b → ∀ k r, Un q k r → UnitAt b.F k r)
    (q : α × Option Pub9) (t : S) (b : K9.Part) (y : Bound K) (hf : Fx9 φ Ok q t) (hfu : Fu t)
    (hb : atS.get? t = some b) (x : Ent) (hx : Named q x) :
    (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  entry_fixed ρ φ Ok q t b y hf hb x.tree x.row x.idx
    (h2 q t b hf hfu hb x.tree x.row (h1 q x hf.1 hx))

/-! ## The general form: weights that are fixed by q -/

/-- Array t has n rows, and virtual row r's weights on them are w. -/
def WeightsAre (F : Fork) (t r n : ℕ) (w : ℕ → E) : Prop :=
  (F.trees.getD t {}).R = n ∧ ∀ j < n, ((F.trees.getD t {}).rows.getD r {}).coef.getD j zeroE = w j

theorem weightsAre_of_unit {F : Fork} {t r : ℕ} (h : UnitAt F t r) :
    WeightsAre F t r (F.trees.getD t {}).R fun j => if j = r then oneE else zeroE :=
  ⟨rfl, h.2⟩

/-- The entries under weights that q names. -/
def entBy (n : α × Option Pub9 → ℕ → ℕ) (w : α × Option Pub9 → ℕ → ℕ → ℕ → E)
    (q : α × Option Pub9) (y : Bound K) : ℕ → ℕ → ℕ → K := fun t r i =>
  ∑ j ∈ Finset.range (n q t), ρ.val (w q t r j) * entUnit q y t j i

/-- At the unit's weights they are the cells: so the unit rows are a case of the general form. -/
theorem entBy_unit (n : α × Option Pub9 → ℕ → ℕ) (q : α × Option Pub9) (y : Bound K) (k r i : ℕ)
    (hr : r < n q k) :
    entBy ρ n (fun _ _ r j => if j = r then oneE else zeroE) q y k r i = entUnit q y k r i := by
  unfold entBy
  rw [Finset.sum_eq_single r]
  · simp only [if_true, ρ.one, one_mul]
  · intro j _ hne
    simp only [if_neg hne, ρ.zero, zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 hr) hn

/-- At no weight they are 0: a row that nobody lays. -/
theorem entBy_zero (n : α × Option Pub9 → ℕ → ℕ) (q : α × Option Pub9) (y : Bound K) (k r i : ℕ) :
    entBy ρ n (fun _ _ _ _ => zeroE) q y k r i = 0 := by
  unfold entBy
  exact Finset.sum_eq_zero fun j _ => by rw [ρ.zero, zero_mul]

/-- **At a state that goes on from q, at a row whose weights are those that q names, the entry is
fixed by q and the data.** -/
theorem entry_by (φ : S → α) (Ok : α × Option Pub9 → Prop) (n : α × Option Pub9 → ℕ → ℕ)
    (w : α × Option Pub9 → ℕ → ℕ → ℕ → E) (q : α × Option Pub9) (t : S) (b : K9.Part)
    (y : Bound K) (hf : Fx9 φ Ok q t) (hb : atS.get? t = some b) (k r i : ℕ)
    (hW : WeightsAre b.F k r (n q k) (w q k r)) :
    (worldAt ρ b.L b.F y).entry k r i = entBy ρ n w q y k r i := by
  obtain ⟨_, _, u, b', hu, hb', g⟩ := hf
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  rw [worldAt_readsRow ρ b.L b.F y k r i, hW.1]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hW.2 j (Finset.mem_range.1 hj)]
  simp only [entUnit, hu, cellsOf, g.2.2.2.1]

/-- **hFu FROM TWO CLAUSES, THE GENERAL FORM**: the weights of each named row are fixed by q. -/
theorem hFu_by (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (Named : α × Option Pub9 → Ent → Prop) (Un : α × Option Pub9 → ℕ → ℕ → Prop)
    (n : α × Option Pub9 → ℕ → ℕ) (w : α × Option Pub9 → ℕ → ℕ → ℕ → E)
    (h1 : ∀ q x, Ok q → Named q x → Un q x.tree x.row)
    (h2 : ∀ q t b, Fx9 φ Ok q t → Fu t → atS.get? t = some b → ∀ k r, Un q k r →
      WeightsAre b.F k r (n q k) (w q k r))
    (q : α × Option Pub9) (t : S) (b : K9.Part) (y : Bound K) (hf : Fx9 φ Ok q t) (hfu : Fu t)
    (hb : atS.get? t = some b) (x : Ent) (hx : Named q x) :
    (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = entBy ρ n w q y x.tree x.row x.idx :=
  entry_by ρ φ Ok n w q t b y hf hb x.tree x.row x.idx
    (h2 q t b hf hfu hb x.tree x.row (h1 q x hf.1 hx))

end VerifiableInference.Desc.EntryUnit

#print axioms VerifiableInference.Desc.EntryUnit.unitAt_of_row
#print axioms VerifiableInference.Desc.EntryUnit.entry_unit
#print axioms VerifiableInference.Desc.EntryUnit.entry_fixed
#print axioms VerifiableInference.Desc.EntryUnit.hFu_of
#print axioms VerifiableInference.Desc.EntryUnit.entBy_unit
#print axioms VerifiableInference.Desc.EntryUnit.entBy_zero
#print axioms VerifiableInference.Desc.EntryUnit.entry_by
#print axioms VerifiableInference.Desc.EntryUnit.hFu_by
