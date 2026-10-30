-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/UnitsRows.lean.

What is here. The rows of a unit, entry by entry: the honest side's weights and numbers of the rows
with some groups left open (`rowWeights`, `rowNumbers`, Johnson/Desc/K4/Honest/Units.lean) against
the verifier's coefficients on the rows (`gamOf`, Johnson/Road/FormsKeysFac.lean) of the claim in
which each open group bears the factor of one index (`deltaAt`, UnitsDelta.lean).

  `outerAdd_toList`, `outerAdd_size`, `outerAdd_getD`   all sums of two arrays' members
  `rowPart`   the part of a group's index that a row's number holds, by the group's name
  `rwOf`, `rnOf`, `rowWeights_eq`, `rowNumbers_eq'`   the two loops, from the last group on
  `rwOf_size`, `rnOf_size`, `rowPart_lt`   sizes
  `rnOf_at`   **a row's number**
  `gam_at`   **the verifier's coefficient is the honest weight times the open factors' row halves**

Limits. At the reading `Reading.gl`. Every group is asked to meet the library's condition `GrpOK`,
every closed factor to have the sizes that its group asks, and no two groups to have one name. For a
row's number below the number of rows. Nothing on the columns or on a matrix.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsDelta
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsRadix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE mulE)
open OnBytes.Model (Reading WsUnit WsGrp WsFac wsOuter wsDigits)
open OnBytes.Road (GrpOK gamOf gamOf_size wsOuter_size wsOuter_getD table_size table_at rowHalf
  flatMap_length flatMap_getElem?)
open OnBytes.Desc.First.K4.Honest (grpIndex strideOf rowWeights rowNumbers outerAdd)

/-! ## 1 All sums of two arrays' members -/

/-- Pushing f of each member of a list onto an array. -/
theorem push_foldN (f : ℕ → ℕ) : ∀ (l : List ℕ) (out : Array ℕ),
    (l.foldl (fun o y => o.push (f y)) out).toList = out.toList ++ l.map f
  | [], out => by simp
  | y :: l, out => by
    rw [List.foldl_cons, push_foldN f l]
    simp

/-- All sums of a member of a and a member of b, as a list: a's members outside, b's inside. -/
theorem outerAdd_toList (a b : Array ℕ) :
    (outerAdd a b).toList = a.toList.flatMap fun x => b.toList.map fun y => x + y := by
  have H : ∀ (l : List ℕ) (out : Array ℕ),
      (l.foldl (fun out x => b.foldl (fun o y => o.push (x + y)) out) out).toList =
        out.toList ++ l.flatMap fun x => b.toList.map fun y => x + y := by
    intro l
    induction l with
    | nil =>
      intro out
      simp
    | cons x l ih =>
      intro out
      rw [List.foldl_cons, ih, ← Array.foldl_toList, push_foldN, List.flatMap_cons,
        List.append_assoc]
  unfold outerAdd
  rw [← Array.foldl_toList, H]
  simp

/-- There are as many sums as pairs. -/
theorem outerAdd_size (a b : Array ℕ) : (outerAdd a b).size = a.size * b.size := by
  have h := flatMap_length (fun x => b.toList.map fun y => x + y) b.size a.toList
    (by intro x _; simp)
  rw [← outerAdd_toList] at h
  simpa using h

/-- The sum at place i times b's size plus q is a's member i plus b's member q. -/
theorem outerAdd_getD (a b : Array ℕ) {i q : ℕ} (hi : i < a.size) (hq : q < b.size) :
    (outerAdd a b).getD (i * b.size + q) 0 = a.getD i 0 + b.getD q 0 := by
  have h2 := flatMap_getElem? (fun x => b.toList.map fun y => x + y) b.size a.toList
    (by intro x _; simp) i q (a.getD i 0) (by simp [Array.getD, hi]) hq
  rw [← outerAdd_toList] at h2
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h2]
  simp [Array.getD, hq]

/-! ## 2 The two loops, from the last group on -/

variable (st : List (String × ℕ))

/-- What one group gives the rows' weights. -/
def tabO (y : WsFac × WsGrp) : Array E :=
  match strideOf st y.2 with
  | none => (y.1.onRows y.2).table y.2
  | some _ => Array.replicate y.2.left oneE

/-- What one group gives the rows' numbers. -/
def numO (y : WsFac × WsGrp) : Array ℕ :=
  match strideOf st y.2 with
  | none => Array.replicate y.2.left 0
  | some s => (Array.range y.2.left).map fun rho => s * grpIndex y.2 0 rho

/-- The rows' weights: for the last pair first. -/
def rwOf (l : List (WsFac × WsGrp)) (d : Array E) : Array E :=
  l.foldr (fun y v => wsOuter v (tabO st y)) d

/-- The rows' numbers: likewise. -/
def rnOf (l : List (WsFac × WsGrp)) (e : Array ℕ) : Array ℕ :=
  l.foldr (fun y v => outerAdd v (numO st y)) e

/-- The honest side's loop for a unit's row weights, from the last group on. -/
theorem rowWeights_eq (u : WsUnit) (fs : List (WsFac × WsGrp)) :
    rowWeights u fs st = rwOf st fs (wsDigits u.nlw oneE).toArray := by
  unfold rowWeights rwOf
  rw [List.foldl_reverse]
  rfl

/-- The honest side's loop for a unit's row numbers, from the last group on. -/
theorem rowNumbers_eq' (u : WsUnit) (fs : List (WsFac × WsGrp)) :
    rowNumbers u fs st = rnOf st fs (Array.replicate u.nlw 0) := by
  unfold rowNumbers rnOf
  rw [List.foldl_reverse]
  rfl

/-- Every group meets the library's condition, and every closed factor fits its group. -/
def RowsOK (l : List (WsFac × WsGrp)) : Prop :=
  ∀ y ∈ l, GrpOK y.2 ∧ (strideOf st y.2 = none → y.1.fits y.2 = true)

variable {st}

/-- One group's array of weights has as many members as the group has values on the left. -/
theorem tabO_size {y : WsFac × WsGrp} (hg : GrpOK y.2)
    (hf : strideOf st y.2 = none → y.1.fits y.2 = true) : (tabO st y).size = y.2.left := by
  unfold tabO
  cases hs : strideOf st y.2 with
  | none => exact table_size hg (hf hs)
  | some s => exact Array.size_replicate

/-- So has its array of numbers. -/
theorem numO_size (y : WsFac × WsGrp) : (numO st y).size = y.2.left := by
  unfold numO
  cases strideOf st y.2 with
  | none => exact Array.size_replicate
  | some s => simp

/-- The size of the row weights: the start's size times the product of the groups' values. -/
theorem rwOf_size : ∀ (l : List (WsFac × WsGrp)), RowsOK st l → ∀ d : Array E,
    (rwOf st l d).size = d.size * (l.map (·.2.left)).prod
  | [], _, d => by simp [rwOf]
  | y :: rest, hok, d => by
    obtain ⟨hg, hf⟩ := hok y List.mem_cons_self
    show (wsOuter (rwOf st rest d) (tabO st y)).size = _
    rw [wsOuter_size, tabO_size hg hf,
      rwOf_size rest (fun z hz => hok z (List.mem_cons_of_mem _ hz)) d, List.map_cons,
      List.prod_cons]
    ring

/-- The size of the row numbers: the same product. -/
theorem rnOf_size : ∀ (l : List (WsFac × WsGrp)) (e : Array ℕ),
    (rnOf st l e).size = e.size * (l.map (·.2.left)).prod
  | [], e => by simp [rnOf]
  | y :: rest, e => by
    show (outerAdd (rnOf st rest e) (numO st y)).size = _
    rw [outerAdd_size, numO_size, rnOf_size rest e, List.map_cons, List.prod_cons]
    ring

/-! ## 3 A row's number, cut -/

/-- **The part of a group's index that the row number j holds**, by the group's name: the first
group's part is the least significant place. -/
def rowPart : List (WsFac × WsGrp) → ℕ → String → ℕ
  | [], _, _ => 0
  | y :: rest, j, n => if n = y.2.name then j % y.2.left else rowPart rest (j / y.2.left) n

/-- At a later group's name the first group does not count. -/
theorem rowPart_cons {y z : WsFac × WsGrp} (rest : List (WsFac × WsGrp)) (j : ℕ)
    (h : z.2.name ≠ y.2.name) :
    rowPart (y :: rest) j z.2.name = rowPart rest (j / y.2.left) z.2.name := by
  show (if z.2.name = y.2.name then _ else _) = _
  rw [if_neg h]

/-- A row's number, cut at the first group. -/
theorem cut_lt {j a b : ℕ} (h : j < a * b) : j / b < a ∧ j % b < b ∧ j / b * b + j % b = j := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with e | e
    · rw [e, Nat.mul_zero] at h
      omega
    · exact e
  exact ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h), Nat.mod_lt _ hb,
    Nat.div_add_mod' j b⟩

/-- A row's part for a group of the list lies below the group's number of values. -/
theorem rowPart_lt : ∀ (l : List (WsFac × WsGrp)) (m j : ℕ), j < m * (l.map (·.2.left)).prod →
    (l.map (·.2.name)).Nodup → ∀ y ∈ l, rowPart l j y.2.name < y.2.left
  | [], _, _, _, _ => fun _ hy => absurd hy List.not_mem_nil
  | x :: rest, m, j, hj, hd => by
    rw [List.map_cons, List.prod_cons, ← Nat.mul_assoc, Nat.mul_right_comm] at hj
    rw [List.map_cons, List.nodup_cons] at hd
    obtain ⟨c1, c2, _⟩ := cut_lt hj
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · show (if y.2.name = y.2.name then _ else _) < _
      rw [if_pos rfl]
      exact c2
    · rw [rowPart_cons rest j fun e => hd.1 (by rw [← e]; exact List.mem_map_of_mem hy')]
      exact rowPart_lt rest m _ c1 hd.2 y hy'

/-- **A ROW's NUMBER**: the sum, over the open groups, of the stride times the index that the row's
part makes alone. -/
theorem rnOf_at : ∀ (l : List (WsFac × WsGrp)) (m j : ℕ), j < m * (l.map (·.2.left)).prod →
    (l.map (·.2.name)).Nodup →
    (rnOf st l (Array.replicate m 0)).getD j 0 = (l.map fun y => match strideOf st y.2 with
      | none => 0
      | some s => s * grpIndex y.2 0 (rowPart l j y.2.name)).sum
  | [], m, j, _, _ => by
    show (Array.replicate m 0).getD j 0 = 0
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  | x :: rest, m, j, hj, hd => by
    rw [List.map_cons, List.prod_cons, ← Nat.mul_assoc, Nat.mul_right_comm] at hj
    rw [List.map_cons, List.nodup_cons] at hd
    obtain ⟨c1, c2, c3⟩ := cut_lt hj
    have hs1 : j / x.2.left < (rnOf st rest (Array.replicate m 0)).size := by
      rw [rnOf_size, Array.size_replicate]
      exact c1
    have hs2 : j % x.2.left < (numO st x).size := by
      rw [numO_size]
      exact c2
    have e := outerAdd_getD (rnOf st rest (Array.replicate m 0)) (numO st x) hs1 hs2
    rw [numO_size, c3] at e
    show (outerAdd (rnOf st rest (Array.replicate m 0)) (numO st x)).getD j 0 = _
    rw [e, rnOf_at rest m _ c1 hd.2, List.map_cons, List.sum_cons, Nat.add_comm]
    congr 1
    · show _ = match strideOf st x.2 with
        | none => 0
        | some s => s * grpIndex x.2 0 (if x.2.name = x.2.name then j % x.2.left else _)
      rw [if_pos rfl]
      unfold numO
      cases strideOf st x.2 with
      | none =>
        show (Array.replicate x.2.left 0).getD (j % x.2.left) 0 = 0
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
        split <;> rfl
      | some s => exact getD_range_map _ _ _ c2 0
    · congr 1
      refine List.map_congr_left fun y hy => ?_
      rw [rowPart_cons rest j fun e => hd.1 (by rw [← e]; exact List.mem_map_of_mem hy)]

/-! ## 4 The verifier's coefficient -/

/-- The pick of an index in each open group: tv, by the group's name. -/
def selSt (st : List (String × ℕ)) (tv : String → ℕ) (g : WsGrp) : Option ℕ :=
  (strideOf st g).map fun _ => tv g.name

/-- A group without a stride is not selected. -/
theorem selSt_none {tv : String → ℕ} {g : WsGrp} (h : strideOf st g = none) :
    selSt st tv g = none := by
  unfold selSt
  rw [h]
  rfl

/-- A group with a stride is selected at the value that tv gives its name. -/
theorem selSt_some {tv : String → ℕ} {g : WsGrp} {s : ℕ} (h : strideOf st g = some s) :
    selSt st tv g = some (tv g.name) := by
  unfold selSt
  rw [h]
  rfl

/-- The factor that a group bears fits the group. -/
theorem pick_fits (tv : String → ℕ) {y : WsFac × WsGrp}
    (hf : strideOf st y.2 = none → y.1.fits y.2 = true) :
    (pickFac (selSt st tv) y).fits y.2 = true := by
  cases hs : strideOf st y.2 with
  | none =>
    rw [pickFac_none (selSt_none hs)]
    exact hf hs
  | some s =>
    rw [pickFac_some (selSt_some hs)]
    exact deltaFac_fits _ _

/-- The list with the selected groups' factors replaced by indicators is fit as the list was. -/
theorem delta_ok (tv : String → ℕ) {l : List (WsFac × WsGrp)} (hok : RowsOK st l) :
    ∀ y ∈ deltaAt (selSt st tv) l, GrpOK y.2 ∧ y.1.fits y.2 = true := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  exact ⟨(hok z hz).1, pick_fits tv (hok z hz).2⟩

/-- Replacing factors does not change the product of the groups' numbers of values. -/
theorem delta_left (sel : WsGrp → Option ℕ) (l : List (WsFac × WsGrp)) :
    ((deltaAt sel l).map (·.2.left)).prod = (l.map (·.2.left)).prod := by
  unfold deltaAt
  rw [List.map_map]
  rfl

/-- The verifier's coefficients, cut at the first group. -/
theorem gamOf_cons_at (x : WsFac) {g : WsGrp} (hg : GrpOK g) (hfit : x.fits g = true)
    (R : List (WsFac × WsGrp)) (d : Array E) {j : ℕ} (hj : j < (gamOf R d).size * g.left) :
    Reading.gl.val ((gamOf ((x, g) :: R) d).getD j zeroE) =
      Reading.gl.val ((gamOf R d).getD (j / g.left) zeroE) *
        rowHalf Reading.gl x g (j % g.left) := by
  obtain ⟨c1, c2, c3⟩ := cut_lt hj
  have g2 := table_size hg hfit
  have e := wsOuter_getD (gamOf R d) ((x.onRows g).table g) c1
    (show j % g.left < _ by rw [g2]; exact c2)
  rw [g2, c3] at e
  show Reading.gl.val ((wsOuter (gamOf R d) ((x.onRows g).table g)).getD j zeroE) = _
  rw [e, Reading.gl.mul, table_at Reading.gl hg hfit c2]

/-- What one group gives a row's honest weight. -/
theorem tabO_at {y : WsFac × WsGrp} (hg : GrpOK y.2)
    (hf : strideOf st y.2 = none → y.1.fits y.2 = true) {q : ℕ} (hq : q < y.2.left) :
    Reading.gl.val ((tabO st y).getD q zeroE) = match strideOf st y.2 with
      | none => rowHalf Reading.gl y.1 y.2 q
      | some _ => 1 := by
  unfold tabO
  cases hs : strideOf st y.2 with
  | none => exact table_at Reading.gl hg (hf hs) hq
  | some s =>
    show Reading.gl.val ((Array.replicate y.2.left oneE).getD q zeroE) = 1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos hq]
    exact Reading.gl.one

/-- The honest weights, cut at the first group. -/
theorem rwOf_cons_at {y : WsFac × WsGrp} (hg : GrpOK y.2)
    (hf : strideOf st y.2 = none → y.1.fits y.2 = true) (R : List (WsFac × WsGrp)) (d : Array E)
    {j : ℕ} (hj : j < (rwOf st R d).size * y.2.left) :
    Reading.gl.val ((rwOf st (y :: R) d).getD j zeroE) =
      Reading.gl.val ((rwOf st R d).getD (j / y.2.left) zeroE) *
        Reading.gl.val ((tabO st y).getD (j % y.2.left) zeroE) := by
  obtain ⟨c1, c2, c3⟩ := cut_lt hj
  have r2 := tabO_size (st := st) hg hf
  have e := wsOuter_getD (rwOf st R d) (tabO st y) c1 (show j % y.2.left < _ by rw [r2]; exact c2)
  rw [r2, c3] at e
  show Reading.gl.val ((wsOuter (rwOf st R d) (tabO st y)).getD j zeroE) = _
  rw [e, Reading.gl.mul]

/-- What an open group's factor of one index weighs a row's part with; 1 for a closed group. -/
def rowPick (st : List (String × ℕ)) (tv : String → ℕ) (rp : String → ℕ) (y : WsFac × WsGrp) :
    Cb.Gl.E :=
  match strideOf st y.2 with
  | none => 1
  | some _ => rowHalf Reading.gl (deltaFac y.2 (tv y.2.name)) y.2 (rp y.2.name)

/-- One group's step. -/
theorem pick_step (tv : String → ℕ) {y : WsFac × WsGrp} (hg : GrpOK y.2)
    (hf : strideOf st y.2 = none → y.1.fits y.2 = true) (rp : String → ℕ)
    (hq : rp y.2.name < y.2.left) :
    rowHalf Reading.gl (pickFac (selSt st tv) y) y.2 (rp y.2.name) =
      Reading.gl.val ((tabO st y).getD (rp y.2.name) zeroE) * rowPick st tv rp y := by
  rw [tabO_at hg hf hq]
  unfold rowPick
  cases hs : strideOf st y.2 with
  | none =>
    rw [pickFac_none (selSt_none hs)]
    exact (mul_one _).symm
  | some s =>
    rw [pickFac_some (selSt_some hs)]
    exact (one_mul _).symm

/-- **THE VERIFIER's COEFFICIENT ON A ROW**, for the claim in which each open group bears the factor
of the one index tv: the honest weight of the row times the product, over the open groups, of that
factor's row half at the row's part. -/
theorem gam_at (tv : String → ℕ) (d : Array E) : ∀ (l : List (WsFac × WsGrp)), RowsOK st l →
    (l.map (·.2.name)).Nodup → ∀ j : ℕ, j < d.size * (l.map (·.2.left)).prod →
    Reading.gl.val ((gamOf (deltaAt (selSt st tv) l) d).getD j zeroE) =
      Reading.gl.val ((rwOf st l d).getD j zeroE) * (l.map (rowPick st tv (rowPart l j))).prod := by
  intro l
  induction l with
  | nil =>
    intro _ _ j _
    show Reading.gl.val (d.getD j zeroE) = Reading.gl.val (d.getD j zeroE) * 1
    rw [mul_one]
  | cons x rest ih =>
    intro hok hd j hj
    obtain ⟨hg, hf⟩ := hok x List.mem_cons_self
    have hok' : RowsOK st rest := fun z hz => hok z (List.mem_cons_of_mem _ hz)
    rw [List.map_cons, List.prod_cons, ← Nat.mul_assoc, Nat.mul_right_comm] at hj
    rw [List.map_cons, List.nodup_cons] at hd
    obtain ⟨c1, c2, _⟩ := cut_lt hj
    have eH : rowPart (x :: rest) j x.2.name = j % x.2.left := by
      show (if x.2.name = x.2.name then _ else _) = _
      rw [if_pos rfl]
    have eT : rest.map (rowPick st tv (rowPart (x :: rest) j)) =
        rest.map (rowPick st tv (rowPart rest (j / x.2.left))) := by
      refine List.map_congr_left fun y hy => ?_
      unfold rowPick
      rw [rowPart_cons rest j fun e => hd.1 (by rw [← e]; exact List.mem_map_of_mem hy)]
    have hstep := pick_step tv hg hf (rowPart (x :: rest) j) (by rw [eH]; exact c2)
    rw [eH] at hstep
    rw [deltaAt_cons,
      gamOf_cons_at _ hg (pick_fits tv hf) _ d
        (by rw [gamOf_size _ (delta_ok tv hok'), delta_left]; exact hj),
      rwOf_cons_at hg hf rest d (by rw [rwOf_size rest hok']; exact hj),
      ih hok' hd.2 _ c1, hstep, List.map_cons, List.prod_cons, eT]
    ring

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.push_foldN
#print axioms ProofFile.Honest.K4.outerAdd_toList
#print axioms ProofFile.Honest.K4.outerAdd_size
#print axioms ProofFile.Honest.K4.outerAdd_getD
#print axioms ProofFile.Honest.K4.rowWeights_eq
#print axioms ProofFile.Honest.K4.rowNumbers_eq'
#print axioms ProofFile.Honest.K4.tabO_size
#print axioms ProofFile.Honest.K4.numO_size
#print axioms ProofFile.Honest.K4.rwOf_size
#print axioms ProofFile.Honest.K4.rnOf_size
#print axioms ProofFile.Honest.K4.rowPart_cons
#print axioms ProofFile.Honest.K4.cut_lt
#print axioms ProofFile.Honest.K4.rowPart_lt
#print axioms ProofFile.Honest.K4.rnOf_at
#print axioms ProofFile.Honest.K4.selSt_none
#print axioms ProofFile.Honest.K4.selSt_some
#print axioms ProofFile.Honest.K4.pick_fits
#print axioms ProofFile.Honest.K4.delta_ok
#print axioms ProofFile.Honest.K4.delta_left
#print axioms ProofFile.Honest.K4.gamOf_cons_at
#print axioms ProofFile.Honest.K4.tabO_at
#print axioms ProofFile.Honest.K4.rwOf_cons_at
#print axioms ProofFile.Honest.K4.pick_step
#print axioms ProofFile.Honest.K4.gam_at
