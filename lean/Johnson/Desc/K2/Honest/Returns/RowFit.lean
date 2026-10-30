-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/RowFit.lean: THE GROUND's TEST ON A NEW OPEN ROW (`rowL`,
Johnson/Desc/First/Base/Ground.lean), CUT INTO ITS SEVEN CLAUSES ON THE ROW's MAKE AND ITS ONE ON
VALUES; and how the four clauses on a row's parts go along as a row is built part by part.
Statements and proofs.

  `PartsFit`        the four clauses on terms, single entries, runs and forms, as statements
  `partsFit_empty`, `mem_push`, `PartsFit.add`, `.addForm`, `.addUnit`, `.addRun`, `.dress`, `.aim`
                    the row without parts; one part more; another kind and target; another target
  `PartsFit.restF`, `.restE`   coefficients on the pieces of a stretch of a table
  `makeClauses`, `makeClauses_of`   the seven clauses as one Bool; they hold where the group is
                    there, its test has not begun, the row is no sample row and its parts fit
  `valueClause`, `rowL_cut`   the eighth; `rowL` says yes just where both do

Limits. Nothing on any property.

-/
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.K2.Honest.Returns.Pieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Own.tensorInOrder Own.placeFits Own.coeffsInside Own.formFits
  Own.allZero)
open VerifiableInference.Desc.Ground (rowL ok has)

/-- The four clauses of `rowL` on a row's parts. -/
structure PartsFit (S : Statement) (G : Group) (r : OnBytes.Row) : Prop where
  terms : ∀ t ∈ r.terms.toList,
    Own.tensorInOrder t.v = true ∧ Own.placeFits S G t.oracle t.part t.v.vars 0 = true
  units : ∀ u ∈ r.units.toList,
    Own.placeFits S G u.oracle u.part (S.tableBits u.oracle u.part) u.index = true
  runs : ∀ w ∈ r.runs.toList,
    Own.coeffsInside w.coeffs = true ∧ 0 < w.coeffs.size ∧ 1 ≤ w.step ∧
      Own.placeFits S G w.oracle w.part (S.tableBits w.oracle w.part)
        (w.first + w.step * (w.coeffs.size - 1)) = true
  forms : ∀ f ∈ r.forms.toList,
    Own.placeFits S G f.oracle .main (S.tableBits f.oracle .main) 0 = true ∧
      Own.formFits f.c (S.tableBits f.oracle .main) = true

variable {S : Statement} {G : Group} {r : OnBytes.Row}

theorem partsFit_empty : PartsFit S G {} :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- An entry of an array with one entry more. -/
theorem mem_push {α : Type} {a : Array α} {x y : α} (h : y ∈ (a.push x).toList) :
    y ∈ a.toList ∨ y = x := by
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at h
  exact h

theorem PartsFit.add (h : PartsFit S G r) (o : Nat) (part : Part) (v : Tensor)
    (h1 : Own.tensorInOrder v = true) (h2 : Own.placeFits S G o part v.vars 0 = true) :
    PartsFit S G (r.add o part v) :=
  ⟨fun t ht => by
      rcases mem_push ht with ht | rfl
      · exact h.terms t ht
      · exact ⟨h1, h2⟩,
    h.units, h.runs, h.forms⟩

theorem PartsFit.addForm (h : PartsFit S G r) (o : Nat) (c : Form)
    (h1 : Own.placeFits S G o .main (S.tableBits o .main) 0 = true)
    (h2 : Own.formFits c (S.tableBits o .main) = true) : PartsFit S G (r.addForm o c) :=
  ⟨h.terms, h.units, h.runs, fun f hf => by
      rcases mem_push hf with hf | rfl
      · exact h.forms f hf
      · exact ⟨h1, h2⟩⟩

theorem PartsFit.addUnit (h : PartsFit S G r) (o : Nat) (part : Part) (index : Nat) (x : E)
    (h1 : Own.placeFits S G o part (S.tableBits o part) index = true) :
    PartsFit S G (r.addUnit o part index x) :=
  ⟨h.terms, fun u hu => by
      rcases mem_push hu with hu | rfl
      · exact h.units u hu
      · exact h1,
    h.runs, h.forms⟩

theorem PartsFit.addRun (h : PartsFit S G r) (o : Nat) (part : Part) (first step : Nat)
    (c : Coeffs) (h1 : Own.coeffsInside c = true) (h2 : 0 < c.size) (h3 : 1 ≤ step)
    (h4 : Own.placeFits S G o part (S.tableBits o part) (first + step * (c.size - 1)) = true) :
    PartsFit S G (r.addRun o part first step c) :=
  ⟨h.terms, h.units, fun w hw => by
      rcases mem_push hw with hw | rfl
      · exact h.runs w hw
      · exact ⟨h1, h2, h3, h4⟩,
    h.forms⟩

/-- Another kind and target. -/
theorem PartsFit.dress (h : PartsFit S G r) (k : RowKind) (t : E) :
    PartsFit S G { r with kind := k, target := t } := ⟨h.terms, h.units, h.runs, h.forms⟩

/-- Another target. -/
theorem PartsFit.aim (h : PartsFit S G r) (t : E) : PartsFit S G { r with target := t } :=
  ⟨h.terms, h.units, h.runs, h.forms⟩

/-- Coefficients over the base field on pieces. P: the place of the stretch's entry, by number. -/
theorem PartsFit.restF (g : Nat) (part : Part) (coeff : Array F) (P : Nat → Nat) (n : Nat)
    (hn : n ≤ coeff.size)
    (hP : ∀ i, i < n → Own.placeFits S G g part (S.tableBits g part) (P i) = true) :
    ∀ (l : List SwitchPiece) (r : OnBytes.Row), PartsFit S G r → (∀ p ∈ l, PieceFits P n p) →
      PartsFit S G (switchAddRestF r g part l coeff)
  | [], _, h, _ => h
  | p :: l, r, h, hl => by
    have hp := hl p (List.mem_cons_self ..)
    have a1 := hp.some
    have a2 := hp.inside
    show PartsFit S G (switchAddRestF
      (r.addRun g part p.first p.step (.stretch coeff p.start (p.stop - p.start))) g part l coeff)
    refine PartsFit.restF g part coeff P n hn hP l _ (h.addRun _ _ _ _ _ ?_ ?_ hp.step ?_)
      fun q hq => hl q (List.mem_cons_of_mem _ hq)
    · show decide (p.start + (p.stop - p.start) ≤ coeff.size) = true
      exact decide_eq_true (by omega)
    · show 0 < p.stop - p.start
      omega
    · show Own.placeFits S G g part _ (p.first + p.step * (p.stop - p.start - 1)) = true
      rw [hp.last]
      exact hP _ (by omega)

/-- Coefficients over the extension field, written out, on pieces. -/
theorem PartsFit.restE (g : Nat) (part : Part) (coeff : Array E) (P : Nat → Nat)
    (hP : ∀ i, i < coeff.size → Own.placeFits S G g part (S.tableBits g part) (P i) = true) :
    ∀ (l : List SwitchPiece) (r : OnBytes.Row), PartsFit S G r →
      (∀ p ∈ l, PieceFits P coeff.size p) → PartsFit S G (switchAddRestE r g part l coeff)
  | [], _, h, _ => h
  | p :: l, r, h, hl => by
    have hp := hl p (List.mem_cons_self ..)
    have a1 := hp.some
    have a2 := hp.inside
    have hsz : (coeff.extract p.start p.stop).size = p.stop - p.start := by
      rw [Array.size_extract]
      omega
    show PartsFit S G (switchAddRestE
      (r.addRun g part p.first p.step (.own (coeff.extract p.start p.stop))) g part l coeff)
    refine PartsFit.restE g part coeff P hP l _ (h.addRun _ _ _ _ _ rfl ?_ hp.step ?_)
      fun q hq => hl q (List.mem_cons_of_mem _ hq)
    · show 0 < (coeff.extract p.start p.stop).size
      omega
    · show Own.placeFits S G g part _
        (p.first + p.step * ((coeff.extract p.start p.stop).size - 1)) = true
      rw [hsz, hp.last]
      exact hP _ (by omega)

/-- The seven clauses of `rowL` on the row's make, as one Bool. -/
def makeClauses (S : Statement) (grp : Nat) (row : OnBytes.Row) : Bool :=
  ok ((rowL S grp row).take 7)

/-- The eighth, on values. -/
def valueClause (S : Statement) (grp : Nat) (row : OnBytes.Row) : Bool :=
  ok ((rowL S grp row).drop 7)

/-- `rowL` says yes just where both do. -/
theorem rowL_cut (S : Statement) (grp : Nat) (row : OnBytes.Row) :
    ok (rowL S grp row) = (makeClauses S grp row && valueClause S grp row) := by
  unfold makeClauses valueClause ok
  rw [← List.all_append, List.take_append_drop]

/-- **The seven hold** where the group is there, its test has not begun, the row is no sample row
and its parts fit. -/
theorem makeClauses_of {grp : Nat} (hG : S.groups[grp]? = some G) (hrun : G.inRun = false)
    (hk : r.kind ≠ .sample) (h : PartsFit S G r) : makeClauses S grp r = true := by
  have t1 : (r.terms.all fun t =>
      Own.tensorInOrder t.v && Own.placeFits S G t.oracle t.part t.v.vars 0) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro t ht
    obtain ⟨a, b⟩ := h.terms t (Array.mem_toList_iff.2 ht)
    rw [a, b]
    rfl
  have t2 : (r.units.all fun u =>
      Own.placeFits S G u.oracle u.part (S.tableBits u.oracle u.part) u.index) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro u hu
    exact h.units u (Array.mem_toList_iff.2 hu)
  have t3 : (r.runs.all fun w =>
      Own.coeffsInside w.coeffs && decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
        Own.placeFits S G w.oracle w.part (S.tableBits w.oracle w.part)
          (w.first + w.step * (w.coeffs.size - 1))) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro w hw
    obtain ⟨a, b, c, d⟩ := h.runs w (Array.mem_toList_iff.2 hw)
    rw [a, d, decide_eq_true b, decide_eq_true c]
    rfl
  have t4 : (r.forms.all fun f =>
      Own.placeFits S G f.oracle .main (S.tableBits f.oracle .main) 0 &&
        Own.formFits f.c (S.tableBits f.oracle .main)) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro f hf
    obtain ⟨a, b⟩ := h.forms f (Array.mem_toList_iff.2 hf)
    rw [a, b]
    rfl
  have hk' : (r.kind != .sample) = true := by simpa using hk
  unfold makeClauses ok rowL has
  simp only [hG, List.take, List.all_cons, List.all_nil, Option.isSome_some, Option.map_some,
    Option.getD_some, hrun, hk', t1, t2, t3, t4, Bool.not_false, Bool.and_self]

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.makeClauses_of
#print axioms VerifiableInference.Desc.K2.Honest.Returns.rowL_cut
