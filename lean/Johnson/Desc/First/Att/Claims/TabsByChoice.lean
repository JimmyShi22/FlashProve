-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/TabsByChoice.lean: "every table of the list is true of the matrices"
(`Holds`, Johnson/Road/FormsKeysMat.lean) can be had by the choice of the entries: where no two
tables of a list name one position, there is ONE assignment of values to the entries of the vector
of tables at which every table of the list holds, whatever the matrices are.

Why: kind K5's law asks of the relation behind the kind that there are entries and matrices at which
the gathered forms are worth 0 and the tables are true (`AttAt`, Johnson/Road/Rows/AttRead.lean).
Whoever pays that premise picks the entries. A sentence "the forms are worth 0 with each entry read
as the stated function of the cells" picks them so.

Main names:
  `Apart tl funs`: two tables of the list that name one position, each at a column and a run, are
    one table, at one column and one run.
  `sumAt`: the weighted sum that `Holds` asks under a table, a column and a run.
  `entryOf ρ tl K3 M funs`: row r, place i: the sum of a table, column and run of the list whose
    position pos has pos / K3 = r and pos % K3 = i, if there is one; else 0. The array's number is
    not read.
  `holds_entryOf`: Apart tl funs → every table of the list holds at `entryOf`, in the world of any
    ledger and mask, at every K3.
  `not_both`: a control: two tables at one position whose sums differ hold together at no world.
Used: plain records and functions of OnBytes/Model; Classical.choice picks the table.
Limits: `Apart` is shown of no list in this file. Nothing is said on whether the forms are worth 0
at these entries, nor on what the committed array holds: that the committed entries ARE these sums
is the reads' truth, which is not touched here.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.FormsKeysMat

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road Finset

variable {K : Type} [Field K]

/-- Two tables of the list that name one position are one, at one column and one run. -/
def Apart (tl : HTailF2) (funs : List HFun) : Prop :=
  ∀ Fn ∈ funs, ∀ Fn' ∈ funs, ∀ c sg c' sg' pos, tl.tabAt Fn c sg = some pos →
    tl.tabAt Fn' c' sg' = some pos → Fn = Fn' ∧ c = c' ∧ sg = sg'

/-- The sum that `Holds` asks under table x.1, column x.2.1, run x.2.2. -/
def sumAt (ρ : Reading K) (M : Mats K) (x : HFun × ℕ × ℕ) : K :=
  ∑ j ∈ range x.1.len, ρ.val (x.1.phi.getD j zeroE) * M x.1.mat (x.2.2 * x.1.len + j) x.2.1

/-- Table, column and run x of the list lies at row r, place i. -/
def LiesAt (tl : HTailF2) (K3 : ℕ) (funs : List HFun) (r i : ℕ) (x : HFun × ℕ × ℕ) : Prop :=
  x.1 ∈ funs ∧ ∃ pos, tl.tabAt x.1 x.2.1 x.2.2 = some pos ∧ r = pos / K3 ∧ i = pos % K3

open Classical in
/-- **The entries, chosen**: each is the stated sum of the table that lies there. -/
noncomputable def entryOf (ρ : Reading K) (tl : HTailF2) (K3 : ℕ) (M : Mats K) (funs : List HFun) :
    ℕ → ℕ → ℕ → K := fun _ r i =>
  if h : ∃ x, LiesAt tl K3 funs r i x then sumAt ρ M h.choose else 0

/-- **At the chosen entries every table of the list holds.** -/
theorem holds_entryOf (ρ : Reading K) (tl : HTailF2) (iU3 K3 : ℕ) (M : Mats K) (funs : List HFun)
    (hA : Apart tl funs) (F : Fork) (mask : ℕ → K) :
    ∀ Fn ∈ funs, Holds ρ (F.worldOf ρ mask (entryOf ρ tl K3 M funs)) tl iU3 K3 M Fn := by
  intro Fn hFn c sg pos hpos
  show entryOf ρ tl K3 M funs iU3 (pos / K3) (pos % K3) = _
  have hex : ∃ x, LiesAt tl K3 funs (pos / K3) (pos % K3) x :=
    ⟨(Fn, c, sg), hFn, pos, hpos, rfl, rfl⟩
  unfold entryOf
  rw [dif_pos hex]
  obtain ⟨h1, pos', h2, h3, h4⟩ := hex.choose_spec
  have e : pos' = pos := by
    have a := Nat.div_add_mod pos K3
    have b := Nat.div_add_mod pos' K3
    rw [← h3, ← h4] at b
    omega
  rw [e] at h2
  obtain ⟨e1, e2, e3⟩ := hA _ h1 _ hFn _ _ _ _ _ h2 hpos
  unfold sumAt
  rw [e1, e2, e3]

/-- A control: two tables at one position whose sums differ hold together at no world. -/
theorem not_both (ρ : Reading K) (W : World K) (tl : HTailF2) (iU3 K3 : ℕ) (M : Mats K)
    (Fn Fn' : HFun) (c sg c' sg' pos : ℕ) (h : tl.tabAt Fn c sg = some pos)
    (h' : tl.tabAt Fn' c' sg' = some pos) (hne : sumAt ρ M (Fn, c, sg) ≠ sumAt ρ M (Fn', c', sg')) :
    ¬ (Holds ρ W tl iU3 K3 M Fn ∧ Holds ρ W tl iU3 K3 M Fn') := by
  rintro ⟨a, b⟩
  exact hne ((a c sg pos h).symm.trans (b c' sg' pos h'))

end K5Law

#print axioms K5Law.holds_entryOf
#print axioms K5Law.not_both
