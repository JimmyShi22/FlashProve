-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EntryTrue.lean: the true value of each entry of the reads of a layers' sub-proof, as
a function of the matrices, written out; and that in every world with these entries every table of
the reads holds what it says.

The statement of K4's row reads the entries of the reads "as true, not as committed": it has a
letter for the true value of an entry. Here is a definition to fill that letter with.

Main names:
  `entryOf ρ tl funs iU3 K3 M`: at the array iU3, row r, entry i: if the smallness test's numbers tl
    have the place r K3 + i for a column and a run of a table of the list funs, that table's sum
    over the run of the column's entries in M under the table's weights (saysOf,
    Johnson/Road/FormsKeysMet.lean); 0 elsewhere. It is the entry of the world that
    holds_of_apart (in that file) makes, given a name.
  `holds_entryOf`: if no place is owned twice (Apart), then in every world whose entries are
    entryOf's, every table of the list holds what it says of M (Holds,
    Johnson/Road/FormsKeysMat.lean).
  `entryTrue tl o M`: entryOf at the reading gl and at what a hearing of K4's text returned: its
    list of tables o.funs and its environment's array and number of columns.
  `reads_true_pub`: at a public record Pub34: ReadsTrue in every world whose entries are entryOf's
    at the record's own letters.
  `reads_true`: at a record that is tied to a hearing's return o (its reading, its list of tables,
    its environment): ReadsTrue in the world of every ledger and every mask row with the entries
    entryTrue X.tl o M.
Limits. TRUE BY MAKE: the entries are chosen so; what is shown is that the choice is free of
clashes (apart_of_run: the tables lie one behind the other). At a place that no table of
the list owns the entry is 0: a filling, true of nothing; it does no harm only as far as no form
names such a place (Johnson/Road/K4/Reads/Covered.lean speaks of that, under premises of its own).
Nothing ties these entries to what a prover has committed: that is another row's matter. Nothing on
a draw, on soundness or on hiding.


-/
import Johnson.Road.FormsKeysMet
import Johnson.Road.Rows.LayerEnds34
import OnBytes.Desc.First.P1.RoundRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World Fork HFun HTailF2)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.P1 (gl)

variable {K : Type} [Field K]

open Classical in
/-- The true value of entry i of row r of array a. -/
noncomputable def entryOf (ρ : Reading K) (tl : HTailF2) (funs : Array HFun) (iU3 K3 : ℕ)
    (M : Mats K) : ℕ → ℕ → ℕ → K := fun a r i =>
  if a = iU3 then
    (if h : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧ tl.tabAt x.1 x.2.1 x.2.2 = some (r * K3 + i)
     then saysOf ρ M h.choose.1 h.choose.2.1 h.choose.2.2 else 0)
  else 0

/-- In every world with these entries every table holds what it says. -/
theorem holds_entryOf (ρ : Reading K) {tl : HTailF2} {funs : Array HFun} (hA : Apart tl funs)
    (iU3 K3 : ℕ) (M : Mats K) {W : World K} (hW : W.entry = entryOf ρ tl funs iU3 K3 M) :
    ∀ Fn ∈ funs, Holds ρ W tl iU3 K3 M Fn := by
  classical
  intro Fn hF c sg pos hpos
  rw [hW]
  show (if iU3 = iU3 then
    (if h : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧
        tl.tabAt x.1 x.2.1 x.2.2 = some (pos / K3 * K3 + pos % K3)
     then saysOf ρ M h.choose.1 h.choose.2.1 h.choose.2.2 else 0) else 0) = saysOf ρ M Fn c sg
  rw [if_pos rfl, Nat.div_add_mod']
  have hex : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧ tl.tabAt x.1 x.2.1 x.2.2 = some pos :=
    ⟨(Fn, c, sg), hF, hpos⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  obtain ⟨e1, e2, e3⟩ := hA _ h1 _ hF _ _ _ _ _ h2 hpos
  rw [e1, e2, e3]

/-- **ReadsTrue at a public record, in every world with the true entries.** -/
theorem reads_true_pub (X : Rows.Pub34 K) (M : Mats K) {W : World K}
    (hW : W.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 M) : X.ReadsTrue W M := by
  have hl := X.hl
  rw [← X.htm] at hl
  exact holds_entryOf X.ρ (apart_of_run hl X.hfun X.hNM) _ _ M hW

/-- The true entries at what a hearing of K4's text returned. -/
noncomputable def entryTrue (tl : HTailF2) (o : Own) (M : Mats Cb.Gl.E) : ℕ → ℕ → ℕ → Cb.Gl.E :=
  entryOf gl tl o.funs o.v.iU3 o.v.K3 M

/-- **ReadsTrue at a hearing, in the world of every ledger and every mask row.** -/
theorem reads_true (X : Rows.Pub34 Cb.Gl.E) {o : Own} (Xρ : X.ρ = gl) (Xf : X.funs = o.funs)
    (Xv : X.p.v = o.v) (M : Mats Cb.Gl.E) (Fl : Fork) (mask : ℕ → Cb.Gl.E) :
    X.ReadsTrue (Fl.worldOf gl mask (entryTrue X.tl o M)) M :=
  reads_true_pub X M (by
    rw [Xρ, Xf, Xv]
    rfl)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.holds_entryOf
#print axioms OnBytes.Road.K4.reads_true_pub
#print axioms OnBytes.Road.K4.reads_true
