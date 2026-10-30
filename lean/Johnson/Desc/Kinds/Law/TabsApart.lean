-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TabsApart.lean.
WHAT IT DOES NOT SHOW. No soundness. Numbers of entries alone: nothing on what an entry is worth.
Nothing on the list of the smallness test's tables (funs): the rows of the table of tables (tab)
alone. That the tables are made: a premise (a yes of the text that makes them).
LETTERS. No "there is".
OBJECT. The table of tables (name; first entry; length) that the description's text makes for the
output head's vector of reads (Desc/K8/ReadsQuiet.lean: tables).
USER. Whoever finds a table by a COLUMN of the reads' array and must know that it is the table found
by its name.
WHAT IT IS. NO ENTRY OF THE VECTOR OF READS LIES IN TWO TABLES' STRETCHES: each table begins where
the vector ended when it was added, and every earlier table ends at or below that entry.
StretchesApart t two rows of t.tab whose stretches share an entry are one row.
  apart_add         adding a table at the vector's end keeps it: over the record WfT
                    (Johnson/Road/HeadReads.lean: no table is empty, each ends inside the vector, no
                    two begin at one entry), whose clause "ends" is what is spent.
  wf_step, wf_fold  one ask, and a list of asks, keep WfT and StretchesApart (WfT by
                    wfT_add).
  tables_apart      after a yes of the head's tables: WfT and StretchesApart.
A search (names with apart, disjoint, overlap, pairwise; statements with two
members of a .tab; over this library and other files of this project, in another version:
some 7,200 files): WfT says less (two tables with different first entries may overlap under it); the
layers' and attention's like laws (k4_tables_apart, tiles_apart) speak of other lists.

-/
import Mathlib
import Johnson.Road.HeadReads
import Johnson.Desc.Kinds.Law.HeadTabsBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model Fo
open OnBytes.Road.Hd (WfT wfT_empty wfT_add)
open VerifiableInference.Desc.K8

/-- Two rows whose stretches share an entry are one row. -/
def StretchesApart (t : Model.Head.Tables) : Prop :=
  ∀ x ∈ t.tab, ∀ y ∈ t.tab, ∀ pos, x.2.1 ≤ pos → pos < x.2.1 + x.2.2 → y.2.1 ≤ pos →
    pos < y.2.1 + y.2.2 → x = y

/-- Adding a table at the vector's end keeps it. -/
theorem apart_add {t t' : Model.Head.Tables} {nm : String} {len : Nat} (hW : WfT t)
    (hA : StretchesApart t) (ht : t'.tab = t.tab ++ [(nm, t.p, len)]) : StretchesApart t' := by
  have mem : ∀ e, e ∈ t'.tab → e ∈ t.tab ∨ e = (nm, t.p, len) := by
    intro e he
    rw [ht, List.mem_append, List.mem_singleton] at he
    exact he
  intro x hx y hy pos a1 a2 b1 b2
  rcases mem x hx with h1 | h1 <;> rcases mem y hy with h2 | h2
  · exact hA x h1 y h2 pos a1 a2 b1 b2
  · subst h2
    have := (hW.ends x h1).2
    have b1' : t.p ≤ pos := b1
    omega
  · subst h1
    have := (hW.ends y h2).2
    have a1' : t.p ≤ pos := a1
    omega
  · rw [h1, h2]

theorem wf_step {mats : Array TMat} {t t' : Model.Head.Tables} {a : Ask}
    (h : askStep mats t a = some t') (Z : WfT t ∧ StretchesApart t) :
    WfT t' ∧ StretchesApart t' := by
  obtain ⟨e1, _, _⟩ := addFun_ok h
  have hg : t.p < t'.p := step_grows h
  exact ⟨wfT_add Z.1 (by omega) (by omega) e1, apart_add Z.1 Z.2 e1⟩

theorem wf_fold (mats : Array TMat) :
    ∀ (l : List Ask) (t t' : Model.Head.Tables), l.foldlM (askStep mats) t = some t' →
      WfT t ∧ StretchesApart t → WfT t' ∧ StretchesApart t'
  | [], t, t', h, Z => by
    obtain rfl : t = t' := Option.some.inj h
    exact Z
  | a :: l, t, t', h, Z => by
    rw [List.foldlM_cons] at h
    cases h1 : askStep mats t a with
    | none =>
      rw [h1] at h
      exact absurd h (by simp)
    | some t1 =>
      rw [h1] at h
      exact wf_fold mats l t1 t' h (wf_step h1 Z)

/-- **After a yes of the head's tables: no entry lies in two tables' stretches.** -/
theorem tables_apart {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (e : ReadsQuiet.tables h L hp cov x = .ok t) : WfT t ∧ StretchesApart t := by
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, _, _, _, _, _, _, ea⟩ := tables_asks e
  exact wf_fold hp.tl.mats _ {} t ea ⟨wfT_empty, fun _ hx => absurd hx (by simp)⟩

end VerifiableInference.Desc.Kinds.Head.Law
