-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxLens.lean: the lengths in every opening of a chain that the strict reader has
read, and the stored tables' depth: each column has its shape's width; each salt has the length
with which the reader of an opening was called; from the reader's equation
`Fmt.readChainX h S seen b i = some (o, j)`.

Main names (h: any hash; S: any description):
  `lens_of_read`: of one call of the format's reader of an opening.
  `RawAt h S b o y`, `rawAt_of_chain`: every opening of every round as read was returned by one call
    of that reader: a stored table's with the table's own length of salts, from the start
    `S.base.cfg`; a tree's of the chain with the plan's length of salts, from the tree's own start.
  `lens_own`: an opening without the mark "stored": columns of the shape's width, salts of the
    plan's length. `lens_sto`: one with the mark: it has the shape of a stored table t that S lists;
    columns of the shape's width, salts of t's length.
  `stored_same`: of a description D within the limits `XD.ok`: every stored table has the depth
    `D.a` and the plan's length of salts.
  `lens_sto_at`: at a description D whose stored tables are S's and have, each, the depth `D.a` and
    the length of salts of D's plan: an opening with the mark has the depth `D.a`, columns of the
    shape's width, salts of that length.

Hypotheses: the reader's equation; for `lens_sto` and `lens_sto_at`: every tree that S opens is the
chain's own; for `lens_sto_at`: `S.stored = D.stored`, and what `stored_same` concludes of D
(`stored_same` itself has it from `D.ok = true`). Nothing is asked of S's plan.

Limits: values alone. Nothing on roots, on leaves' digests, or on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxReadAs

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice
open _root_.Run (HId)

/-- One call of the format's reader of an opening: the columns' and the salts' lengths. -/
theorem lens_of_read (h : HId) (cfg : ByteArray) (f : Fmt.Fld) (sb : ℕ) (sh : Fmt.Shape)
    (start : ByteArray) (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : Fmt.OpenOut)
    (e : Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i = some o) :
    (∀ c ∈ o.cols, c.length = sh.W) ∧ ∀ sl ∈ o.salts, sl.size = sb := by
  obtain ⟨-, cs, hp, hc, hs⟩ := _root_.Run.PQ.readOpening_some h cfg f sb sh start xs b i o e
  have hall := (_root_.Run.rdOpening_parts f sb sh xs b i cs o.given o.next hp).1
  rw [hc, hs]
  refine ⟨fun c hcm => ?_, fun sl hsm => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hcm
    exact (hall z hz).1
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hsm
    exact (hall z hz).2

/-- An opening as read was returned by one call of the format's reader of an opening. -/
def RawAt (h : HId) (S : Fmt.SpecX) (b : ByteArray) (o : Fmt.ChainOut)
    (y : Fmt.Shape × List ℕ × Fmt.OpenOut) : Prop :=
  (∃ t ∈ S.stored.flatten, y.1 = t.sh ∧ ∃ i, Fmt.readOpeningW (m := Id) h S.base.cfg
    S.base.plan.field t.salt y.1 S.base.cfg y.2.1 b i = some y.2.2) ∨
  ∃ r ∈ S.base.rounds, ∃ x ∈ r.opens, y.1 = x.1 ∧ ∃ start i, startOf o.run x.2 = some start ∧
    Fmt.readOpeningW (m := Id) h S.base.cfg S.base.plan.field S.base.plan.salt y.1 start y.2.1 b
      i = some y.2.2

section
variable {h : HId} {S : Fmt.SpecX} {seen : Fmt.Seen} {b : ByteArray} {i : ℕ} {o : Fmt.ChainOut}
  {j : ℕ} (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))

include e in
/-- Every opening of every round as read. -/
theorem rawAt_of_chain : ∀ r ∈ o.rounds.toList, ∀ y ∈ r.opens, RawAt h S b o y := by
  obtain ⟨hok, -, rc, g1, g2, -, g5⟩ := readX_trace h S seen b i o j e
  have hlen : S.stored.length = S.base.rounds.length := by
    have := hok
    simp only [Fmt.SpecX.ok, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  have hzp : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (by omega)
  have sh1 := List.forall₂_map_right_iff.1 (shapes_of_trace h S.base.plan _ _ _ _ g2)
  rw [← hzp] at sh1
  have all := forall₂_and (List.forall₂_map_left_iff.1 sh1) g5
  intro r hr y hy
  rw [g1] at hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  obtain ⟨x, hx, hs, -, hown, hsto⟩ := forall₂_mem_right all p hp
  have hs' : List.Forall₂ (fun a c => c.1 = a.1) x.1.opens p.1.opens :=
    List.forall₂_map_right_iff.1 hs
  rcases List.mem_append.1 (show y ∈ p.2 ++ p.1.opens from hy) with hy | hy
  · obtain ⟨t, ht, hf, i', hrd⟩ := forall₂_mem_right hsto y hy
    exact .inl ⟨t, List.mem_flatten.2 ⟨x.2, (List.of_mem_zip hx).2, ht⟩, hf.sh, i',
      by rw [hf.sh]; exact hrd⟩
  · obtain ⟨a, ha, hsh, start, i', hst, hrd, -⟩ := forall₂_mem_right (forall₂_and hs' hown) y hy
    exact .inr ⟨x.1, (List.of_mem_zip hx).1, a, ha, hsh, start, i', hst, by rw [hsh]; exact hrd⟩

include e in
/-- An opening without the mark "stored": columns of the shape's width, salts of the plan's
length. -/
theorem lens_own : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
    (∀ c ∈ op.out.cols, c.length = op.sh.W) ∧ ∀ sl ∈ op.out.salts, sl.size = S.base.plan.salt := by
  intro op hop
  obtain ⟨hop, hf⟩ := List.mem_filter.1 hop
  rcases ops1_all (RawAt h S b o) o (rawAt_of_chain e) op hop with
    ⟨t, ht, hs, -⟩ | ⟨-, -, -, -, -, start, i', -, hrd⟩
  · have hS := (readX_trace h S seen b i o j e).1
    have hs' : op.sh = t.sh := hs
    rw [hs', (specX_shape S hS t ht).1] at hf
    cases hf
  · exact lens_of_read h _ _ _ _ _ _ _ _ _ hrd

include e in
/-- An opening with the mark "stored": the shape of a stored table that S lists; columns of the
shape's width, salts of that table's length. -/
theorem lens_sto (hown : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n) :
    ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored), ∃ t ∈ S.stored.flatten, op.sh = t.sh ∧
      (∀ c ∈ op.out.cols, c.length = op.sh.W) ∧ ∀ sl ∈ op.out.salts, sl.size = t.salt := by
  intro op hop
  obtain ⟨hop, hf⟩ := List.mem_filter.1 hop
  rcases ops1_all (RawAt h S b o) o (rawAt_of_chain e) op hop with
    ⟨t, ht, hs, i', hrd⟩ | ⟨r, hr, x, hx, hs, -⟩
  · exact ⟨t, ht, hs, lens_of_read h _ _ _ _ _ _ _ _ _ hrd⟩
  · have hS := (readX_trace h S seen b i o j e).1
    have hs' : op.sh = x.1 := hs
    rw [hs', own_unmarked hS r hr x hx (hown r hr x hx)] at hf
    cases hf

end

/-- Of a description within the limits: every stored table has the depth `D.a` and the plan's
length of salts. -/
theorem stored_same {D : TypedOracleCompiler.Run.PQ.XD} (hD : D.ok = true) :
    ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt := by
  intro t ht
  simp only [TypedOracleCompiler.Run.PQ.XD.ok, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hD
  exact ⟨(hD.2 t ht).1.1, (hD.2 t ht).1.2⟩

/-- At a description D whose stored tables are S's and have the depth `D.a` and the length of salts
of D's plan: an opening with the mark "stored" has the depth `D.a`, columns of its shape's width,
salts of that length. -/
theorem lens_sto_at {h : HId} {S : Fmt.SpecX} {seen : Fmt.Seen} {b : ByteArray} {i : ℕ}
    {o : Fmt.ChainOut} {j : ℕ} (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))
    (hown : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    {D : TypedOracleCompiler.Run.PQ.XD}
    (hsame : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt)
    (hst : S.stored = D.stored) :
    ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored), op.sh.a = D.a ∧
      (∀ c ∈ op.out.cols, c.length = op.sh.W) ∧
      ∀ sl ∈ op.out.salts, sl.size = D.base.plan.salt := by
  intro op hop
  obtain ⟨t, ht, hs, hc, hsl⟩ := lens_sto e hown op hop
  rw [hst] at ht
  obtain ⟨ha, hsalt⟩ := hsame t ht
  exact ⟨by rw [hs, ha], hc, fun sl hm => (hsl sl hm).trans hsalt⟩

end OnBytes.K.Left
