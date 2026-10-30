-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/EqLays.lean: WHAT A YES OF THE ONE EQUATION's BLOCK DOES TO WHAT THE
TABLE's PROMISE READS OF THE RECORD: ONE PLAIN ROW IS PUSHED AT THE END OF THE LINK's GROUP's LIST
OF OPEN ROWS; the count of rows is paid; all else is as it was. Theorems on the block's step, at the
first chain's record.

What is said.
  `termsRow_kind`, `asRow_kind`: the row that the equation is made into is plain. `door_link`: the
    door hands the link's record back. `EqLays s s' g row`: the statement's groups behind are those
    in front with `row` pushed on group g's list; the row is plain; as many oracle messages; the
    mark, the book, the number of roots, the stand and the open link's number as they were; no count
    of rows waits. `eq_lays`: **a yes of a block each of whose yeses is the one equation's gives
    `EqLays` at the link's own group**, which is there in front.

Limits. Facts on one block. What the table's tests on the open rows and on the members say behind it
is RowsPush.lean's. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RbRuns
import Johnson.Desc.First.Link.Law.OwedPaid
import Johnson.Desc.First.Batch.Law.DoorTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.K9 (atS Where door asRow termsRow)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S standOf)

/-- The summands' laying leaves the row's kind. -/
theorem termsRow_kind (layout : ReqLayout) (f : ReqFrame) (St : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), termsRow layout f St ts row = .ok row' →
      row'.kind = row.kind
  | [], row, row', h => by
    have e : row = row' := Except.ok.inj h
    rw [e]
  | t :: ts, row, row', h => by
    rw [termsRow] at h
    obtain ⟨a, _, h⟩ := ok_bind h
    obtain ⟨o, _, h⟩ := ok_bind h
    obtain ⟨c, _, h⟩ := ok_bind h
    exact termsRow_kind layout f St ts (row.addForm o c) row' h

/-- The row that the equation is made into is plain. -/
theorem asRow_kind {X : Type} (Rr : ReqRows) (f : ReqFrame) (q : K9.Equation) (d d' : K9.St X)
    (row : OnBytes.Row) (h : asRow Rr f q d = .ok (row, d')) : row.kind = .plain := by
  unfold asRow at h
  obtain ⟨row0, h0, h⟩ := ok_bind h
  have k0 : row0.kind = .plain := termsRow_kind _ _ _ _ _ _ h0
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e : ({ row0 with target := subE zeroE q.constant } : OnBytes.Row) = row :=
      congrArg Prod.fst (Except.ok.inj h)
    rw [← e]
    exact k0
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o', _, h⟩ := ok_bind h
    obtain ⟨x, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e : ({ row0.addRun o' .mask 0 1 (.own q.onMasks) with
        target := subE zeroE q.constant } : OnBytes.Row) = row :=
      congrArg Prod.fst (Except.ok.inj h)
    rw [← e]
    exact k0

/-- The door hands the link's record back. -/
theorem door_link {X : Type} (owed : K9.RowsOwed) (laid : Option ℕ) (L : LinkCtx) (F : Fork)
    (d : K9.St X) (o : K9.Out X) (h : door owed laid L F d = .ok o) : o.L = L := by
  unfold door at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]

/-- **What the one equation's yes does to what the promise reads of the record.** -/
structure EqLays (s s' : S) (g : ℕ) (row : OnBytes.Row) : Prop where
  groups : s'.st.groups = s.st.groups.modify g fun G => { G with rows := G.rows.push row }
  kind : row.kind = .plain
  oracles : s'.st.oracles.size = s.st.oracles.size
  failed : s'.failed = s.failed
  book : s'.book = s.book
  roots : s'.roots = s.roots
  stand : standOf s' = standOf s
  num : s'.link?.map (·.link) = s.link?.map (·.link)
  owed : s'.rowsOwed = none

/-- **A YES OF THE ONE EQUATION's BLOCK LAYS ONE PLAIN ROW ON THE LINK's GROUP.** -/
theorem eq_lays {Cl : Type} (pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₃.step ft s rs cols = .ok (s', k)) :
    ∃ (a : K9.Part) (row : OnBytes.Row) (G0 : Group), atS.get? s = some a ∧
      s.st.groups[a.L.check.group]? = some G0 ∧ EqLays s s' a.L.check.group row := by
  have hp := (owed_paid pw b₃ hb₃ ft s rs cols s' k h).1
  obtain ⟨a, out, ha, hdoor, rfl⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ h)
  obtain ⟨hL, hst⟩ := part_reads s a ha
  obtain ⟨q, G, row, d1, _, hr, hadd⟩ := door_addRowP _ _ _ _ _ _ hdoor
  obtain ⟨row', d1', G0, hout, _, hG0, _⟩ := door_tests _ _ _ _ _ _ hdoor
  have hout2 : out.d = { d1 with st := Slice.withRow d1.st a.L.check.group row } := by
    unfold Ground.addRowP at hadd
    split at hadd
    · exact (Option.some.inj hadd).symm
    · simp at hadd
  have h1 := (rb_putLink s a.L out.L hL (by rw [door_link _ _ _ _ _ _ hdoor])).trans
    (rb_putFork _ out.F)
  refine ⟨a, row, G0, ha, by rw [← hst]; exact hG0, ?_, asRow_kind _ _ _ _ _ _ hr, ?_, h1.failed,
    h1.book, h1.roots, h1.stand, h1.num, hp⟩
  · show out.d.st.groups = _
    rw [hout2, ← hst, ← asRow_groups _ _ _ _ _ _ hr]
    rfl
  · show out.d.st.oracles.size = _
    rw [hout2, ← hst, ← asRow_size _ _ _ _ _ _ hr]
    rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.asRow_kind
#print axioms VerifiableInference.Desc.LinkJoin.eq_lays
