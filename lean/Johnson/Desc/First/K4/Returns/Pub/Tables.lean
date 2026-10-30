-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/Tables.lean: THE PLACES OF THE FAMILIES OF TABLES, AS A PUBLIC
TEST. The hearing of the sub-protocol K4 asks that layTables (OnBytes/Model/LayerForms.lean) returns
at the group's matrices and families, and that the first free entry behind them is the plan's length
of the reads. Both read public numbers alone, so the test is that clause itself, with code.

Limits. THE TEST IS SHOWN TRUE AT NO PLAN HERE. Nothing is said on what the tables hold. Where
OnBytes/Iop/SymbolLaws.lean is imported too,
the bare name tablesAt can mean the library's OnBytes.tablesAt: write
OnBytes.Desc.First.K4.RtPub.tablesAt. No property is claimed.

  matsAt, tablesAt   the rows and columns of the group's matrices; what layTables returns there.
  tablesB            the test.
  tables_iff         the test is true just where the hearing's clause holds at some places.
  tables_at          the clause at the places that layTables returns.
-/
import OnBytes.Model.LayerPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- The rows and the columns of the matrices of group g, as the hearing takes them. -/
def matsAt (P : Pub) (g : Nat) : Array (Nat × Nat) :=
  (P.tails.getD g {}).mats.map fun M => (M.m, M.k)

/-- The places of the families of tables of group g. -/
def tablesAt (P : Pub) (g : Nat) :
    Option (List TableAt × List (TableAsk × List (Nat × Nat)) × Nat) :=
  layTables (matsAt P g) (tableAsks P.y P.rd g) 0

/-- **The public test**: the families are placed, and they end at the plan's length of the reads. -/
def tablesB (P : Pub) (hp : HPlan2) (g : Nat) : Bool :=
  (tablesAt P g).any fun r => r.2.2 == hp.nU.getD 2 0

/-- The test is true just where the hearing's clause holds at some places. -/
theorem tables_iff (P : Pub) (hp : HPlan2) (g : Nat) :
    tablesB P hp g = true ↔ ∃ tab laid nU3,
      layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
        some (tab, laid, nU3) ∧ (nU3 == hp.nU.getD 2 0) = true := by
  show ((tablesAt P g).any fun r => r.2.2 == hp.nU.getD 2 0) = true ↔
    ∃ tab laid nU3, tablesAt P g = some (tab, laid, nU3) ∧ (nU3 == hp.nU.getD 2 0) = true
  cases tablesAt P g with
  | none =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, _, _, e, _⟩
      cases e
  | some r =>
    obtain ⟨tab, laid, n⟩ := r
    constructor
    · intro h
      exact ⟨tab, laid, n, rfl, h⟩
    · rintro ⟨_, _, _, e, h⟩
      cases e
      exact h

/-- **The hearing's clause at the places that layTables returns.** -/
theorem tables_at {P : Pub} {hp : HPlan2} {g : Nat} {tab : List TableAt}
    {laid : List (TableAsk × List (Nat × Nat))} {n : Nat}
    (e : tablesAt P g = some (tab, laid, n)) (h : tablesB P hp g = true) :
    ∃ nU3, layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
      some (tab, laid, nU3) ∧ (nU3 == hp.nU.getD 2 0) = true := by
  unfold tablesB at h
  rw [e] at h
  exact ⟨n, e, h⟩

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.tables_iff
#print axioms OnBytes.Desc.First.K4.RtPub.tables_at
