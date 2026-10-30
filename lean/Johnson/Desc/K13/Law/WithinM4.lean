-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/WithinM4.lean: THEOREM: OwedWithinM4 (OwedWithin.lean): over a yes of W's
commitment (atM4 P (K1.sendAtS P')) the item "K13.pileWithin" goes on: every ledger fits, and every
mask entry that a row on the table names lies within its table. UNDER TWO OF THE STATEMENTS THAT ARE
OWED BESIDE IT, as binders: OwedLedgersC (the test on the ledgers says what the laws' word says) and
OwedLedgersKept (the ground's plain functions keep "every ledger fits").
  tableSizeC_grows  a number below the size of a table stays below it where the statement has grown
                    (Grows: the code table stays; each message keeps its shape).
  atM4_rel          BOTH HALVES OF THE JOINED BLOCK WRITE THE STATEMENT THROUGH THE GROUND's PLAIN
                    FUNCTIONS ALONE (K1.Rel.sendAtS_keeps; atM4_keeps over rowsB_keeps): so every
                    relation that these functions keep holds from the statement in front to the
                    statement behind.
  withinM4          the ledgers: atM4_rel at OwedLedgersKept. The rows on the table: they stay
                    (atM4_rec); the tables' sizes: atM4_rel at "a statement only grows".
THE QUESTION THAT THE STATEMENT's HEAD PUTS ("SameAll says nothing of a ledger: read rowsB's text")
needs no reading of that text here: what rowsB does to a ledger is whatever the ground's functions
do, and that is OwedLedgersKept's matter.
What is not claimed. The two binders. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.OwedWithin
import Johnson.Desc.K1.KeepsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (GroundKeeps groundKeeps_grows)

/-- Where the statement has grown, a number below a table's size stays below it. -/
theorem tableSizeC_grows {T T' : Statement} (h : Grows T T') (o : ℕ) (part : OnBytes.Part) (n : ℕ)
    (hn : n < tableSizeC T o part) : n < tableSizeC T' o part := by
  cases hx : T.oracles[o]? with
  | none =>
    have e : tableSizeC T o part = 0 := by
      unfold tableSizeC Statement.has
      simp [hx]
    omega
  | some x =>
    obtain ⟨x', hx', hs, -, -⟩ := h.2.2 o x hx
    have e : tableSizeC T' o part = tableSizeC T o part := by
      unfold tableSizeC Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
      simp only [hx, hx', hs, h.1]
    rw [e]
    exact hn

/-- **Over a yes of W's commitment** every relation that the ground's plain functions keep holds
from the statement in front to the statement behind. -/
theorem atM4_rel {Cl : Type} {R : Statement → Statement → Prop} (H : GroundKeeps R) (P : Where)
    (P' : K1.Par) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s rs gs = .ok s') : R s.st s'.st :=
  atM4_keeps H.quiet P (K1.sendAtS P') (K1.Rel.sendAtS_keeps H P') s rs gs s' h

/-- **"K13.pileWithin" goes on over W's commitment.** -/
theorem withinM4 (hC : OwedLedgersC) (hK : OwedLedgersKept) : OwedWithinM4 := by
  intro Cl P P' s s' r₁ r₂ gs h hp
  unfold pileWithinC at hp ⊢
  rw [Bool.and_eq_true] at hp ⊢
  obtain ⟨hl, hr⟩ := hp
  have hL : LedgersFit s.st → LedgersFit s'.st := atM4_rel hK P P' s s' _ gs h
  refine ⟨(hC s').2 (hL ((hC s).1 hl)), ?_⟩
  have hg : Grows s.st s'.st := atM4_rel groundKeeps_grows P P' s s' _ gs h
  have hrows : s'.rows = s.rows := (atM4_rec h).2.2.2.2
  unfold rowsWithinC at hr ⊢
  rw [hrows]
  simp only [List.all_eq_true, decide_eq_true_eq] at hr ⊢
  intro r hrm t ht
  exact tableSizeC_grows hg _ _ _ (hr r hrm t ht)

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.tableSizeC_grows
#print axioms VerifiableInference.Desc.K13.Law.atM4_rel
#print axioms VerifiableInference.Desc.K13.Law.withinM4
