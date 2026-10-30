-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/SmpRowsLay.lean: WRITING ONE MESSAGE's LEDGER TURNS NO STORED OUT-OF-DOMAIN SAMPLE.
Statements with their proofs; no definition.

In plain words. The verifier's state holds the session's statement; the statement holds, for each
oracle message, its shape, a mark "sampled", its sample rows and, once it is sampled and where it
has mask rows, a ledger that hands out free mask entries. `K13.Law.layLedger st o l'`
(Johnson/Desc/K13/Law/LedgerWithin.lean) is the statement with the ledger l' written at message o
and nothing else turned. The three readers of a tenant's out-of-domain sample
(Johnson/Desc/SmpRows.lean) read the book's places, the codes, and of a message its mark, its shape
and its sample rows: never its ledger. So each of the three gives the same value at both
statements:
  `smpRows_lay`   the sample rows of tenant t of tree j
  `smpSeed_lay`   the seed and the answers that a run reads back off them
  `smpHeld_lay`   the test "the sample is held"
All three are equations without a premise: at every statement, every number o (also one at which
there is no message: then nothing is written), every ledger, every book, every j and t.

`lay_sees` is private: a reader that reads of a message these three fields alone gives the same at
both statements.

What is not claimed. Nothing on the book: it is the same letter on both sides. Nothing on any step
of the verifier: that a step's state behind is `layLedger` of the state in front is the caller's to
show. No soundness statement.

-/
import Johnson.Desc.SmpRows
import Johnson.Desc.K13.Law.LedgerWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes

/-- A reader that reads of a message its mark, its shape and its sample rows alone gives the same at
the statement with a ledger written as at the statement itself. -/
private theorem lay_sees (st : Statement) (o o' : ℕ) (l' : Ledger) {α : Type}
    (g : Bool → OracleShape → Array OnBytes.Row → Option α) :
    ((K13.Law.layLedger st o l').oracles[o']?).bind (fun x => g x.sampled x.shape x.sampleRows) =
      (st.oracles[o']?).bind (fun x => g x.sampled x.shape x.sampleRows) := by
  show ((st.oracles.modify o _)[o']?).bind _ = _
  rw [Array.getElem?_modify]
  by_cases h : o = o'
  · rw [if_pos h]
    cases st.oracles[o']? <;> rfl
  · rw [if_neg h]

/-- The sample rows of a tenant are the same behind the writing of a ledger. -/
theorem smpRows_lay (st : Statement) (o : ℕ) (l' : Ledger) (book : TreeBook) (j t : ℕ) :
    smpRows (K13.Law.layLedger st o l') book j t = smpRows st book j t := by
  unfold smpRows
  cases oracleNo book j t with
  | none => rfl
  | some o' =>
    exact lay_sees st o o' l' (fun a s r =>
      if a && decide (0 < s.answers) && r.size == s.answers then some r else none)

/-- The seed and the answers that a run reads back are the same behind the writing of a ledger. -/
theorem smpSeed_lay (st : Statement) (o : ℕ) (l' : Ledger) (book : TreeBook) (j t : ℕ) :
    smpSeed (K13.Law.layLedger st o l') book j t = smpSeed st book j t := by
  unfold smpSeed
  rw [smpRows_lay]
  cases oracleNo book j t with
  | none => rfl
  | some o' =>
    exact lay_sees st o o' l' (fun _ s _ =>
      (smpRows st book j t).bind fun rows => (rows[0]?).bind fun r =>
        (seedOf st.codes s r).map fun sd => (sd, rows.toList.map (·.target)))

/-- **The test "the sample is held" gives the same Bool behind the writing of a ledger.** -/
theorem smpHeld_lay (st : OnBytes.Statement) (o : ℕ) (l' : OnBytes.Ledger)
    (book : OnBytes.TreeBook) (j t : ℕ) :
    smpHeld (K13.Law.layLedger st o l') book j t = smpHeld st book j t := by
  unfold smpHeld
  rw [smpSeed_lay]

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.smpRows_lay
#print axioms VerifiableInference.Desc.smpSeed_lay
#print axioms VerifiableInference.Desc.smpHeld_lay
