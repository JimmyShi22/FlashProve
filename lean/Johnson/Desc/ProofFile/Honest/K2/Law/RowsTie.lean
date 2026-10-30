-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/RowsTie.lean: the kind "the code switch" (K2): THE LAW THAT
TIES `switchRowsLaid` (Honest/K2/ScriptLots.lean), WHICH WRITES ONCE MORE WHAT THE SWITCH's PART
SENDS IN ITS FIRST ROUND, TO THE TEXT THAT IT REPEATS: the part's own first move (`switchPart`,
Honest/K2/Part.lean; by name `moveOne`, Honest/K2/Law/SwitchMoves.lean) at the sender `coreSender
freshTable`. EQUATIONS WITHOUT A HYPOTHESIS. Three statements with their proofs; no definition.

  `tables_are`      the sender's tables are the shared sending's `treeTables` of `rowsAll`'s rows
  `says_of_rows`    WHAT THE FIRST MOVE SAYS IS: no item in the clear, and `treeTables` of
                    `switchRowsLaid`'s rows; it refuses just where `switchRowsLaid` refuses, with
                    the same words
  `table_of_rows`   so the table number τ of the switch's sending (`switchTableAt`,
                    Honest/K2/Seated.lean) is table number τ of `treeTables` of these rows, at what
                    `handed` hands; a table without a word where either answers nothing

`treeTables` (Honest/K1/Part.lean, of other authors): for each tree of a place its table, of the
messages' rows: called, not typed again.

Limits. AT `coreSender freshTable` ALONE: at another sender nothing is said. On the first round's
tables: nothing on the second round's answers. Nothing on what a row holds. NO LOT IS LAID. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots
import Johnson.Desc.ProofFile.Honest.K2.Seated
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- The sender's tables are `treeTables` of the rows. -/
theorem tables_are (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (data : Nat → Nat → Nat → Cb.Gl.E)
    (c : Cs (sendingDue codes sent fresh)) :
    (coreSender freshTable).tables codes sent fresh data c =
      (rowsAll freshTable codes sent fresh data c).map
        (K1.treeTables (sendingPar codes sent)) := by
  show (rowsAll freshTable codes sent fresh data c).map _ = _
  congr 1
  funext V
  unfold K1.treeTables VerifiableInference.Desc.K1.Par.trees
  have e1 : (sendingPar codes sent).codes = codes := rfl
  rw [e1, sendingPar_sent]
  cases VerifiableInference.Desc.Own.treesMade codes sent <;> rfl

/-- **WHAT THE FIRST MOVE SAYS, OF `switchRowsLaid`'s ROWS.** -/
theorem says_of_rows (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (w : Local W₀ Rc Xi Tr)
    (h : List Fmt.Drawn) (s : Seen) :
    (moveOne (coreSender freshTable) p.sizes p.others p.foldVars p.carries).say c s
        ⟨switchWit D readers closing p w, h, ()⟩ =
      (switchRowsLaid D readers closing p c w h).map fun V =>
        ⟨[], K1.treeTables (sendingPar p.sizes.codes (switchSent p.sizes p.others)) V⟩ := by
  unfold moveOne switchRowsLaid
  simp only [tables_are]
  cases p.sizes.serves with
  | false => rfl
  | true =>
    cases p.sizes.roomy with
    | false => rfl
    | true =>
      show ((switchRowsAt p.sizes p.carries c.2.2
        ⟨switchWit D readers closing p w, h, ()⟩ 0).bind _) = Except.map _ (Except.bind
          (switchRowsAt p.sizes p.carries c.2.2 ⟨switchWit D readers closing p w, h, ()⟩ 0) _)
      cases switchRowsAt p.sizes p.carries c.2.2 ⟨switchWit D readers closing p w, h, ()⟩ 0 with
      | error _ => rfl
      | ok M =>
        show Except.map _ (Except.map _ (rowsAll freshTable p.sizes.codes
          (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) M c.1)) =
          Except.map _ (rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) M c.1)
        cases rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) M c.1 <;> rfl

/-- **THE TABLE AT THE SWITCH's TREE IS MADE OF THESE ROWS.** -/
theorem table_of_rows (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (h : List Fmt.Drawn) (τ : Nat) :
    switchTableAt Bk ch (coreSender freshTable) D readers closing p k w h τ =
      (((handed ch p k).bind fun c => (switchRowsLaid D readers closing p c w h).toOption).bind
        fun V => (K1.treeTables (sendingPar p.sizes.codes (switchSent p.sizes p.others))
          V)[τ]?).getD noTable := by
  unfold switchTableAt switchSays handed
  cases lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
  | error _ => rfl
  | ok c =>
    show (((moveOne (coreSender freshTable) p.sizes p.others p.foldVars p.carries).say c noSeen
      ⟨switchWit D readers closing p w, h, ()⟩).toOption.bind (·.tables[τ]?)).getD noTable = _
    rw [says_of_rows]
    show _ = (((switchRowsLaid D readers closing p c w h).toOption).bind _).getD noTable
    cases switchRowsLaid D readers closing p c w h <;> rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.tables_are
#print axioms ProofFile.Honest.K2.Law.says_of_rows
#print axioms ProofFile.Honest.K2.Law.table_of_rows
