-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAskedCost.lean: the typing of an entry file tosses no coin and asks at most tT
strings, tT a closed expression of the tables' shape and the rounds, one at every digest of the
public files, every first table and every file.
Over the asking half (OnBytes/Tie/EntryAsked.lean: `askedE`, `typedE`, `typedER`): the twin's
reading of the entry file, then both tables' seeds once more. The reading's count:
OnBytes/ChecksWithHashAsArgument/M/AtPort/AsksRecord.lean; the seeds': OnBytes/Slice/SeedsCost.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryAsked
import OnBytes.ChecksWithHashAsArgument.M.AtPort.AsksRecord
import OnBytes.Slice.SeedsCost
import OnBytes.Slice.ChainChkAsk

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.TwoPort
open OnBytes.TwoPort.M.AsksRecord (entryT)

/-- The strings that the typing of an entry file asks at most: the reading's, and the seeds' of
both tables once more. -/
def typedT (s : Params.IndexShape) (r0 : Params.Rounds) : Nat :=
  entryT s r0 + 2 * (2 * Slice.seedCalls s.cubeBits s.answers + 1)

/-- The asking half, in the library's count with a condition. -/
theorem askedE_le (q : Params.Link) (first : Params.TableName) (ent : ByteArray)
    (r0 : Params.Rounds) (h0 : Params.entryRoundsAny q = some r0) :
    (Run.qp 256).le (askedE q first ent) (typedT q.link.table r0) fun _ => True := by
  unfold askedE typedT
  refine (Run.qp 256).le_bind _ _ _ _ (fun _ => True) _
    (M.Asks.le_readFit (Run.qp 256) 2 (Fmt.HM Run.askB) Run.qp_HM q first ent _
      (M.AsksRecord.specsBelowFit_of_zero q first r0 h0)) fun r _ => ?_
  cases r with
  | error e => exact Run.CostP.pureLe (Run.qp 256) _ _ _ trivial
  | ok r =>
    refine (Run.qp 256).le_mono _ ((2 * Slice.seedCalls q.link.table.cubeBits q.link.table.answers
      + 1) + ((2 * Slice.seedCalls q.link.table.cubeBits q.link.table.answers + 1) + 0)) _ _ _ ?_
      (by omega) fun _ h => h
    refine (Run.qp 256).le_bind _ _ _ _ (fun _ => True) _
      (Slice.recordSeedsW_HM_cost (Run.qp 256) Run.askB qp_askB _ _ _ _) fun l0 _ => ?_
    refine (Run.qp 256).le_bind _ _ _ _ (fun _ => True) _
      (Slice.recordSeedsW_HM_cost (Run.qp 256) Run.askB qp_askB _ _ _ _) fun l1 _ => ?_
    exact (Run.qp 256).le_pure _ _ trivial

/-- For any plain map behind the asking half: the typing, as a tree in the
library's generic language, tosses no coin and asks at most `typedT` strings. -/
theorem typedER_asks {Out : Type} (asm : AskedE → Option Out) (q : Params.Link)
    (first : Params.TableName) (ent : ByteArray) (r0 : Params.Rounds)
    (h0 : Params.entryRoundsAny q = some r0) :
    (typedER asm q first ent).NoCoin ∧
      (typedER asm q first ent).QueryBound (typedT q.link.table r0) := by
  have e : (Run.qp 256).le (typedE asm q first ent) (typedT q.link.table r0 + 0) fun _ => True :=
    (Run.qp 256).le_bind _ _ _ _ (fun _ => True) _ (askedE_le q first ent r0 h0) fun _ _ =>
      (Run.qp 256).le_pure _ _ trivial
  exact toRom_out _ _ ⟨e.1, e.2.1⟩

/-- At a ground G, at EVERY digest c, every first table and every file: ONE number. -/
theorem EntryGround.typedER_asks {Out : Type} (G : EntryGround) (asm : AskedE → Option Out)
    (c : ByteArray) (first : Params.TableName) (ent : ByteArray) :
    (typedER asm (linkAtCfg G.q c) first ent).NoCoin ∧
      (typedER asm (linkAtCfg G.q c) first ent).QueryBound (typedT G.q.link.table G.rs) :=
  Tie.typedER_asks asm (linkAtCfg G.q c) first ent G.rs (G.rounds_at c)

/-- At the full size: 41,336 for the reading and 2 · 143 for the seeds once more. -/
theorem record_typedT : typedT Params.recordRead.link.table Params.recordRounds = 41622 := by
  unfold typedT
  rw [M.AsksRecord.record_entryT]
  decide +kernel

end OnBytes.Tie
