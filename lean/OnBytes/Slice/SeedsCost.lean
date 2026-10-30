-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SeedsCost.lean: the text of the program's `recordSeeds`, at a hash that asks an
oracle, tosses no coin and asks at most one question more than twice `seedCalls bits count`.

`recordSeedsW` (OnBytes/Slice/RecordRead.lean) is generic in the hash and in the monad. The library
has a frame for counts of questions in any monad (`Run.CostP`, Run/CostP.lean), with a law for one
step of a chain (`Run.CostP.queryW`, Run/CostFmtProofs.lean), and the count "no coin, at most t
queries" for algorithms that ask the one oracle (`Run.qp`, Run/OCompCostP.lean). The text is one
call number 160, one step of a chain, and a value.

Main theorems.
 `recordSeedsW_cost`    in any monad with a count: a for the call number 160 on the name, k for a
                        call of the hash: a + `seedCalls bits count` k.
 `HM_cost_one`, `recordSeedsW_HM_cost`   at the hash that asks by `ask`, each `ask s` at most 1: a
                        call with a number other than 162 costs 1; the text costs one more than
                        twice `seedCalls bits count`.
 `recordSeedsW_asks`    FOR ALGORITHMS THAT ASK THE ONE ORACLE: no coin, and at most that many
                        questions. The hypothesis has the form of that of `chainChkBy_bound`
                        (OnBytes/Slice/ChainChkAsk.lean); `Tie.qp_askB` meets it at `Run.askB`.

What is not claimed. Which strings are asked (`askSeed_asked`, OnBytes/Slice/SeedAsked.lean, for the
algorithm `askSeed`; `seedAt_ask_eq`, OnBytes/Slice/SeedWhich.lean). What the text returns. That any
checker runs it. The count is an upper bound: where the round's data are refused the text asks one
question. No number is evaluated (at the sizes of OnBytes/Slice/RecordFull.lean the bound is 143:
`rec_questions`). Nothing on any hash function.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.SeedAsked
import Run.CostFmtProofs
import Run.OCompCostP

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## In any monad with a count of questions -/

section
variable {m : Type → Type} [Monad m] (c : Run.CostP m)

/-- The count of the text of `recordSeeds`, in any monad with a count of questions: if the call
number 160 on a name costs at most a and every call of the hash at most k, the text costs at most
a + `seedCalls bits count` k. -/
theorem recordSeedsW_cost (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → m ByteArray) (a k : ℕ)
    (h0 : ∀ b, c.le (h 160 0 Fmt.recordLabel Fmt.zero32 b) a fun _ => True)
    (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
    (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) :
    c.le (recordSeedsW h f name bits count) (a + seedCalls bits count * k) fun _ => True :=
  c.le_bind _ _ a (seedCalls bits count * k) (fun _ => True) _ (h0 _) fun _ _ =>
    c.bindPure _ _ _ (fun _ => True) _ (c.queryW h k hk _ _ _ _ _ _) fun _ _ => trivial

/-- The hash that asks by `ask`, at a number other than 162, costs what one `ask` costs. -/
theorem HM_cost_one (ask : ByteArray → m ByteArray) (k : ℕ)
    (hk : ∀ s, c.le (ask s) k fun _ => True) (number tree index : ℕ) (start bytes : ByteArray)
    (hn : number ≠ 162) : c.le (Fmt.HM ask number tree index start bytes) k fun _ => True := by
  unfold Fmt.HM
  rw [if_neg hn]
  exact hk _

/-- At the hash that asks by `ask`: if every `ask s` costs at most 1, the text costs at most
2 `seedCalls bits count` + 1. -/
theorem recordSeedsW_HM_cost (ask : ByteArray → m ByteArray)
    (h1 : ∀ s, c.le (ask s) 1 fun _ => True) (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) :
    c.le (recordSeedsW (Fmt.HM ask) f name bits count) (2 * seedCalls bits count + 1)
      fun _ => True :=
  c.le_mono _ _ _ _ _
    (recordSeedsW_cost c (Fmt.HM ask) 1 (2 * 1)
      (fun b => HM_cost_one c ask 1 h1 160 0 Fmt.recordLabel Fmt.zero32 b (by decide))
      (c.HM ask 1 h1) f name bits count)
    (by omega) fun _ h => h

end

/-! ## For algorithms that ask the one oracle -/

/-- If every `ask s` tosses no coin and asks at most one question, the text of `recordSeeds` at
the hash that asks by `ask` tosses no coin and asks at most one question more than twice `seedCalls
bits count`: as many as `askSeed` (OnBytes/Slice/SeedAsked.lean). -/
theorem recordSeedsW_asks (ask : ByteArray → ZKCP.OComp 256 ByteArray)
    (h : ∀ s, (Run.qp 256).le (ask s) 1 fun _ => True) (f : Fmt.Fld) (name : ByteArray)
    (bits count : ℕ) :
    (recordSeedsW (Fmt.HM ask) f name bits count).NoCoin ∧
      (recordSeedsW (Fmt.HM ask) f name bits count).QueryBound (2 * seedCalls bits count + 1) :=
  ⟨(recordSeedsW_HM_cost (Run.qp 256) ask h f name bits count).1,
    (recordSeedsW_HM_cost (Run.qp 256) ask h f name bits count).2.1⟩

end OnBytes.Slice
