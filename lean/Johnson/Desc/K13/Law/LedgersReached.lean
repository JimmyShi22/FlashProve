-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LedgersReached.lean: EVERY LEDGER IS IN ORDER AT EVERY STATE THAT THE FOLD
REACHES: THE GENERAL HALF. One statement as a definition of a proposition, and the rule that gives
it. No kind and no IOP is named: the list of sub-protocols is a letter.
IN PLAIN WORDS. "In order" (`LedgersFit`, Johnson/Desc/K13/Law/OwedLedgers.lean): every ledger of
mask entries in the statement is that of some number of takes since it was made. "Reached" (`Reach`,
Johnson/Top/H0/Walk/Reach.lean): the state comes from the chain's first state by the own steps of
the first k sub-protocols, each accepting at some rounds and columns. The rule: where the first
state has no oracle message, and the decision of every sub-protocol of the list keeps "in order in
front, in order behind" (`FitStays`, LedgersB.lean), every reached state is in order.
On words: "the state" is the value that the fold carries from sub-protocol to sub-protocol; st reads
the statement off it.
  `RchLedgers st Rch`   THE STATEMENT, general in a family Rch: ∀ k a, Rch k a →
                        LedgersFit (st a.1.2): the form of a field of the structure of facts
                        along the fold.
  `reach_ledgers`       THE RULE, by induction on `Reach`: the start by `ledgersFit_none`
                        (LedgersKept.lean); a step by `K1.step_ok` (a step's yes is a yes of the
                        decision) and the premise on that sub-protocol.
  `reach_ledgers_plan`  the same where the premise is asked only of sub-protocols that pass their
                        own test on the list of rounds, and all of them pass.
  `rchAt_ledgers`       **at the family `RchAt F`** (ReachAt.lean) of an IOP as written in Lean.
"REACHED" IS AN EXISTENTIAL: the rounds and columns are bound inside "there are"; nothing is
concluded here about them: the conclusion reads the state alone.
What is not claimed. That any sub-protocol keeps it: that is the premise hb. That an IOP's first
state has no oracle message: the premise h0. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.LedgersB
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Ground (By)
open Johnson.Desc.First.Walk.Tied (Reach StepYes RchAt)

/-- **THE STATEMENT**: at every reached state every ledger is in order. -/
def RchLedgers {Pp T Str : Type} (st : T → Statement) (Rch : ℕ → (Pp × T) × Str → Prop) : Prop :=
  ∀ k a, Rch k a → LedgersFit (st a.1.2)

/-- **THE RULE.** -/
theorem reach_ledgers {Pp T Cl : Type} (st : T → Statement) {ft : ℕ} {bs : List (Block T Cl)}
    {start : Pp → T} (h0 : ∀ z, (st (start z)).oracles = #[])
    (hb : ∀ b ∈ bs, Decides (By FitStays st) b) {k : ℕ} {a : Pp × T}
    (h : Reach ft bs start k a) : LedgersFit (st a.2) := by
  induction h with
  | zero z => exact ledgersFit_none _ (h0 z)
  | @succ k z s s' b _ hk hy ih =>
    obtain ⟨R, c, _, hs⟩ := hy
    obtain ⟨_, gs, hd⟩ := K1.step_ok ft b s s' R c _ hs
    exact hb b (List.mem_of_getElem? hk) s _ gs s' hd ih

/-- The same, the premise asked only under the sub-protocol's own test on the list of rounds. -/
theorem reach_ledgers_plan {Pp T Cl : Type} (st : T → Statement) {ft : ℕ}
    {bs : List (Block T Cl)} {start : Pp → T} (h0 : ∀ z, (st (start z)).oracles = #[])
    (hp : ∀ b ∈ bs, b.planOk = true)
    (hb : ∀ b ∈ bs, b.planOk = true → Decides (By FitStays st) b) {k : ℕ} {a : Pp × T}
    (h : Reach ft bs start k a) : LedgersFit (st a.2) :=
  reach_ledgers st h0 (fun b hm => hb b hm (hp b hm)) h

/-- **At the family of an IOP as written in Lean.** -/
theorem rchAt_ledgers {Xi Str : Type} (F : FileDescription Xi) (st : F.S₁ → Statement)
    (h0 : ∀ z, (st (F.start₁ z)).oracles = #[])
    (hb : ∀ b ∈ F.first.blocksInOrder, Decides (By FitStays st) b) :
    RchLedgers st (RchAt (Str := Str) F) :=
  fun _ _ h => reach_ledgers st h0 hb (Johnson.Desc.First.Walk.Tied.reach_raw h)

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.reach_ledgers
#print axioms VerifiableInference.Desc.K13.Law.reach_ledgers_plan
#print axioms VerifiableInference.Desc.K13.Law.rchAt_ledgers
