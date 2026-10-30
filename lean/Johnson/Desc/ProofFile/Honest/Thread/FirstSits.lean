-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstSits.lean: the first chain's `Thread` at the library's own
terms (`lettersAt`, Honest/Thread/FirstAt.lean) is taken from the description that the library's
hypothesis `AtMgA` names. That hypothesis contains, in its field `laid` (`P5J.LaidAt`,
Johnson/P5J/LaidOpens.lean): the function that computes the description returns exactly the term
`P5J.F0T o Zp Np cF`, and that term passes the description's own test on the plan. Here: that term's
first chain's flat list is the list that `lettersAt` supplies as `bs`; the types of its first state
and of its claims are those of the `Thread`. So the first of the three clauses of `Sits`
(Honest/Thread/File.lean) holds by unfolding, at whatever prover's sides are supplied as `hs`; and
`planOk` is the hypothesis's own field. Lemmas: equations by unfolding, and one projection.

  `head_flat`     the term's first chain's flat list is that of cF
  `head_planOk`   the test on the plan: the hypothesis's own field: nothing is evaluated
  `head_value`    what the function that computes the description returns at the hypothesis's three
                  files
  `sits_first`    the five equations of `Sits.one`

Limits.
  * The full size alone, and the hash function `secondHashFunction` alone, as for `lettersAt`
    (Honest/Thread/FirstAt.lean says which that is).
  * A term of the library's hypothesis `AtMgA` exists, at `D` := `dpZ Z` and `r` :=
    `theProofRun (asDescriptionFiles Z)` alone, under four hypotheses on the public files (the library's
    `head_exists_at_name`); this file does not call it; no such term together with the invariant's
    proposition is proved to exist.
  * The tests of `Sits` on the parameters (`Thread.fits`) are not touched.
  * Nothing is said on the two later chains.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem head_flat (o : ProofFile.SecondHashFunctionArgument) : (F0T o Zp Np cF).first.blocksInOrder = cF.blocksInOrder := rfl

theorem head_planOk {o : ProofFile.SecondHashFunctionArgument} (h : AtMgA o Z D r Zp Np cF x) :
    (F0T o Zp Np cF).planOk = true := h.laid.planOk

theorem head_value {o : ProofFile.SecondHashFunctionArgument} (h : AtMgA o Z D r Zp Np cF x) :
    ProofFile.onlineDescription o Z.pol Z.lay Z.KL = .ok (F0T o Zp Np cF) := h.laid.value

/-- **The first clause of `Sits`, by unfolding**: at the prover's sides of whatever prover. -/
theorem sits_first (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) :
    (lettersAt h H.first Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.φ = .own ∧
      (lettersAt h H.first Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.chain =
        0 ∧
      (lettersAt h H.first Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.ft = 0 ∧
      (lettersAt h H.first Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.bs =
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ∧
      (lettersAt h H.first Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.hs =
        H.first :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_flat
#print axioms ProofFile.Honest.FirstThread.head_planOk
#print axioms ProofFile.Honest.FirstThread.head_value
#print axioms ProofFile.Honest.FirstThread.sits_first
