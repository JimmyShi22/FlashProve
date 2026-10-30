-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ShareAtFull.lean.
WHAT IT IS NOT. IT SHOWS NO ITEM TRUE: it says that what each of the three items MEANS at these
letters follows from the composed meaning's field at the data with two fields turned. CONDITIONAL on
the one hypothesis of Honest/Thread/FirstAt.lean. The full size and the format's second hash function alone,
as that file. The other five fields of the structure are not shown here (Honest/K6/Law/
LettersFull.lean has them). Nothing on any property.
WHAT IT IS. The first three fields of `K6ShareLetters` (Honest/K6/Law/Share.lean) AT THE FIRST
CHAIN's LETTERS AT THE LIBRARY's OWN (Honest/Thread/FirstAt.lean: `lettersAt`). One theorem, by
unfolding.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Share
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (mgAll mgBase MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA mgAtAll CellsM TS)
open ProofFile.Honest (ProverCoinCounts Local Placed)
open ProofFile.Honest.FirstThread (Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on the one hypothesis h: at the first chain's letters at the library's own, what
each of the three items means follows from the composed meaning's field at the turned data: by
unfolding. -/
theorem k6_means_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) (run : String) :
    ∀ (w : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (y : Strs) (v : WtF),
      (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells w), cr1 := carryX } mgBase).formsT 24 4
          run (id a.1, a.2) y (id v) →
        (ProofFile.Honest.FirstThread.lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides
          keeps).thread.means w (Item.formsT 24 4 run) a y v :=
  k6_means_at
    (ProofFile.Honest.FirstThread.lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
    (Dof := fun w => { h.𝔇 with decT := fun _ _ => some (Q.cells w), cr1 := carryX })
    (Mg₀ := mgBase) (fun _ => rfl) run

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_means_full
