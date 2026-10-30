-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ObjectsRidesHead.lean: THE OPEN CLAIM formsT 24 3 "objects"
RIDES FORWARD PAST THE SUB-PROTOCOL "the output head's own rounds" (K6; number 341 of the first
chain's flat list), IN THE FORM IN WHICH THE FIRST CHAIN'S THREAD ASKS IT: `RidesPastAtS`
(Honest/Thread/SharesS.lean) at the thread of `lettersHead` (Honest/Thread/FirstHead.lean). One
theorem. CONDITIONAL: h (the library's head AtMgA) · hp (p is the place written at number 341) · hK
(at that place the thread's letter for "what a yes keeps" gives `K6Keeps`,
Johnson/Desc/K6/Honest/Law/Keeps.lean).

How: calls and an unfolding. The form hands over the thread's sentence in front, the letter keeps at
the two states, and the claim's sentence in front at the prover's own witness. The thread's sentence
gives "reached at border 341" (`thr_reach`, Honest/Thread/ReachFacts.lean; that the flat list has
358 members: `Meaning.K2.flat_358`, Johnson/IMR/EndFive.lean); the letter gives `K6Keeps`
(`head_keeps`, then hK); the claim's sentence at the thread's meaning unfolds to the first clause of
the composed meaning's sentence at the head's own data: the thread lays two fields of these data
anew (the decoder of the stored table and the exact carry), which that clause does not read. Then
`objects_on_head_runs` (Johnson/Desc/K6/Honest/Law/ObjectsOnHead.lean). What is said so far, the
oracles' strings and the promise in front are not read.

Limits. `RidesPastAtS` is a premise's form of the thread's files: none of the library's goals. THAT
THE HEAD CAN BE MET, THAT THE THREAD STANDS AT ANY RUN, THAT hK HOLDS OF ANY LETTER: not shown here.
NOTHING HERE SAYS THAT A FORM IS WORTH 0 AT ANY STATE: the sentence in front is the form's own
premise. THE FULL SIZE ALONE, and the format's second hash function alone. Nothing on any property.
-/
import Johnson.Desc.K6.Honest.Law.ObjectsOnHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_reach head_keeps)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Honest (objects_on_head_runs)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`RidesPastAtS` AT THE OPEN CLAIM formsT 24 3 "objects", AT THE THREAD, AT NUMBER 341.**
CONDITIONAL: on h, hp and hK. -/
theorem k6_ridesPastAtS_objects_head
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {p : Place}
    (hp : P5J.At.ps[341]? = some p)
    (hK : ∀ s s', Kp p s s' → VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps s s') :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      Said 341 (Item.formsT 24 3 "objects") := by
  intro k s m E s' ps v hT hk hw
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hb : 341 ≤ cF.blocksInOrder.length := by
    rw [Meaning.K2.flat_358 h.scope O]
    omega
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT.1
  have K := hK s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').1 hk)
  obtain ⟨h1, -⟩ := hw
  exact ⟨objects_on_head_runs h hr K _ h1, fun e => absurd e (by decide)⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_ridesPastAtS_objects_head
