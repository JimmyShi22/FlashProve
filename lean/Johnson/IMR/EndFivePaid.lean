-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/EndFivePaid.lean: THE FIVE FACTS AT EVERY REACHED LAST STATE OF THE FIRST CHAIN THAT
BEARS NO MARK, UNDER THE DESCRIPTION's OWN TEST ON THE PLAN: a join of two files that lie; no
induction is typed here. For the premise h5 of Sh.reachOwed_in_scope
(Johnson/Desc/K14/Law/SharedConstReachAt.lean).

WHY. Johnson/IMR/EndFive.lean's five_at_end stands under hp (every entry of the flat list passes its test on the plan) and D (IM.SendDebts: what each sending sub-protocol appends to the list of commitment trees). Johnson/IMR/SendsFinal.lean pays D under blocksOk c.blocksInOrder = true (debts_final), and Johnson/IMR/PlanOkFlat.lean draws that from F.planOk = true. So both premises fall to one: F.planOk = true.

WHAT IS SAID.
  planOk_of_blocksOk   blocksOk bs = true gives b.planOk = true at every entry b of bs
  five_at_end_planOk   the five facts, in scope, at an opening O, under F.planOk = true, hB and hL
  h5_planOk            the same in the letters of Sh.reachOwed_in_scope's premise h5: ∀ Bs base A B, IM.Open … → the five facts (the def Sh.FiveAtEnd Z c L of SharedConstReachAt.lean, written out: that file is not imported here)

THE PREMISES THAT ARE LEFT, AND WHOSE EACH IS. hS: the goals' scope · O: free, by seat_open · hF :
F.planOk = true: the description's own test on the plan: whoever holds an accepting run has it
(FileDescription.planOk_parts_of_run's first step); planOk_of_laid [not in this library] by another's word
· hB : K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true: a closed
test on the list of rounds: evaluated once, PROVED AT NO LIST · hL : K12.Door.laidAtCodes
Z.first.codes Z.made.proof.1 = some L: the caller's own.

What is not claimed. hF, hB, hL are shown nowhere here. At OnBytes.secondHashFunction alone. No soundness.

-/
import Johnson.IMR.EndFive
import Johnson.IMR.SendsFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {P : VerifierAndGoals.PublicFiles}

/-- Where the test on a list of sub-protocols accepts, each entry passes its own test on the plan. -/
theorem planOk_of_blocksOk {bs : List (Block S Cl)} (h : blocksOk bs = true) : ∀ b ∈ bs, b.planOk = true := by
  intro b hb
  unfold blocksOk at h
  have h1 := List.all_eq_true.mp h b hb
  simp only [Bool.and_eq_true] at h1
  exact h1.1

/-- **The five facts under the description's own test on the plan.** -/
theorem five_at_end_planOk (hS : VerifierAndGoals.InScope P = true) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true) (hB : K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true) {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L) : ∀ p : ProofFile.InstPub × S, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length p → p.2.failed = none → K12.Door.atFirstBook 0 p.2 = true ∧ Sound.bookFitsB p.2.book = true ∧ p.2.book.place.size = p.2.st.oracles.size ∧ p.2.st.codes = Z.first.codes ∧ K12.Door.atFirstSeats L p.2 = true := by
  obtain ⟨pp, hR⟩ := IM.reads_of_scope hS
  have hb := IM.blocksOk_of_planOk O hF
  exact five_at_end hS O (planOk_of_blocksOk hb) (fun z => IM.debts_final hS hR O z hb) hB hL

/-- **The same in the letters of Sh.reachOwed_in_scope's premise h5.** -/
theorem h5_planOk (hS : VerifierAndGoals.InScope P = true) (hF : F.planOk = true) (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B → K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true) {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L) : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B → ∀ p : ProofFile.InstPub × S, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length p → p.2.failed = none → K12.Door.atFirstBook 0 p.2 = true ∧ Sound.bookFitsB p.2.book = true ∧ p.2.book.place.size = p.2.st.oracles.size ∧ p.2.st.codes = Z.first.codes ∧ K12.Door.atFirstSeats L p.2 = true :=
  fun Bs base A B O => five_at_end_planOk hS O hF (hB Bs base A B O) hL

end Meaning.K2

#print axioms Meaning.K2.planOk_of_blocksOk
#print axioms Meaning.K2.five_at_end_planOk
#print axioms Meaning.K2.h5_planOk
