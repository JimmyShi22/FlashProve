-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/EndFive.lean: FIVE FACTS ON THE VERIFIER's STATE AT EVERY REACHED LAST STATE OF THE
FIRST CHAIN THAT BEARS NO MARK: a join of laws that lie; no induction is typed here.

WHY. The shared table's constant spends five facts on the state that the first chain hands to the shared chain. Johnson/Desc/K14/Law/SharedConstReachOwed.lean states them as owed (ReachOwed | ReachInScopeOwed). That file stands over the K14 chain and descN: so the sentence is typed here in the letters of IM.Open, which seat_open gives wherever ProofFile.onlineDescription returns; EndAt₁ F p is written out: Reach 0 (F.first.blocksInOrder.map below) F.start₁ F.first.blocksInOrder.length p, at F.first = c and F.start₁ = ProofFile.startS Z.

WHAT IS SAID.
  start_noMark   where z's request passes its test the start bears no mark
  flat_358       in scope the first chain's flat list has 358 sub-protocols
  two_at_end     conjuncts 1 and 2 (the list of commitment trees is in order · its places fit), AT EVERY o, from O and hp alone
  codes_at_end   conjunct 4 (the state's codes are the plan's), in scope
  five_at_end    all five, in scope, UNDER THREE PREMISES THAT ARE SHOWN NOWHERE HERE (hp · D · hB)

THE PREMISES IN FRONT OF five_at_end, AND WHOSE EACH IS. hS: the goals' scope (that the files can be read follows from it: reads_of_scope, Johnson/IMR/MemberOfGate.lean) · O: free, by seat_open · hp: every entry of the flat list passes its test on the plan (Johnson/IMR/AtReach.lean's head says what that Bool asks; planOk_of_run gives it from one accepting run; member_of_gate, Johnson/IMR/MemberOfGate.lean, from one accepting call of the proof's gate) · D: IM.SendDebts …: what each sending sub-protocol appends to the list of commitment trees: debts, NOT ALL PAID · hB: K12.Door.sendsAreB … = true: a closed test on the list of rounds against these sendings: proved at no list · hL: the caller's own.

HOW. reach_raw (Johnson/Top/H0/Walk/Reach.lean): a state reached by the wrapped sub-protocols' steps is reached by their own. 1 | 2: atFirstBook_all | atFirstFits_all (Johnson/IMR/AtReach.lean). 4: recAll_all. 5 and 3: seats_under_test (Johnson/IMR/SendsLeft.lean) at the flat list's length: its second conjunct placesAre holds the equal counts.

What is not claimed. THE ROW's SENTENCE BINDS EVERY o : ProofFile.SecondHashFunctionArgument: here conjuncts 3, 4 and 5 stand at OnBytes.secondHashFunction alone. The tie from «onlineDescription … = .ok (descN … Z N c)» to an opening at that very Z and c, and the equation (planAt …).Q.codes = Z.first.codes, are left to the files that state the row (Johnson/Desc/K14/Law/). None of hp, D, hB is shown. No soundness.

-/
import Johnson.IMR.AtReach
import Johnson.IMR.SendsLeft
import Johnson.IMR.MemberOfGate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- Where z's request passes its test the start bears no mark. -/
theorem start_noMark (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {z : ProofFile.InstPub} (hq : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) : (ProofFile.startS Z z).failed = none := by
  unfold ProofFile.startS
  dsimp only
  rw [if_pos hq]
  have hs := pub_start h
  unfold S.startP at hs
  split at hs
  · have e := Option.some.inj hs
    rw [← e]
    rfl
  · cases hs

/-- **Conjuncts 1 and 2, at every o.** -/
theorem two_at_end (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) : ∀ p : ProofFile.InstPub × S, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length p → K12.Door.atFirstBook 0 p.2 = true ∧ Sound.bookFitsB p.2.book = true :=
  fun _ h => ⟨atFirstBook_all O hp (reach_raw h), atFirstFits_all O hp (reach_raw h)⟩

section
variable {P : VerifierAndGoals.PublicFiles}

/-- In scope the first chain's flat list has 358 sub-protocols. -/
theorem flat_358 (hS : VerifierAndGoals.InScope P = true) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : c.blocksInOrder.length = 358 := by
  obtain ⟨pp, hR⟩ := IM.reads_of_scope hS
  have e := congrArg List.length (IM.places_scope hS hR O)
  rw [List.length_map, IM.places_len] at e
  exact e

/-- **Conjunct 4, in scope.** -/
theorem codes_at_end (hS : VerifierAndGoals.InScope P = true) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) : ∀ p : ProofFile.InstPub × S, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length p → p.2.failed = none → p.2.st.codes = Z.first.codes :=
  fun _ h hu => by
    obtain ⟨pp, hR⟩ := IM.reads_of_scope hS
    exact (recAll_all hS hR O hp (reach_raw h) hu).codes

/-- **The five facts at every reached last state of the first chain that bears no mark**, in scope, under hp, D and hB, which are shown nowhere here. -/
theorem five_at_end (hS : VerifierAndGoals.InScope P = true) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (D : ∀ z : ProofFile.InstPub, IM.SendDebts 0 Z.first.codes (K12.Door.snAt Z Bs.G₀ IM.placesW) Z Bs.G₀ c (ProofFile.startS Z z)) (hB : K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true) {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L) : ∀ p : ProofFile.InstPub × S, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length p → p.2.failed = none → K12.Door.atFirstBook 0 p.2 = true ∧ Sound.bookFitsB p.2.book = true ∧ p.2.book.place.size = p.2.st.oracles.size ∧ p.2.st.codes = Z.first.codes ∧ K12.Door.atFirstSeats L p.2 = true := by
  intro p h hu
  obtain ⟨pp, hR⟩ := IM.reads_of_scope hS
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) c.blocksInOrder.length (p.1, p.2) := reach_raw h
  obtain ⟨a1, a2⟩ := two_at_end O hp p h
  have hq := reqOk_of_noMark hS hR O hr hu
  obtain ⟨-, rs, cols, f⟩ := hr.fold
  obtain ⟨b1, b2⟩ := IM.seats_under_test hS hR O p.1 (D p.1) (start_noMark O.pub hq) hB hL
    (Nat.le_of_eq (flat_358 hS O)) f
  refine ⟨a1, a2, ?_, codes_at_end hS O hp p h hu, b1⟩
  unfold placesAre at b2
  simp only [Bool.and_eq_true, beq_iff_eq] at b2
  exact b2.1.2.symm

end

end Meaning.K2

#print axioms Meaning.K2.start_noMark
#print axioms Meaning.K2.two_at_end
#print axioms Meaning.K2.flat_358
#print axioms Meaning.K2.codes_at_end
#print axioms Meaning.K2.five_at_end
