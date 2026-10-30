-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/Second.lean: THE LAST CHAIN's ROW FOR THE ROUNDS AT THE FULL SIZE: IF FOUR
EQUATIONS HOLD, EACH OF ITS FOUR SUB-PROTOCOLS DECLARES THE WRITTEN LIST THAT THE TABLE listAt
(Johnson/AtFull/Rounds/ListAt.lean) HAS AT ITS NAME, AND IN A ROW THEY ARE THE THIRD OF THE WRITTEN
DECLARED ROUNDS. Four closed facts by Lean's kernel, one of them a bent twin; one induction
(flat_of_lists); the rest are calls.

What the last chain's seat reads of the public part Z is said field by field, as in
Johnson/AtFull/Desc/SecondShare.lean, whose four equations are the premises here too: z.set,
z.codes, z.batch are proofSizedFull's (z := Z.p.chains.made.sized.proof) and
H2U.p12OwnOfMade Z.made 2 = piW.

  secondFlatW   the last chain at the written values, carried to the description's type of claims
      and laid flat (SecondShare.lean: four sub-protocols).
  second_rounds_closed   BY LEAN's KERNEL: each of them declares listAt of its own name.
  second_names_closed   BY LEAN's KERNEL: their names are the written cut's, in its order.
  second_rounds_bent   A BENT TWIN: with one stage fewer in the own test some sub-protocol does not
      declare its name's list.
  second_some   the fact is not idle: the four declare 30 rounds in all.
  flat_of_lists   general: sub-protocols that each declare their name's list: their rounds in a row.
  second_rounds_written, second_decl_written   so in a row the four are declProofFull.2.2
      (second_lists).
  second_flat_at   the flat list of P2Third.secondSeatOf Z N is secondFlatW, from three fields and
      pOwn N = piW.
  **second_rounds_of**   both at every B that ProofFile.onlineLastChain Z returns, from the four equations.
  second_decl_of   the second of these in the description's own words: the last third of
      (ProofFile.fileDescBy …).roundsDeclaredByBlocks.

Limits. THE FOUR EQUATIONS ARE PREMISES: nothing here shows that they hold at any public files.
declProofFull is the one of Johnson/AtFull/ProofRows/WrittenProof.lean. A name that the table has
not bears the empty list: so of a sub-protocol whose name it has not the fact says that it declares
no round: the table has ONE of the four names (the proximity test's). second_names_closed has no
bent twin here. It stands over SecondShare.lean, LaterSeats.lean beneath it, ListAt.lean and its
two fellows.
The full size alone. Raised limit: maxRecDepth 1000000. Nothing on soundness.

-/
import Johnson.AtFull.Desc.SecondShare
import Johnson.AtFull.Rounds.ListAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Rounds
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.PlanWritten
open Johnson.AtFull.Desc (secondAt piW places_of_own later_return)
open Johnson.AtFull.ProofRows (declProofFull)
open H2K.JointK (pOwn)

/-- The last chain at the written values, at the description's type of claims, laid flat. -/
def secondFlatW : List (Block Third.S₃ ProofFile.Cl) :=
  ((secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
    piW).retype (Cl' := ProofFile.Cl)).blocksInOrder

/-- **Each of the four declares the table's list at its own name.** -/
theorem second_rounds_closed :
    secondFlatW.all (fun b => decide (b.rounds = listAt b.name)) = true := by decide +kernel

/-- Their names are the written cut's, in its order. -/
theorem second_names_closed : secondFlatW.map (·.name) = cutSecondFull.map (·.1) := by
  decide +kernel

/-- A BENT TWIN: with one stage fewer in the own test some sub-protocol does not declare its name's
list. -/
theorem second_rounds_bent :
    (((secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
      { piW with nums := { piW.nums with stages := piW.nums.stages.dropLast } }).retype
        (Cl' := ProofFile.Cl)).blocksInOrder).any (fun b => !decide (b.rounds = listAt b.name)) = true := by
  decide +kernel

/-- The fact is not idle: the four declare 30 rounds in all. -/
theorem second_some : (secondFlatW.flatMap (·.rounds)).length = 30 := by decide +kernel

/-- A list of sub-protocols that each declare the table's list: their rounds in a row. -/
theorem flat_of_lists {S Cl : Type} : ∀ bs : List (Block S Cl),
    (∀ b ∈ bs, b.rounds = listAt b.name) →
      bs.flatMap (·.rounds) = (bs.map (·.name)).flatMap listAt
  | [], _ => rfl
  | b :: bs, h => by
    simp only [List.flatMap_cons, List.map_cons, h b (List.mem_cons_self ..),
      flat_of_lists bs fun c hc => h c (List.mem_cons_of_mem _ hc)]

/-- The closed fact, member by member. -/
theorem second_rounds_written : ∀ b ∈ secondFlatW, b.rounds = listAt b.name := fun b hb =>
  of_decide_eq_true (List.all_eq_true.1 second_rounds_closed b hb)

/-- **In a row they are the third of the written declared rounds.** -/
theorem second_decl_written : secondFlatW.flatMap (·.rounds) = declProofFull.2.2 := by
  rw [flat_of_lists _ second_rounds_written, second_names_closed, second_lists]

section
variable (Z : ProofFile.Pub) (N : H2U.Places4)
  (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
  (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
  (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
include hset hcodes hbatch

/-- The seat's chain, laid flat, is the written one. -/
theorem second_flat_at (hW : pOwn N = piW) :
    ((P2Third.secondSeatOf Z N).chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = secondFlatW := by
  have e : (P2Third.secondSeatOf Z N).chain =
      secondAt (Third.p₁₄Z Z.p.chains.made.sized.proof.set Z.p.chains.made.sized.proof.codes
        Z.p.chains.made.sized.proof.batch) (pOwn N) := rfl
  rw [e, hset, hcodes, hbatch, hW]
  rfl

end

/-- **At every B that the seat's maker returns: each sub-protocol's rounds, and all in a row.** -/
theorem second_rounds_of (Z : ProofFile.Pub)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) {B : ProofFile.SecondSeat}
    (r₇ : ProofFile.onlineLastChain Z = some B) :
    (∀ b ∈ (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder, b.rounds = listAt b.name) ∧
      (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder.flatMap (·.rounds) = declProofFull.2.2 := by
  obtain ⟨N, hN, hW⟩ := places_of_own Z.made e₃
  obtain rfl : P2Third.secondSeatOf Z N = B :=
    Option.some.inj ((later_return Z N hN).2.symm.trans r₇)
  have e := second_flat_at Z N hset hcodes hbatch hW
  constructor
  · intro b hb
    rw [e] at hb
    exact second_rounds_written b hb
  · rw [e]
    exact second_decl_written

/-- The same in the description's own words: the last third of what it declares. -/
theorem second_decl_of {σ : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (A : ProofFile.SharedSeat) {B : ProofFile.SecondSeat} (get : σ → First.S) (start : ProofFile.InstPub → σ)
    (c : Chain σ ProofFile.Cl)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) (r₇ : ProofFile.onlineLastChain Z = some B) :
    (ProofFile.fileDescBy o mk Z A B get start c).roundsDeclaredByBlocks.2.2 = declProofFull.2.2 :=
  (second_rounds_of Z hset hcodes hbatch e₃ r₇).2

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.second_rounds_closed
#print axioms Johnson.AtFull.Rounds.second_names_closed
#print axioms Johnson.AtFull.Rounds.second_rounds_bent
#print axioms Johnson.AtFull.Rounds.second_some
#print axioms Johnson.AtFull.Rounds.flat_of_lists
#print axioms Johnson.AtFull.Rounds.second_rounds_written
#print axioms Johnson.AtFull.Rounds.second_decl_written
#print axioms Johnson.AtFull.Rounds.second_flat_at
#print axioms Johnson.AtFull.Rounds.second_rounds_of
#print axioms Johnson.AtFull.Rounds.second_decl_of
