-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/Shared.lean: THE DECLARED ROUNDS OF THE PROOF FILE's SHARED CHAIN ARE THE
WRITTEN ONES: of A := what `ProofFile.onlineSharedChain Z` returns: each of the twelve sub-protocols of its
flat list declares the list that the written table `listAt` (Johnson/AtFull/Rounds/ListAt.lean)
has under the sub-protocol's own name; and so the chain's declared rounds in a row
are `declProofFull.2.1` (Johnson/AtFull/ProofRows/WrittenProof.lean): the second
third of "what the sub-protocols themselves declare is the written list". Definitions, statements
and proofs. It stands beside the chain's first row (Johnson/AtFull/Desc/LaterSeats.lean:
the written parameters, the chain's cut; SharedShare.lean, SharedWhole.lean), which has each
sub-protocol's NUMBER of rounds.
WHAT IS NOT PAID, FIRST. Six hypotheses by field are left, all among the first row's: three fields
of the planner's sizes (the setting, the codes, the batch) and the three members (the parameters of
the three proximity tests that the made plan gives are the written ones). The first row's two tests
on the plan (front2, beside) are NOT wanted: no round reads them. That `onlineSharedChain` returns is a
hypothesis of the main statements (the first row shows it from the same six). That the proof file's
description has `shared := A.chain.retype` is that description's own text
(Johnson/Desc/ProofFile/Frames1.lean:226): whoever spends this on `FileDescription.roundsDeclaredByBlocks`'s second component
owes that equation. THAT THE SIX HOLD TOGETHER AT ANY PUBLIC FILES IS NOT SHOWN IN THIS FILE;
WHETHER A THEOREM ELSEWHERE SHOWS IT WAS NOT EXAMINED FOR THIS FILE: at the library's full-size
values they were evaluated true: so these statements add to no count of what is proved. Not
premises, but shown here or in the first row at the written values: that the chain's eight own
sub-protocols can be made (`back_size`, first clause); that Omega's written parameters are not the
empty ones (`piO_stages`, LaterSeats.lean). Nothing on what a sub-protocol decides. No soundness is
claimed. No example of the head is shown in this file; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are worth.

  `piU_place`, `piO_place`, `piW_place`; `piU_full`, `piO_full`, `piW_full`   WHICH LETTERS THE
      THREE MEMBERS' EQUATIONS MEAN: `Johnson.AtFull.Desc.piU`, `piO`, `piW` (LaterSeats.lean): the
      full proof's numbers, seated at the pieces 9, 10 and 2: by rfl
  `nr`, `nr_retype_flat`   a sub-protocol's name and rounds; **a chain that is carried to another
      type of claims and laid flat keeps them** (general; the fellow of `cutOf_retype_flat`)
  `shB T bs`   the test: each member's rounds are T at its own name
  `back_rounds`   **BY LEAN's KERNEL: the eleven sub-protocols behind the first pass, at the written
      values** (nine of them have rounds: 68 in all: `back_size`). Looked at with the evaluator
      first
  `front_rounds`   the table has no row under the first sub-protocol's name: so the twelfth member
      of the flat list is had
  `back_names`   the twelve names are pairwise different; `back_names_bites`: it can fail
  `back_name_bites`, `back_stage_bites`, `back_swap_bites`, `back_round_bites`   NEGATIVE TESTS,
      stated positively: the table with two names of one-round lists exchanged; one stage fewer in
      Omega's test; the two proximity tests' parameters' numbers exchanged; a round laid into a
      sub-protocol whose name has no row: the test rejects
  `shared_rounds_at`   each sub-protocol of the flat list, at the places' numbers N
  `shared_length_at`, `shared_length`   the flat list has twelve members: "for each" is not idle
  `rows_flat`   from "each member's rounds are T at its name": the rounds in a row are the names'
      lists in a row (general)
  `shared_decl_at`   the rounds in a row, through the first row's cut and
      `shared_lists`
  `shared_rounds`, `shared_lst`, `shared_decl`   **MAIN, UNDER THE SIX: at every A that
      onlineSharedChain Z returns**
  `shared_decl_whole`   the same from the first row's `hz` and its three members

-/
import Johnson.AtFull.Desc.SharedShare
import Johnson.AtFull.Rounds.ListAt
import Johnson.Desc.ProofFile.Law.Skel.SkelLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds.Shared

open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.PlanWritten
open VerifiableInference.Desc.K12.Seat (onGu onGomega onOwn)
open H2K.JointK (sharedN p14N pGu pGomega pOwn)
open Johnson.AtFull.ProofRows (declProofFull)
open Johnson.AtFull.Desc (piU piO piW p14W sharedBack shared_chain_written cut_shared_written
  later_return places_of_members)

/-! ## 0 Which letters the hypotheses mean -/

/-- The three written parameters are SEATED where the makers seat theirs: every value of
`H2U.p12FoldedOfMade m 9` stands at piece 9 of chain 2, of `p12OmegaOfMade m 10` at piece 10, of
`p12OwnOfMade m 2` at piece 2 of chain 3 (Johnson/Desc/K12/AtPlan.lean). The library's own closed
members `H2K.Member.piUFull`, `piOFull`, `piWFull` stand at the pieces 0, 1, 0: an equation to one
of THESE could be met by no public part. -/
theorem piU_place : piU.place = ⟨2, none, 9, .K12⟩ := rfl
theorem piO_place : piO.place = ⟨2, none, 10, .K12⟩ := rfl
theorem piW_place : piW.place = ⟨3, none, 2, .K12⟩ := rfl

/-- All their other fields are the FULL proof's (Johnson/Desc/K12/Law/PlacesFull.lean), not the
small proof's (PlacesSmall.lean, whose members bear the short names piU, piO, piW in another
namespace). -/
theorem piU_full : piU = { H2K.Member.piUFull with place := ⟨2, none, 9, .K12⟩ } := rfl
theorem piO_full : piO = { H2K.Member.piOFull with place := ⟨2, none, 10, .K12⟩ } := rfl
theorem piW_full : piW = { H2K.Member.piWFull with place := ⟨3, none, 2, .K12⟩ } := rfl

/-! ## 1 Two general laws -/

/-- A sub-protocol's name and its declared rounds. -/
def nr {S Cl : Type} (b : Block S Cl) : String × List Fmt.DeclaredRound := (b.name, b.rounds)

/-- **A chain that is carried to another type of claims and laid flat keeps names and rounds.** -/
theorem nr_retype_flat {S Cl Cl' : Type} (c : Chain S Cl) :
    (c.retype (Cl' := Cl')).blocksInOrder.map nr = (c.first :: c.front ++ c.back ++ [c.last]).map nr := by
  unfold Chain.blocksInOrder Chain.retype
  simp only [List.map_cons, List.map_append, List.map_map, List.flatMap_nil, List.append_nil,
    List.map_nil, List.cons_append]
  rfl

/-- From "each member's rounds are T at its name": the rounds in a row are the names' lists in a
row. -/
theorem rows_flat {S Cl : Type} {T : String → List Fmt.DeclaredRound} {bs : List (Block S Cl)}
    (h : ∀ b ∈ bs, b.rounds = T b.name) :
    bs.flatMap (·.rounds) = (bs.map (·.name)).flatMap T := by
  rw [List.flatMap_map]
  exact List.flatMap_congr h

/-! ## 2 The test, and closed facts at the written values -/

/-- The test: each member's rounds are T at its own name. -/
def shB {S Cl : Type} (T : String → List Fmt.DeclaredRound) (bs : List (Block S Cl)) : Bool :=
  bs.all fun b => decide (b.rounds = T b.name)

set_option maxRecDepth 1000000 in
/-- **BY LEAN's KERNEL: at the written values each of the eleven sub-protocols behind the first
declares the written list under its own name.** Nine names have a row in the table. Two,
"(rec_gamma)" and "joins", have none, by the table's design (a name without a row bears the empty
list): there the clause says that the sub-protocol declares no round; `back_round_bites` shows that
a round there is caught. -/
theorem back_rounds : shB Johnson.AtFull.Rounds.listAt
    (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Eleven; nine of them have rounds; 68 rounds in all. With `back_rounds`: at these nine the
table's list is not empty, so their names have a row in the table; at the two others both sides are
the empty list. The first clause buys a second thing: `Desc.K14.blocksOr` (Johnson/Desc/K14/
Blocks.lean) lays ONE sub-protocol that refuses where its eight cannot be made; then there would be
four members here, not eleven: at the written parameters that default is not taken. -/
theorem back_size :
    (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]).length = 11 ∧
    ((sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]).filter
      fun b => !b.rounds.isEmpty).length = 9 ∧
    ((sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]).flatMap
      (·.rounds)).length = 68 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The twelve names, the first sub-protocol's among them, are pairwise different: the table goes by
the name alone. -/
theorem back_names : ("the shared chain's front" ::
    (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]).map (·.name)).Nodup := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: with the name "LOC" in the first one's stead, that name stands twice. -/
theorem back_names_bites : decide (("LOC" ::
    (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]).map (·.name)).Nodup) =
      false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The table with the names "LIN point" and "LIN zeta" exchanged: their lists have one round each,
and differ: nothing is shortened. -/
theorem back_name_bites : shB
    (fun n => Johnson.AtFull.Rounds.listAt
      (if n == "LIN point" then "LIN zeta" else if n == "LIN zeta" then "LIN point" else n))
    (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- In the maker's input: one stage fewer in Omega's test: the member "the proximity test (chain 2,
piece 10)" declares other rounds. -/
theorem back_stage_bites : shB Johnson.AtFull.Rounds.listAt
    (let b := sharedBack p14W piU
      { piO with nums := { piO.nums with stages := piO.nums.stages.dropLast } }
     b ++ [Seat.last b]) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- In the maker's input: the field `nums` of the two proximity tests' parameters exchanged. Their
places, and so their names, stay: it is the rounds' side of the equation that turns. -/
theorem back_swap_bites : shB Johnson.AtFull.Rounds.listAt
    (let b := sharedBack p14W { piU with nums := piO.nums } { piO with nums := piU.nums }
     b ++ [Seat.last b]) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A round laid into "(rec_gamma)", whose name has no row in the table: the test rejects. So the
empty list under a name without a row hides no round. -/
theorem back_round_bites : shB Johnson.AtFull.Rounds.listAt
    ((sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]).map fun b =>
      if b.name == "(rec_gamma)" then { b with rounds := Johnson.AtFull.Rounds.listAt "LIN point" }
      else b) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The table has no row under the first sub-protocol's name, by its design: a name without a row
bears the empty list; and that sub-protocol declares no round. -/
theorem front_rounds : Johnson.AtFull.Rounds.listAt "the shared chain's front" = [] := by
  decide +kernel

/-! ## 3 At Z, under hypotheses by field -/

section
variable (Z : ProofFile.Pub) (N : H2U.Places4)
  (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
  (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
  (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
include hset hcodes hbatch

/-- **Each sub-protocol of the shared chain's flat list declares the written list under its own
name.** -/
theorem shared_rounds_at (nO : H2U.PlaceNums) (hO : N.O = some nO) (hU : pGu N = piU)
    (hO' : pGomega nO = piO) (hW : pOwn N = piW) (Cl' : Type) :
    ∀ b ∈ ((sharedN Z N).chain.retype (Cl' := Cl')).blocksInOrder,
      b.rounds = Johnson.AtFull.Rounds.listAt b.name := by
  intro b hb
  have hm : nr b ∈ ((sharedN Z N).chain.retype (Cl' := Cl')).blocksInOrder.map nr :=
    List.mem_map_of_mem hb
  rw [nr_retype_flat, shared_chain_written Z N hset hcodes hbatch nO hO hU hO' hW] at hm
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
  have key : x.rounds = Johnson.AtFull.Rounds.listAt x.name := by
    have hx' : x ∈ _root_.Desc.K14.frontBlock Z.p.chains ::
        (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]) := hx
    rcases List.mem_cons.1 hx' with rfl | h1
    · exact front_rounds.symm
    · exact of_decide_eq_true (List.all_eq_true.1 back_rounds x h1)
  have e1 : x.name = b.name := congrArg (·.1) e
  have e2 : x.rounds = b.rounds := congrArg (·.2) e
  rw [← e1, ← e2]
  exact key

/-- The flat list has twelve members. -/
theorem shared_length_at (nO : H2U.PlaceNums) (hO : N.O = some nO) (hU : pGu N = piU)
    (hO' : pGomega nO = piO) (hW : pOwn N = piW) (Cl' : Type) :
    ((sharedN Z N).chain.retype (Cl' := Cl')).blocksInOrder.length = 12 := by
  have h := congrArg List.length (nr_retype_flat (Cl' := Cl') (sharedN Z N).chain)
  simp only [List.length_map] at h
  rw [h, shared_chain_written Z N hset hcodes hbatch nO hO hU hO' hW]
  show (_root_.Desc.K14.frontBlock Z.p.chains ::
    (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)])).length = 12
  rw [List.length_cons, back_size.1]

/-- **The shared chain's declared rounds in a row are the written ones.** -/
theorem shared_decl_at (nO : H2U.PlaceNums) (hO : N.O = some nO) (hU : pGu N = piU)
    (hO' : pGomega nO = piO) (hW : pOwn N = piW) (Cl' : Type) :
    ((sharedN Z N).chain.retype (Cl' := Cl')).blocksInOrder.flatMap (·.rounds) = declProofFull.2.1 := by
  rw [rows_flat (shared_rounds_at Z N hset hcodes hbatch nO hO hU hO' hW Cl'),
    ← Johnson.AtFull.Rounds.shared_lists,
    ← cut_shared_written Z N hset hcodes hbatch nO hO hU hO' hW Cl']
  unfold cutOf
  rw [List.map_map]
  rfl

end

/-! ## 4 At every return of onlineSharedChain -/

section
variable {Z : ProofFile.Pub} {A : ProofFile.SharedSeat}

/-- UNDER THE SIX HYPOTHESES BY FIELD, WHICH NOTHING HERE PAYS: the flat list has twelve members. -/
theorem shared_length (hA : ProofFile.onlineSharedChain Z = some A)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₁ : H2U.p12FoldedOfMade Z.made 9 = piU) (e₂ : H2U.p12OmegaOfMade Z.made 10 = piO)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) :
    (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder.length = 12 := by
  obtain ⟨N, nO, hN, hO, hU, hO', hW⟩ := places_of_members Z.made e₁ e₂ e₃
  obtain rfl : sharedN Z N = A := Option.some.inj ((later_return Z N hN).1.symm.trans hA)
  exact shared_length_at Z N hset hcodes hbatch nO hO hU hO' hW _

/-- **MAIN, UNDER THE SIX HYPOTHESES BY FIELD, WHICH NOTHING HERE PAYS: sub-protocol by
sub-protocol.** -/
theorem shared_rounds (hA : ProofFile.onlineSharedChain Z = some A)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₁ : H2U.p12FoldedOfMade Z.made 9 = piU) (e₂ : H2U.p12OmegaOfMade Z.made 10 = piO)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) :
    ∀ b ∈ (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder,
      b.rounds = Johnson.AtFull.Rounds.listAt b.name := by
  obtain ⟨N, nO, hN, hO, hU, hO', hW⟩ := places_of_members Z.made e₁ e₂ e₃
  obtain rfl : sharedN Z N = A := Option.some.inj ((later_return Z N hN).1.symm.trans hA)
  exact shared_rounds_at Z N hset hcodes hbatch nO hO hU hO' hW _

/-- The same in the form that the law on the rounds' column spends. -/
theorem shared_lst (hA : ProofFile.onlineSharedChain Z = some A)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₁ : H2U.p12FoldedOfMade Z.made 9 = piU) (e₂ : H2U.p12OmegaOfMade Z.made 10 = piO)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) :
    ∀ b ∈ (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder,
      ProofFile.Sk.Lst Johnson.AtFull.Rounds.listAt b.name b.rounds :=
  fun b hb => Or.inr (shared_rounds hA hset hcodes hbatch e₁ e₂ e₃ b hb)

/-- **MAIN, UNDER THE SIX HYPOTHESES BY FIELD, WHICH NOTHING HERE PAYS: the shared chain's declared
rounds are the written list.** -/
theorem shared_decl (hA : ProofFile.onlineSharedChain Z = some A)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₁ : H2U.p12FoldedOfMade Z.made 9 = piU) (e₂ : H2U.p12OmegaOfMade Z.made 10 = piO)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) :
    (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder.flatMap (·.rounds) = declProofFull.2.1 := by
  obtain ⟨N, nO, hN, hO, hU, hO', hW⟩ := places_of_members Z.made e₁ e₂ e₃
  obtain rfl : sharedN Z N = A := Option.some.inj ((later_return Z N hN).1.symm.trans hA)
  exact shared_decl_at Z N hset hcodes hbatch nO hO hU hO' hW _

/-- The same from the first of the hypotheses of `shared_whole`
(Johnson/AtFull/Desc/SharedWhole.lean) and its three members. -/
theorem shared_decl_whole (hA : ProofFile.onlineSharedChain Z = some A)
    (hz : Z.p.chains.made.sized.proof = proofSizedFull)
    (m₁ : H2U.p12FoldedOfMade Z.made 9 = piU) (m₂ : H2U.p12OmegaOfMade Z.made 10 = piO)
    (m₃ : H2U.p12OwnOfMade Z.made 2 = piW) :
    (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder.flatMap (·.rounds) = declProofFull.2.1 :=
  shared_decl hA (congrArg (·.set) hz) (congrArg (·.codes) hz) (congrArg (·.batch) hz) m₁ m₂ m₃

end

end Johnson.AtFull.Rounds.Shared

#print axioms Johnson.AtFull.Rounds.Shared.piU_place
#print axioms Johnson.AtFull.Rounds.Shared.piO_place
#print axioms Johnson.AtFull.Rounds.Shared.piW_place
#print axioms Johnson.AtFull.Rounds.Shared.piU_full
#print axioms Johnson.AtFull.Rounds.Shared.piO_full
#print axioms Johnson.AtFull.Rounds.Shared.piW_full
#print axioms Johnson.AtFull.Rounds.Shared.nr_retype_flat
#print axioms Johnson.AtFull.Rounds.Shared.rows_flat
#print axioms Johnson.AtFull.Rounds.Shared.back_rounds
#print axioms Johnson.AtFull.Rounds.Shared.back_size
#print axioms Johnson.AtFull.Rounds.Shared.back_names
#print axioms Johnson.AtFull.Rounds.Shared.back_names_bites
#print axioms Johnson.AtFull.Rounds.Shared.back_name_bites
#print axioms Johnson.AtFull.Rounds.Shared.back_stage_bites
#print axioms Johnson.AtFull.Rounds.Shared.back_swap_bites
#print axioms Johnson.AtFull.Rounds.Shared.back_round_bites
#print axioms Johnson.AtFull.Rounds.Shared.front_rounds
#print axioms Johnson.AtFull.Rounds.Shared.shared_rounds_at
#print axioms Johnson.AtFull.Rounds.Shared.shared_length_at
#print axioms Johnson.AtFull.Rounds.Shared.shared_decl_at
#print axioms Johnson.AtFull.Rounds.Shared.shared_length
#print axioms Johnson.AtFull.Rounds.Shared.shared_rounds
#print axioms Johnson.AtFull.Rounds.Shared.shared_lst
#print axioms Johnson.AtFull.Rounds.Shared.shared_decl
#print axioms Johnson.AtFull.Rounds.Shared.shared_decl_whole
