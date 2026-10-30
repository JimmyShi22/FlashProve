-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/SendingRoundsAtHead.lean: AT WHICH ROUND EACH TREE OF THE SHARED AND THE SECOND CHAIN
IS SENT, AT THE DESCRIPTION MADE OF PUBLIC FILES, under the library's hypothesis at the full size:
it is the round at which the written declared rounds send it. Statements with their proofs; no
definition.

Why. A thread's field fixed says after how many challenges a tree's table changes no more. The terms
that are laid for it at the two later chains read WRITTEN numbers: fixedShared
(Honest/K12/AtFile/TableShared.lean) reads the written declared rounds; lastFixed
(Honest/K12/AtFile/LastTerm.lean) is laid with the test's own count seedRound
(Honest/K12/ScriptLots.lean). The three sentences on fixed and taken that the threads' rule asks
(later_fields_at_written_taken_list, AtFullSide/HonestTrace/LaterTreesAtAnyTakenList.lean) are shown
from two equations AT THE DESCRIPTION's OWN ROUNDS. Here these two equations are shown.

  sendRound_of_entries, sentIn_of_entries   the round that sends a tree hangs on the rounds' entries
                      alone
  entries_at_head     **in each of the three chains the description's declared rounds have the
                      entries of the written declared rounds**
  sentIn_shared_at_head, sentIn_second_at_head   so sentIn (Honest/Small/FixedSent.lean) at the
                      description's rounds is sentIn at the written ones, at every number
  rounds_at_head      and each chain has as many declared rounds as the written list
  shared_fixed_is     **THE FIRST EQUATION**: where the shared thread's letter fixed is fixedShared
                      at the written rounds: fixed (.own j) = sentIn (the description's shared
                      rounds) j, at every j
  written_trees_second, trees_second_at_head   the second chain declares four trees (by the kernel,
                      off the written cut, with a control; then at the description)
  own_is              **THE SECOND EQUATION**: at each of these four: n₀ + seedRound stages j is the
                      first chain's rounds + the shared chain's rounds + sentIn (the description's
                      second rounds) j, where n₀ is the sum of these two counts and stages are the
                      written place's
  own_is_at_W         the same at the stages of the seated place of the request's own test
  later_fields_at_head   **so the three sentences hold at these terms**: a call of
                      later_fields_at_written_taken_list

By what. The verifier's test on the public files pins the description's declared rounds to the
written run's data (seat_in_scope, Johnson/Goal/Numbers/PlanWrittenDescScope.lean), the written
declared rounds give the same data (written_proof, Johnson/AtFull/ProofRows/WrittenProof.lean), and
that data has the entries of the rounds it is made of (writtenOf_entries,
Johnson/G/DataEntries.lean). The numbers: sent_last and seed_W
(Honest/K12/AtFile/TableLines.lean), both [7, 14, 20, 26]; nums_head_W
(AtFullSide/K12/RestTiesAtHeadW.lean); cuts_of_laid (Johnson/Goal/Skeleton/CutIsOfLaid.lean).

Limits.
  * h : HeadAtReturn is a hypothesis (Honest/Thread/TheFirstThread.lean).
  * THE LETTERS' VALUES ARE PREMISES: hfix, fixedIs, takenIs, hn, hst. That any thread is laid at
    them is not said here. At the named values of the letters the five are met by
    fixed_fields_at_the_letters (AtTheLetters.lean of this folder).
  * fixFirst, the like sentence on the first chain, is a premise of later_fields_at_head.
  * THE ENTRIES ALONE: that the description's declared rounds ARE the written ones (what they store
    and open too) is not said.
  * Tests on numbers. Nothing on any table, on what a run sends, or on what is hidden.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import AtFullSide.HonestTrace.LaterTreesAtAnyTakenList
import AtFullSide.K12.RestTiesAtHeadW
import Johnson.AtFull.ProofRows.WrittenProof
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableShared
import Johnson.Desc.ProofFile.Honest.K14.BookAtUHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open VerifiableInference.Desc (Chain sendRound)
open VerifiableInference.PlanWritten (cutSecondFull)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K12 (seedRound)
open ProofFile.Honest.K12.AtFile (fixedShared lastFixed takenLast sentLast sent_last seed_W)
open ProofFile.Honest.K12.AtProof (fourOf)
open H2K.Member (piWFull)
open P2Law.ProofPlan (declProofFull)
open VerifierAndGoals (InScope)
open P5J (LaidAt F0T TS)
open AtFullSide.Honest (threadThree)
open HonestTraceRun.LaterTrees (treesTo_whole later_fields_at_written_taken_list)

/-! ## 1 The round that sends a tree hangs on the entries alone -/

theorem sendRound_of_entries : ∀ (l l' : List Fmt.DeclaredRound),
    l.map (·.entry) = l'.map (·.entry) → ∀ j, sendRound l j = sendRound l' j
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: l, r' :: l', h, j => by
    simp only [List.map_cons, List.cons.injEq] at h
    unfold sendRound
    rw [h.1, sendRound_of_entries l l' h.2]

theorem sentIn_of_entries (l l' : List Fmt.DeclaredRound) (h : l.map (·.entry) = l'.map (·.entry))
    (j : Nat) : Small.sentIn l j = Small.sentIn l' j := by
  unfold Small.sentIn
  rw [sendRound_of_entries l l' h]

/-! ## 2 The entries at the description -/

section files
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **In each of the three chains the description's declared rounds have the entries of the written
declared rounds.** -/
theorem entries_at_head (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ((F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).map (·.entry) =
        declProofFull.1.map (·.entry) ∧
      ((F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).map (·.entry) =
        declProofFull.2.1.map (·.entry) ∧
      ((F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)).map (·.entry) =
        declProofFull.2.2.map (·.entry) := by
  have hw := (VerifiableInference.PlanWritten.seat_in_scope _ _ Z scope
    (LPFD.asks_written L.asks)).1
  have a := Johnson.G.OfPlan.writtenOf_entries hw
  have b := Johnson.G.OfPlan.writtenOf_entries Johnson.AtFull.ProofRows.written_proof
  exact ⟨a.1.symm.trans b.1, a.2.1.symm.trans b.2.1, a.2.2.symm.trans b.2.2⟩

end files

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A)

theorem sentIn_shared_at_head (j : Nat) :
    Small.sentIn (h.description.shared.blocksInOrder.flatMap (·.rounds)) j =
      Small.sentIn declProofFull.2.1 j :=
  sentIn_of_entries _ _ (entries_at_head h.head.toAtMg.scope h.head.toAtMg.laid).2.1 j

theorem sentIn_second_at_head (j : Nat) :
    Small.sentIn (h.description.second.blocksInOrder.flatMap (·.rounds)) j =
      Small.sentIn declProofFull.2.2 j :=
  sentIn_of_entries _ _ (entries_at_head h.head.toAtMg.scope h.head.toAtMg.laid).2.2 j

/-- Each chain has as many declared rounds as the written list. -/
theorem rounds_at_head :
    roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length = declProofFull.1.length ∧
      roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length =
        declProofFull.2.1.length ∧
      roundsTo h.description.second.blocksInOrder h.description.second.blocksInOrder.length =
        declProofFull.2.2.length := by
  obtain ⟨e1, e2, e3⟩ := entries_at_head h.head.toAtMg.scope h.head.toAtMg.laid
  have l1 := congrArg List.length e1
  have l2 := congrArg List.length e2
  have l3 := congrArg List.length e3
  rw [List.length_map, List.length_map] at l1 l2 l3
  unfold roundsTo declsTo
  rw [List.take_length, List.take_length, List.take_length]
  exact ⟨l1, l2, l3⟩

/-! ## 3 The first equation -/

/-- **Where the shared thread's letter fixed is fixedShared at the written rounds, it is sentIn at
the description's own shared rounds**, at every number. -/
theorem shared_fixed_is (later : LaterLetters A)
    (hfix : later.fixed = fixedShared declProofFull.2.1) (j : Nat) :
    later.fixed (.own j) = Small.sentIn (h.description.shared.blocksInOrder.flatMap (·.rounds)) j := by
  rw [hfix, sentIn_shared_at_head h j]
  rfl

/-! ## 4 The second equation -/

set_option maxRecDepth 1000000 in
/-- By the kernel: the second chain's written cut tells four trees. The second clause is a control:
its first two rows tell none. -/
theorem written_trees_second :
    (cutSecondFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).sum = 4 ∧
      ((cutSecondFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).take 2).sum = 0 := by
  decide +kernel

theorem trees_second_at_head :
    treesTo h.description.second.blocksInOrder h.description.second.blocksInOrder.length = 4 := by
  obtain ⟨-, -, c3⟩ := P5J.cuts_of_laid h.head.toAtMg.scope h.head.toAtMg.laid
  rw [treesTo_whole, c3]
  exact written_trees_second.1

/-- **At each of the second chain's four trees: the test's own count, behind the two earlier chains'
rounds, is sentIn at the description's own second rounds, behind the same.** -/
theorem own_is {n₀ : Nat} {stages : List Fmt.M1.Stage}
    (hn : n₀ = roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
      roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length)
    (hst : stages = piWFull.nums.stages) :
    ∀ j, j < treesTo h.description.second.blocksInOrder h.description.second.blocksInOrder.length →
      n₀ + seedRound stages j =
        roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
          roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length +
          Small.sentIn (h.description.second.blocksInOrder.flatMap (·.rounds)) j := by
  intro j hj
  rw [trees_second_at_head h] at hj
  have e : (List.range 4).map (seedRound piWFull.nums.stages) =
      (List.range 4).map (Small.sentIn declProofFull.2.2) := seed_W.trans sent_last.symm
  have ej := List.map_inj_left.1 e j (List.mem_range.2 hj)
  rw [hn, hst, sentIn_second_at_head h j, ej]

/-- The same at the stages of the seated place of the request's own test. -/
theorem own_is_at_W {n₀ : Nat}
    (hn : n₀ = roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
      roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length) :
    ∀ j, j < treesTo h.description.second.blocksInOrder h.description.second.blocksInOrder.length →
      n₀ + seedRound (fourOf h.places).W.nums.stages j =
        roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
          roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length +
          Small.sentIn (h.description.second.blocksInOrder.flatMap (·.rounds)) j :=
  own_is h hn (congrArg (·.stages) (ProofFile.Honest.K12.Light.nums_head_W h.head.toAtMg))

/-! ## 5 The three sentences at these terms -/

variable [Inhabited TS] [Inhabited Desc.K14.St]

/-- **The three sentences on fixed and taken at the two later chains, at the written terms.** The
letters' values (hfix, fixedIs, takenIs, hn, hst) and the like sentence on the first chain
(fixFirst) are premises. -/
theorem later_fields_at_head (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
    (later : LaterLetters A) (lastLetters : LastLetters A)
    (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    {n₀ : Nat} {stages : List Fmt.M1.Stage}
    (hfix : later.fixed = fixedShared declProofFull.2.1)
    (fixedIs : lastLetters.fixed =
      lastFixed (roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length)
        first.script.fixed later.fixed fun τ => n₀ + seedRound stages τ)
    (hn : n₀ = roundsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length +
      roundsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length)
    (hst : stages = piWFull.nums.stages)
    (takenIs : lastLetters.taken = takenLast)
    (fixFirst : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      first.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    (∀ b, b ≤ h.description.shared.blocksInOrder.length → ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      (sharedParts h later).fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b) ∧
    (∀ b, b ≤ h.description.second.blocksInOrder.length →
      ∀ σ ∈ (threadThree h first reads (lastParts h first lastLetters) R).hand b,
      (threadThree h first reads (lastParts h first lastLetters) R).fixed σ ≤
        (threadThree h first reads (lastParts h first lastLetters) R).front +
          roundsTo
            (threadThree h first reads (lastParts h first lastLetters) R).bs b) ∧
    ∀ σ ∈ (lastParts h first lastLetters).taken, ∃ c j, σ = Fmt.TreeSource.taken c j :=
  later_fields_at_written_taken_list h first reads later lastLetters R
    (fun j _ => shared_fixed_is h later hfix j) fixedIs (own_is h hn hst) takenIs fixFirst

end AtFullSide.K14

#print axioms AtFullSide.K14.sendRound_of_entries
#print axioms AtFullSide.K14.sentIn_of_entries
#print axioms AtFullSide.K14.entries_at_head
#print axioms AtFullSide.K14.sentIn_shared_at_head
#print axioms AtFullSide.K14.sentIn_second_at_head
#print axioms AtFullSide.K14.rounds_at_head
#print axioms AtFullSide.K14.shared_fixed_is
#print axioms AtFullSide.K14.written_trees_second
#print axioms AtFullSide.K14.trees_second_at_head
#print axioms AtFullSide.K14.own_is
#print axioms AtFullSide.K14.own_is_at_W
#print axioms AtFullSide.K14.later_fields_at_head
