-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/CutsAtLaid.lean

What it proves. Two premises on the book of random values, at whatever book the maker returns
(bookWhole) at the proof file's own description, the library's written sendings and the merges that
it reads off the first chain, in the goals' scope, at the full size, at any earlier hash:
- the part at "SPLIT" spends one entry, of the second sending's part, from coin 42853 on
  (he_at_laid): the premise he of spOneCoin_of_book (Johnson/Desc/ProofFile/Honest/K14/Holds2.lean),
  with that number in the place of its offsetOf;
- the public test bookCutsU (Johnson/Desc/ProofFile/Honest/K12/CutOfBookAt.lean) says yes at every
  place record whose place is the test's on G_u, and every public data with eight named numbers
  (bookCutsU_at_laid).

Names.
  spent_split_written, carried_U_written   the entries at the written list.
  he_at_laid, he_bite                      the first premise; at any other number it is false.
  carried_U_at_laid                        what the test's second part carries.
  bookCutsU_of_numbers                     the test from three entries and eight numbers: general.
  numbers_written                          the eight numbers at the library's written parameters.
  bookCutsU_at_laid                        the second premise.
  bookCutsU_written_bite                   at the written parameters; and where it says no.
  cutFits_bite                             a sharper control: the two senders exchanged.

By what. Evaluations in Lean's kernel at the 46 written entries outside the first chain, behind
ahead_at (TiesAtLaid.lean in this folder), and at the written parameters. Of the authors of the
honest side of the linear claim's shared rounds (K14): bookWhole_returns_written_ahead
(AtFullSide/K14/BookWholeWritten.lean), bookWhole_same_at_laid
(Johnson/Desc/ProofFile/Honest/K14/BookWholeAtHead.lean), atWritten
(Honest/K14/SharedAheadOwners.lean). The texts of carriedOf, cutFits (Honest/K12/CutOfBook.lean),
bookCutsU.

Limits.
- The eight numbers at the public data of a run (the plan's own parameters under the head) are
  premises: that tie is not made here. At the library's written parameters they are numbers_written.
- TiesAtLaid.lean's limits stand: the full size alone; the library's written sendings; the merges
  that the maker reads off the first chain; the side library. That a filling's book is the maker's
  at these letters is a premise (hB).
- The library's written place record piUFull bears piece 0 in its own field place: bookCutsU asks at
  that field, so at piUFull it says no (bookCutsU_written_bite). The seated record's place is the
  test's.
- Neither law that takes one of the two premises is applied here.
- One limit is raised at four theorems (spent_split_written, carried_U_written, numbers_written,
  bookCutsU_written_bite): maxRecDepth to 1000000.
- What it costs: on our machine Lake's whole call for this file alone took 37 s and 38 s in two
  builds, at 10.4 GB resident; TiesAtLaid.lean beneath it 152 s and 241 s in two builds.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtLaid
import Johnson.Desc.ProofFile.Honest.K12.CutOfBookAt
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places
import Johnson.Desc.ProofFile.Honest.K14.SharedAheadOwners
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (P12)
open ProofFile.Honest (ProverCoinCounts Addr Ahead Due bookWhole mergesByName)
open ProofFile.Honest.K14 (SendPub jobU jobOmega offsetOf dueOf takesOf place sendPlace atWritten)
open ProofFile.Honest.K12.Light (carriedOf cutFits bookCutsU)
open ProofFile.Honest.K12.Light (shapeAt)
open ProofFile.Honest.K12.AtProof (placeU)
open AtFullSide.K14 (rawAheadW rawShortW)
open Johnson.G (proofSendsFull)
open P5J (TS)

set_option maxRecDepth 1000000 in
/-- **At the written list of the book's entries the part at "SPLIT" spends one entry**: its owner is
the second sending's part, it starts at coin 42853 and counts one. An evaluation in Lean's kernel,
behind ahead_at. -/
theorem spent_split_written :
    ((rawAheadW.filter fun e => e.spender == ⟨place 8, 0⟩).filter (·.once)).map
        (fun e => (e.owner, e.start, e.count)) = [(⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 1⟩)] := by
  rw [ahead_at ⟨place 8, 0⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written list the second part of the test on G_u carries three entries**: o_u, o_sp, and
the fresh table that was sent with o_u. An evaluation in Lean's kernel, behind ahead_at. -/
theorem carried_U_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeU, 1⟩).filter (!·.once)).map
        (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 2, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨sendPlace 2, 0⟩, ⟨0, 10808⟩, ⟨0, 167⟩)] := by
  rw [ahead_at ⟨placeU, 1⟩ (by decide)]
  decide +kernel

/-- The premise he of spOneCoin_of_book (Honest/K14/Holds2.lean), with the number 42853 in the place
of its offsetOf: at whatever book the maker returns, in the goals' scope. -/
theorem he_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, 42853⟩ := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  intro e he hs ho
  rw [hA] at he
  have hm : (e.owner, e.start, e.count) ∈
      ((rawAheadW.filter fun e => e.spender == ⟨place 8, 0⟩).filter (·.once)).map
        (fun e => (e.owner, e.start, e.count)) :=
    List.mem_map.2 ⟨e, List.mem_filter.2
      ⟨List.mem_filter.2 ⟨he, by rw [hs]; exact beq_self_eq_true _⟩, ho⟩, rfl⟩
  rw [spent_split_written, List.mem_singleton] at hm
  exact ⟨congrArg (·.1) hm, congrArg (·.2.1) hm⟩

/-- It is not empty, and it can fail: the maker's book has such an entry, so at any other number the
sentence is false. -/
theorem he_bite {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) (n : ℕ) (hn : n ≠ 42853) :
    ¬ ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, n⟩ := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  intro H
  have hne : ((rawAheadW.filter fun e => e.spender == ⟨place 8, 0⟩).filter (·.once)) ≠ [] := by
    intro h0
    have := spent_split_written
    rw [h0] at this
    cases this
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨he1, ho⟩ := List.mem_filter.1 he
  obtain ⟨he2, hs⟩ := List.mem_filter.1 he1
  have hs' : e.spender = ⟨place 8, 0⟩ := eq_of_beq hs
  have hm : (e.owner, e.start, e.count) ∈
      ((rawAheadW.filter fun e => e.spender == ⟨place 8, 0⟩).filter (·.once)).map
        (fun e => (e.owner, e.start, e.count)) := List.mem_map.2 ⟨e, he, rfl⟩
  rw [spent_split_written, List.mem_singleton] at hm
  have e1 : e.start = ⟨0, 42853⟩ := congrArg (·.2.1) hm
  have e2 := (H e (by rw [hA]; exact he2) hs' ho).2
  rw [e1] at e2
  exact hn (congrArg (·.e) e2).symm

/-- What the second part of the test on G_u carries, at whatever book the maker returns, in the
goals' scope. -/
theorem carried_U_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    (carriedOf Bk ⟨placeU, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 2, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨sendPlace 2, 0⟩, ⟨0, 10808⟩, ⟨0, 167⟩)] := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  unfold carriedOf
  rw [hA]
  exact carried_U_written

/-- **bookCutsU from the three entries and eight numbers of the two sendings' jobs.** General in the
book and in the public data A. -/
theorem bookCutsU_of_numbers (Bk : ProverCoinCounts)
    (hc : (carriedOf Bk ⟨placeU, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 2, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨sendPlace 2, 0⟩, ⟨0, 10808⟩, ⟨0, 167⟩)])
    (A : SendPub) (p : P12) (hp : p.place = placeU)
    (o0 : offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 0 = 0)
    (d0 : dueOf (jobU A).Q.codes (shapeAt (jobU A) 0) ((jobU A).sort 0) = 10808)
    (o1 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 1 = 42853)
    (d1 : dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) ((jobOmega A).sort 1) = 216)
    (o2 : offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 1 = 10808)
    (d2 : dueOf (jobU A).Q.codes (shapeAt (jobU A) 1) ((jobU A).sort 1) = 167)
    (tU : 10975 ≤ (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort).e)
    (tO : 43069 ≤ (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).e) :
    bookCutsU Bk A p = true := by
  obtain ⟨e0, l1, hl, h0, hc⟩ := List.map_eq_cons_iff.1 hc
  obtain ⟨e1, l2, hl1, h1, hc⟩ := List.map_eq_cons_iff.1 hc
  obtain ⟨e2, l3, hl2, h2, -⟩ := List.map_eq_cons_iff.1 hc
  subst hl1 hl2
  have a0 := congrArg (·.1) h0
  have b0 := congrArg (·.2.1) h0
  have c0 := congrArg (·.2.2) h0
  have a1 := congrArg (·.1) h1
  have b1 := congrArg (·.2.1) h1
  have c1 := congrArg (·.2.2) h1
  have a2 := congrArg (·.1) h2
  have b2 := congrArg (·.2.1) h2
  have c2 := congrArg (·.2.2) h2
  dsimp only at a0 b0 c0 a1 b1 c1 a2 b2 c2
  unfold bookCutsU cutFits
  rw [hp, hl]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, a0, b0, c0, a1, b1, c1, a2, b2, c2,
    o0, d0, o1, d1, o2, d2, beq_self_eq_true, Bool.and_true, Bool.true_and, decide_eq_true_eq,
    Bool.and_eq_true]
  omega

set_option maxRecDepth 1000000 in
/-- The eight numbers at the library's written parameters. Evaluations in Lean's kernel. -/
theorem numbers_written :
    offsetOf (jobU (atWritten 0)).Q.codes (jobU (atWritten 0)).Q.sent
        (jobU (atWritten 0)).sort 0 = 0 ∧
      dueOf (jobU (atWritten 0)).Q.codes (shapeAt (jobU (atWritten 0)) 0)
        ((jobU (atWritten 0)).sort 0) = 10808 ∧
      offsetOf (jobOmega (atWritten 0)).Q.codes (jobOmega (atWritten 0)).Q.sent
        (jobOmega (atWritten 0)).sort 1 = 42853 ∧
      dueOf (jobOmega (atWritten 0)).Q.codes (shapeAt (jobOmega (atWritten 0)) 1)
        ((jobOmega (atWritten 0)).sort 1) = 216 ∧
      offsetOf (jobU (atWritten 0)).Q.codes (jobU (atWritten 0)).Q.sent
        (jobU (atWritten 0)).sort 1 = 10808 ∧
      dueOf (jobU (atWritten 0)).Q.codes (shapeAt (jobU (atWritten 0)) 1)
        ((jobU (atWritten 0)).sort 1) = 167 ∧
      10975 ≤ (takesOf (jobU (atWritten 0)).Q.codes (jobU (atWritten 0)).Q.sent
        (jobU (atWritten 0)).sort).e ∧
      43069 ≤ (takesOf (jobOmega (atWritten 0)).Q.codes (jobOmega (atWritten 0)).Q.sent
        (jobOmega (atWritten 0)).sort).e := by
  decide +kernel

/-- **bookCutsU at whatever book the maker returns, in the goals' scope**, at every place record
whose place is the test's, and every public data with the eight numbers. -/
theorem bookCutsU_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (A : SendPub) (p : P12) (hp : p.place = placeU)
    (o0 : offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 0 = 0)
    (d0 : dueOf (jobU A).Q.codes (shapeAt (jobU A) 0) ((jobU A).sort 0) = 10808)
    (o1 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 1 = 42853)
    (d1 : dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) ((jobOmega A).sort 1) = 216)
    (o2 : offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 1 = 10808)
    (d2 : dueOf (jobU A).Q.codes (shapeAt (jobU A) 1) ((jobU A).sort 1) = 167)
    (tU : 10975 ≤ (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort).e)
    (tO : 43069 ≤ (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).e) :
    bookCutsU Bk A p = true :=
  bookCutsU_of_numbers Bk (carried_U_at_laid scope L hB) A p hp o0 d0 o1 d1 o2 d2 tU tO

set_option maxRecDepth 1000000 in
/-- So at the written parameters; and the test can fail: at the library's written place record
piUFull, whose own field place says piece 0, it says no at the same book. -/
theorem bookCutsU_written_bite {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    (∀ p : P12, p.place = placeU → bookCutsU Bk (atWritten 0) p = true) ∧
      bookCutsU Bk (atWritten 0) H2K.Member.piUFull = false := by
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := numbers_written
  refine ⟨fun p hp => bookCutsU_at_laid scope L hB _ p hp n0 n1 n2 n3 n4 n5 n6 n7, ?_⟩
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  have hnil : carriedOf B₀ ⟨H2K.Member.piUFull.place, 1⟩ = [] := by
    unfold carriedOf
    rw [hA, ahead_at _ (by decide)]
    decide +kernel
  unfold bookCutsU cutFits
  rw [hnil]
  rfl

/-- A sharper control: with the two senders exchanged the first limb of bookCutsU says no, at the
same book and the same written parameters: there the entry is found, and its owner is compared. -/
theorem cutFits_bite {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    cutFits Bk ⟨placeU, 1⟩ 0 ⟨sendPlace 5, 0⟩ (jobOmega (atWritten 0)) 0 = false := by
  obtain ⟨e0, l1, hl, h0, -⟩ := List.map_eq_cons_iff.1 (carried_U_at_laid scope L hB)
  have a0 : e0.owner = ⟨sendPlace 2, 0⟩ := congrArg (·.1) h0
  unfold cutFits
  rw [hl]
  simp only [List.getElem?_cons_zero, a0]
  have hne : ((⟨sendPlace 2, 0⟩ : Addr) == ⟨sendPlace 5, 0⟩) = false := by decide
  rw [hne]
  rfl

end AtFullSide.K12

#print axioms AtFullSide.K12.spent_split_written
#print axioms AtFullSide.K12.carried_U_written
#print axioms AtFullSide.K12.he_at_laid
#print axioms AtFullSide.K12.he_bite
#print axioms AtFullSide.K12.carried_U_at_laid
#print axioms AtFullSide.K12.bookCutsU_of_numbers
#print axioms AtFullSide.K12.numbers_written
#print axioms AtFullSide.K12.bookCutsU_at_laid
#print axioms AtFullSide.K12.bookCutsU_written_bite
#print axioms AtFullSide.K12.cutFits_bite
