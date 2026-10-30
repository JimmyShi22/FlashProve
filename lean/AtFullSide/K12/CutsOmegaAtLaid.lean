-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/CutsOmegaAtLaid.lean

What it proves. Two things on the book of random values, at whatever book the maker returns
(bookWhole) at the proof file's own description, the library's written sendings and the merges that
it reads off the first chain, in the goals' scope, at the full size, at any earlier hash. (1) The
fellow at the test on G_omega of what CutsAtLaid.lean in this folder has at the test on G_u: the
public test bookCutsOmega (Johnson/Desc/ProofFile/Honest/K12/CutOfBookAt.lean) says yes at every
place record whose place is the test's, and every public data with five named numbers. (2) One coin
at three places: the round "SPLIT", the test on G_u and the test on G_omega. Five entries: the one
by which the part at "SPLIT" spends, one coin long, and the four by which the two parts of each test
carry o_sp, 216 long, each under its name. All five have one owner and one start.

Names.
  carried_written, spent_written   a list at the written list, at the maker's book.
  carried_U0_written, carried_O0_written, carried_O1_written   the written lists.
  names_U0_written, names_U1_written, names_O0_written, names_O1_written   their names.
  map_one           entry number 1 of a list, from its image.
  one_coin_at_laid  (2).
  bookCutsOmega_of_numbers   the test from two entries and five numbers: general.
  numbers_O_written   the five numbers at the library's written parameters.
  bookCutsOmega_at_laid   (1).
  bookCutsOmega_written, cutFits_O_bite   at the written parameters; a control: the senders
      exchanged, the test says no.

By what. The proofs are CutsAtLaid.lean's, with the places turned. Evaluations in Lean's kernel at
the written entries outside the first chain, behind ahead_at (TiesAtLaid.lean); he_at_laid,
carried_U_written (CutsAtLaid.lean); bookWhole_returns_written_ahead
(AtFullSide/K14/BookWholeWritten.lean), bookWhole_same_at_laid
(Johnson/Desc/ProofFile/Honest/K14/BookWholeAtHead.lean).

Limits.
- THE BOOK: that a filling's book is the maker's at these letters is a premise (hB).
  CutsAtLaid.lean's and TiesAtLaid.lean's limits stand: the full size alone; the library's written
  sendings; the merges that the maker reads off the first chain; the side library.
- ONE OWNER AND ONE START ARE ENTRIES OF A BOOK. That the coins which the frame hands at these
  places are one goes, at the four carried entries, by lend_stretch and stretch_tie
  (K12/AgreeBook.lean), which ask one count; at the split, one coin long against 216, stretch_tie
  does not apply, and cut_at (K12/CutOfBook.lean) at number 0 is what joins them. None is called
  here. That the lending returns is not shown.
- The first part's carried lists feed one_coin_at_laid alone: no law here reads them otherwise.
- CutsAtLaid.lean's limit on the library's written place record has its like: piOFull's own field
  place bears piece 1 (Johnson/Desc/K12/Law/PlacesFull.lean), not the test's: the seated record's
  place is what bookCutsOmega_at_laid asks (hp).
- The five numbers at the public data of a run are premises, as the eight are in CutsAtLaid.lean.
- Neither law that takes the test is applied here.
- One limit is raised at the written evaluations: maxRecDepth to 1000000, as in CutsAtLaid.lean.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.CutsAtLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (P12)
open ProofFile.Honest (ProverCoinCounts Addr Ahead Due bookWhole mergesByName)
open ProofFile.Honest.K14 (SendPub jobU jobOmega offsetOf dueOf takesOf place sendPlace atWritten)
open ProofFile.Honest.K12.Light (carriedOf cutFits bookCutsOmega shapeAt)
open ProofFile.Honest.K12.AtProof (placeU placeO)
open AtFullSide.K14 (rawAheadW)
open Johnson.G (proofSendsFull)
open P5J (TS)

/-- **A carried list at the maker's book is the written one**, under any reader of its entries. -/
theorem carried_written {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles}
    {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) (a : Addr)
    {β : Type} (g : Ahead → β) (v : List β)
    (hw : ((rawAheadW.filter fun e => e.spender == a).filter (!·.once)).map g = v) :
    (carriedOf Bk a).map g = v := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  unfold carriedOf
  rw [hA]
  exact hw

/-- **The entries that a part spends at the maker's book are the written ones.** -/
theorem spent_written {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) (a : Addr)
    {β : Type} (g : Ahead → β) (v : List β)
    (hw : ((rawAheadW.filter fun e => e.spender == a).filter (·.once)).map g = v) :
    ((Bk.ahead.filter fun e => e.spender == a).filter (·.once)).map g = v := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  rw [hA]
  exact hw

set_option maxRecDepth 1000000 in
/-- **At the written list the first part of the test on G_u carries o_u and o_sp.** -/
theorem carried_U0_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeU, 0⟩).filter (!·.once)).map
        (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 2, 0⟩, ⟨0, 0⟩, ⟨0, 10808⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩)] := by
  rw [ahead_at ⟨placeU, 0⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written list the first part of the test on G_omega carries o_omega and o_sp.** -/
theorem carried_O0_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeO, 0⟩).filter (!·.once)).map
        (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 5, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩)] := by
  rw [ahead_at ⟨placeO, 0⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written list the second part of the test on G_omega carries three entries**: o_omega,
o_sp, and the first part's own fresh table. -/
theorem carried_O1_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeO, 1⟩).filter (!·.once)).map
        (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 5, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨placeO, 0⟩, ⟨0, 0⟩, ⟨0, 161⟩)] := by
  rw [ahead_at ⟨placeO, 1⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The names of what the first part of the test on G_u carries. -/
theorem names_U0_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeU, 0⟩).filter (!·.once)).map (·.name) =
      ["message 0 of 2.-.2.0 to 2.-.9.0: carried", "message 1 of 2.-.5.0 to 2.-.9.0: carried"] := by
  rw [ahead_at ⟨placeU, 0⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The names of what its second part carries. -/
theorem names_U1_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeU, 1⟩).filter (!·.once)).map (·.name) =
      ["message 0 of 2.-.2.0 to 2.-.9.1: carried", "message 1 of 2.-.5.0 to 2.-.9.1: carried",
        "message 1 of 2.-.2.0 to 2.-.9.1: carried"] := by
  rw [ahead_at ⟨placeU, 1⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The names of what the first part of the test on G_omega carries. -/
theorem names_O0_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeO, 0⟩).filter (!·.once)).map (·.name) =
      ["message 0 of 2.-.5.0 to 2.-.10.0: carried",
        "message 1 of 2.-.5.0 to 2.-.10.0: carried"] := by
  rw [ahead_at ⟨placeO, 0⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The names of what its second part carries. -/
theorem names_O1_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeO, 1⟩).filter (!·.once)).map (·.name) =
      ["message 0 of 2.-.5.0 to 2.-.10.1: carried", "message 1 of 2.-.5.0 to 2.-.10.1: carried",
        "message 0 of 2.-.10.0 to 2.-.10.1: carried"] := by
  rw [ahead_at ⟨placeO, 1⟩ (by decide)]
  decide +kernel

/-- Entry number 1 of a list, from its image. -/
theorem map_one {α β : Type} (f : α → β) (l : List α) (a b : β) (t : List β)
    (h : l.map f = a :: b :: t) : (l[1]?).map f = some b := by
  rw [← List.getElem?_map, h]
  rfl

/-- **One coin at three places**: at whatever book the maker returns, in the goals' scope: the part
at "SPLIT" spends just one entry, one coin from coin 42853 of the second sending's part on; and
entry number 1 of what each of the four parts of the two tests carries bears the name of message 1
of that sending to that part, and is that owner's, from that coin on, 216 long. -/
theorem one_coin_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    ((Bk.ahead.filter fun e => e.spender == ⟨place 8, 0⟩).filter (·.once)).map
        (fun e => (e.owner, e.start, e.count)) = [(⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 1⟩)] ∧
    ((carriedOf Bk ⟨placeU, 0⟩)[1]?).map (fun e => (e.owner, e.start, e.count)) =
      some (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩) ∧
    ((carriedOf Bk ⟨placeU, 1⟩)[1]?).map (fun e => (e.owner, e.start, e.count)) =
      some (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩) ∧
    ((carriedOf Bk ⟨placeO, 0⟩)[1]?).map (fun e => (e.owner, e.start, e.count)) =
      some (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩) ∧
    ((carriedOf Bk ⟨placeO, 1⟩)[1]?).map (fun e => (e.owner, e.start, e.count)) =
      some (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩) ∧
    ((carriedOf Bk ⟨placeU, 0⟩)[1]?).map (·.name) =
      some "message 1 of 2.-.5.0 to 2.-.9.0: carried" ∧
    ((carriedOf Bk ⟨placeU, 1⟩)[1]?).map (·.name) =
      some "message 1 of 2.-.5.0 to 2.-.9.1: carried" ∧
    ((carriedOf Bk ⟨placeO, 0⟩)[1]?).map (·.name) =
      some "message 1 of 2.-.5.0 to 2.-.10.0: carried" ∧
    ((carriedOf Bk ⟨placeO, 1⟩)[1]?).map (·.name) =
      some "message 1 of 2.-.5.0 to 2.-.10.1: carried" :=
  ⟨spent_written scope L hB _ _ _ spent_split_written,
    map_one _ _ _ _ _ (carried_written scope L hB _ _ _ carried_U0_written),
    map_one _ _ _ _ _ (carried_U_at_laid scope L hB),
    map_one _ _ _ _ _ (carried_written scope L hB _ _ _ carried_O0_written),
    map_one _ _ _ _ _ (carried_written scope L hB _ _ _ carried_O1_written),
    map_one _ _ _ _ _ (carried_written scope L hB _ _ _ names_U0_written),
    map_one _ _ _ _ _ (carried_written scope L hB _ _ _ names_U1_written),
    map_one _ _ _ _ _ (carried_written scope L hB _ _ _ names_O0_written),
    map_one _ _ _ _ _ (carried_written scope L hB _ _ _ names_O1_written)⟩

/-- **bookCutsOmega from two entries and five numbers of the sending's job.** General in the book
and in the public data A. -/
theorem bookCutsOmega_of_numbers (Bk : ProverCoinCounts)
    (hc : (carriedOf Bk ⟨placeO, 1⟩).map (fun e => (e.owner, e.start, e.count)) =
      [(⟨sendPlace 5, 0⟩, ⟨0, 0⟩, ⟨0, 42853⟩), (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩),
        (⟨placeO, 0⟩, ⟨0, 0⟩, ⟨0, 161⟩)])
    (A : SendPub) (p : P12) (hp : p.place = placeO)
    (o0 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 = 0)
    (d0 : dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 0) ((jobOmega A).sort 0) = 42853)
    (o1 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 1 = 42853)
    (d1 : dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) ((jobOmega A).sort 1) = 216)
    (tO : 43069 ≤ (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).e) :
    bookCutsOmega Bk A p = true := by
  obtain ⟨e0, l1, hl, h0, hc⟩ := List.map_eq_cons_iff.1 hc
  obtain ⟨e1, l2, hl1, h1, -⟩ := List.map_eq_cons_iff.1 hc
  subst hl1
  have a0 := congrArg (·.1) h0
  have b0 := congrArg (·.2.1) h0
  have c0 := congrArg (·.2.2) h0
  have a1 := congrArg (·.1) h1
  have b1 := congrArg (·.2.1) h1
  have c1 := congrArg (·.2.2) h1
  dsimp only at a0 b0 c0 a1 b1 c1
  unfold bookCutsOmega cutFits
  rw [hp, hl]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, a0, b0, c0, a1, b1, c1,
    o0, d0, o1, d1, beq_self_eq_true, Bool.and_true, Bool.true_and, decide_eq_true_eq,
    Bool.and_eq_true]
  omega

set_option maxRecDepth 1000000 in
/-- The five numbers at the library's written parameters. Evaluations in Lean's kernel. -/
theorem numbers_O_written :
    offsetOf (jobOmega (atWritten 0)).Q.codes (jobOmega (atWritten 0)).Q.sent
        (jobOmega (atWritten 0)).sort 0 = 0 ∧
      dueOf (jobOmega (atWritten 0)).Q.codes (shapeAt (jobOmega (atWritten 0)) 0)
        ((jobOmega (atWritten 0)).sort 0) = 42853 ∧
      offsetOf (jobOmega (atWritten 0)).Q.codes (jobOmega (atWritten 0)).Q.sent
        (jobOmega (atWritten 0)).sort 1 = 42853 ∧
      dueOf (jobOmega (atWritten 0)).Q.codes (shapeAt (jobOmega (atWritten 0)) 1)
        ((jobOmega (atWritten 0)).sort 1) = 216 ∧
      43069 ≤ (takesOf (jobOmega (atWritten 0)).Q.codes (jobOmega (atWritten 0)).Q.sent
        (jobOmega (atWritten 0)).sort).e := by
  decide +kernel

/-- **bookCutsOmega at whatever book the maker returns, in the goals' scope**, at every place
record whose place is the test's, and every public data with the five numbers. -/
theorem bookCutsOmega_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (A : SendPub) (p : P12) (hp : p.place = placeO)
    (o0 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 = 0)
    (d0 : dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 0) ((jobOmega A).sort 0) = 42853)
    (o1 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 1 = 42853)
    (d1 : dueOf (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) ((jobOmega A).sort 1) = 216)
    (tO : 43069 ≤ (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort).e) :
    bookCutsOmega Bk A p = true :=
  bookCutsOmega_of_numbers Bk (carried_written scope L hB _ _ _ carried_O1_written) A p hp o0 d0 o1
    d1 tO

/-- So at the written parameters. -/
theorem bookCutsOmega_written {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (p : P12) (hp : p.place = placeO) : bookCutsOmega Bk (atWritten 0) p = true := by
  obtain ⟨n0, n1, n2, n3, n4⟩ := numbers_O_written
  exact bookCutsOmega_at_laid scope L hB _ p hp n0 n1 n2 n3 n4

/-- A control: with the sender exchanged the first limb says no, at the same book and the same
written parameters: there the entry is found, and its owner is compared. -/
theorem cutFits_O_bite {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    cutFits Bk ⟨placeO, 1⟩ 0 ⟨sendPlace 2, 0⟩ (jobU (atWritten 0)) 0 = false := by
  obtain ⟨e0, l1, hl, h0, -⟩ :=
    List.map_eq_cons_iff.1 (carried_written scope L hB _ _ _ carried_O1_written)
  have a0 : e0.owner = ⟨sendPlace 5, 0⟩ := congrArg (·.1) h0
  unfold cutFits
  rw [hl]
  simp only [List.getElem?_cons_zero, a0]
  have hne : ((⟨sendPlace 5, 0⟩ : Addr) == ⟨sendPlace 2, 0⟩) = false := by decide
  rw [hne]
  rfl

end AtFullSide.K12

#print axioms AtFullSide.K12.carried_written
#print axioms AtFullSide.K12.spent_written
#print axioms AtFullSide.K12.carried_U0_written
#print axioms AtFullSide.K12.carried_O0_written
#print axioms AtFullSide.K12.carried_O1_written
#print axioms AtFullSide.K12.names_U0_written
#print axioms AtFullSide.K12.names_U1_written
#print axioms AtFullSide.K12.names_O0_written
#print axioms AtFullSide.K12.names_O1_written
#print axioms AtFullSide.K12.map_one
#print axioms AtFullSide.K12.one_coin_at_laid
#print axioms AtFullSide.K12.bookCutsOmega_of_numbers
#print axioms AtFullSide.K12.numbers_O_written
#print axioms AtFullSide.K12.bookCutsOmega_at_laid
#print axioms AtFullSide.K12.bookCutsOmega_written
#print axioms AtFullSide.K12.cutFits_O_bite
