-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/ClosedAtHead354.lean:
THE LAW OF THE PROXIMITY
TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN, sub-protocol number 354: FOUR CLOSED PREMISES
OF ITS SECOND AND FIFTH TIE, AS THEOREMS UNDER THE ONE HEAD (AtMgA, MgAtAll.lean) AND TWO ENTRY
TESTS' ACCEPTS. Each is a tie to a written list and a line that Lean's kernel evaluates, with a
line beside it that shows that the evaluation can fail. Definitions, statements and proofs.
Main names (each "…_at" ends in a field of K12Left, H2K12/Owed354AtMg.lean, to
the letter):
  pubsNone_at     no public item is open at border 355, at the composed meaning's own list of extra
                  public tests: mgAll_more_base (Johnson/Desc/Sound/MgBase.lean) and pubs_355;
                  pubs_356_no: one border on, one is. NOTHING IN FRONT BUT THE HEAD.
  fence_at        the index masks' message's tree stands below the piece's base: index_at (the seat
                  is (1, 0): N0Full_seats, Johnson/P5T/PlanSeatsFull.lean) and trees_front_of (the
                  data of the first 48,237 rounds send 77 trees: roundsOfData,
                  Johnson/Desc/Sound/DataRounds.lean; roots_front_LFull,
                  Johnson/Desc/K12/Law/StretchLast.lean), at "the declared rounds are the written
                  ones" off the head's own fields (seat_in_scope, asks_written).
  indexListed_at  the listed places have the index masks' seat at the table's own number of that
                  message: indexNo_at (the number is 4: told_at, no_written) and
                  laid_of and index_full (H2K12/ClosedOfPins354.lean).
  goOn_at         the plan's numbers and lists go on with what the test's five sendings lay (goOnB,
                  Johnson/Desc/K12/Coin/GoOnTest.lean): goOnB_body, nums_written, borders_written,
                  go_written with five bent twins; five_pinned
                  (Johnson/IMR/FivePinned.lean).
PREMISES THAT STAY. W : Written354 Zp (four equations that the entry test madeRow gives:
written354_of_pins) · hm : madeRow Zp = true (goOn_at) · hc : the first chain's cut is the
written cut (cutOf cF.blocksInOrder = cutFirstFull: cut_of_row from the entry test cutRow,
Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean) · hL : the laying of the listed places returns L ·
hcd : the codes are the first chain's · hp : the test on the plan at the place (goOn_at).
NEAREST KIN. indexNo_atAll (Johnson/Desc/K1/Law/TiesAtAll.lean):
the end of indexNo_at at the head's own letter, under the head, the maker's opening and
the same two entry tests. Its file is not imported here;
whoever imports it may strike indexNo_at.
Limits. (1) THE WRITTEN CUT RESTS ON PRINTS OF LEAN's EVALUATOR (Johnson/Desc/First/CutWritten.lean,
its own Limits): no theorem says that it is the value's; the entry test compares it at a run:
indexNo_at, indexListed_at and goOn_at inherit that. (2) A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND
zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). THAT W, hm AND hc HOLD
AT ANY PUBLIC FILES IS NO THEOREM; what has been evaluated of them stands in texts of this project
that are not in this repository, not here. (3) The full size alone. (4) HERE W, hm AND hc FOLLOW
FROM NO ACCEPT OF THE VERIFIER: they are premises. The list of the proof file's entry tests
(Johnson/Desc/Laid/ProofAsks.lean) asks madeRow and cutRow, at the full size's key; the law that
reads the two off its accept (asks_pins, Johnson/Desc/Laid/ProofAsksLaw2.lean) is not imported
here.

(Where this and lean/THEOREM.md differ, the page holds.)
No soundness statement. Nothing on hiding.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.First.CutWritten
import Johnson.Desc.First.BookNumbers
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Goal.Numbers.PlanWrittenDescScope
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.Sound.Cuts
import Johnson.Desc.K12.Law.StretchLast
import Johnson.Desc.K12.Law.WrittenOfDecl
import Johnson.Desc.K12.Law.SitsChains
import Johnson.Desc.K12.Coin.GoOnTest
import Johnson.Loose.H2K12.WrittenAtSeats
import Johnson.IMR.FivePinned
import Johnson.Loose.H2K12.ClosedOfPins354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes.Maker (WholeD RDT)
open VerifiableInference.Desc (FileDescription Block Chain Place)

/-! ## 1 No public item is open at border 355 -/

set_option maxRecDepth 1000000 in
/-- By the kernel: at the closed list of extra public tests and the written lists no public item is
open at border 355. -/
theorem pubs_355 : (VerifiableInference.Desc.First.pubSets VerifiableInference.Desc.Sound.mgMore
    VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull
      true))[354 + 1]?.getD [] = [] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The line can fail: one border on, one public item is open. -/
theorem pubs_356_no : (VerifiableInference.Desc.First.pubSets VerifiableInference.Desc.Sound.mgMore
    VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull
      true))[356]?.getD [] = [.frontOk] := by decide +kernel

/-- The two spellings of the written list of the segments' sorts are one list. -/
theorem links_one : P5J.fullLinks = VerifiableInference.Desc.Sound.linksFull := by decide

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **pubsNone, under the head alone.** -/
theorem pubsNone_at (h : P5J.AtMgA o Z D r Zp Np cF x) :
    (VerifiableInference.Desc.First.pubSets (P5J.mgAtAll h).more P5J.fullLinks
      P5J.At.ps)[354 + 1]?.getD [] = [] := by
  have e : (P5J.mgAtAll h).more = VerifiableInference.Desc.Sound.mgMore :=
    VerifiableInference.Desc.Sound.mgAll_more_base h.𝔇
  have e2 : P5J.At.ps = VerifiableInference.Desc.First.flatPlacesOf P5J.fullLinks true := rfl
  rw [e, e2, links_one]
  exact pubs_355

end

/-! ## 2 The index masks' message's tree stands below the piece's base -/

/-- The trees that the data of the first n rounds send are the roots that the first n declared
rounds declare. -/
theorem nTrees_take_decl : ∀ (ds : List RDT) (rs : List Fmt.DeclaredRound),
    List.Forall₂ VerifiableInference.Desc.RoundAsG ds rs → ∀ n,
      VerifiableInference.Desc.Sound.nTrees (ds.take n) = Johnson.G.OfPlan.rootsOf (rs.take n)
  | _, _, .nil, n => by simp [VerifiableInference.Desc.Sound.nTrees, Johnson.G.OfPlan.rootsOf]
  | _, _, .cons (a := d) (b := r) (l₁ := ds) (l₂ := rs) h t, n => by
    cases n with
    | zero => simp [VerifiableInference.Desc.Sound.nTrees, Johnson.G.OfPlan.rootsOf]
    | succ n =>
      have ih := nTrees_take_decl ds rs t n
      rw [List.take_succ_cons, List.take_succ_cons, VerifiableInference.Desc.Sound.nTrees_cons, ih,
        h.2.2.2.1]
      simp [Johnson.G.OfPlan.rootsOf]

/-- The first chain's written list of rounds has 48,238 rounds or more: the test's own 33 rounds
stand in it from number 48,237 on (stretch_LFull, namesL_length:
Johnson/Desc/K12/Law/StretchLast.lean). -/
theorem first_long : 48238 ≤ H2K.Member.xsFirst.length := by
  have h := congrArg List.length (H2K.JointK.entries_of_rounds H2K.Member.stretch_LFull)
  have hn := H2K.Member.namesL_length
  unfold H2K.Member.namesL at hn
  simp only [List.length_map, List.length_take, List.length_drop] at h hn
  omega

set_option maxRecDepth 1000000 in
/-- The count 77 can fail: behind the test's own rounds the written rounds have sent 82 roots. -/
theorem roots_behind_no : H2K.Member.rootsE 0 (Johnson.G.dryProofFull.1.take 48270) = 82 := by
  decide +kernel

/-- **Where the declared rounds are the written ones, the data of the first 48,237 rounds of the
first chain send 77 trees.** -/
theorem trees_front_of {Xi : Type} (F : FileDescription Xi) (D : WholeD)
    (hD : F.data "proof file" = .ok D)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" F.roundsDeclaredByBlocks = .ok Johnson.G.dryProofFull) :
    VerifiableInference.Desc.Sound.nTrees (D.ds₁.take 48237) = 77 := by
  have hx : F.roundsDeclaredByBlocks.1.mapM (·.round []) = some H2K.Member.xsFirst :=
    (H2K.Pub.chains_of_written hW).1
  have R := (VerifiableInference.Desc.roundsOfData F "proof file" D hD).1
  have hlen : H2K.Member.xsFirst.length = F.roundsDeclaredByBlocks.1.length := by
    have := congrArg List.length (H2K.JointK.entries_of_rounds hx)
    simpa using this
  have hl := first_long
  have h1 := nTrees_take_decl _ _ R 48237
  have h2 : F.roundsDeclaredByBlocks.1.dropLast.take 48237 = F.roundsDeclaredByBlocks.1.take 48237 := by
    rw [List.dropLast_eq_take, List.take_take]
    congr 1
    omega
  have hx' : (F.roundsDeclaredByBlocks.1.take 48237 ++ F.roundsDeclaredByBlocks.1.drop 48237).mapM (·.round []) =
      some H2K.Member.xsFirst := by
    rw [List.take_append_drop]
    exact hx
  have h3 := H2K.JointK.roots_closed hx'
  rw [h1, h2, h3, List.length_take, Nat.min_eq_left (by omega)]
  exact H2K.Member.roots_front_LFull

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The index masks' message's seat in the table's numbers. -/
theorem index_at (W : Written354 Zp) : (P5J.At.N Zp cF).index = (1, 0) := by
  have e : (P5J.At.N Zp cF).index = (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).index := rfl
  rw [e, pseats_written W]
  exact (Prod.mk.inj P5T.N0Full_seats).1

/-- **fence, under the head and the four equations.** -/
theorem fence_at (h : P5J.AtMgA o Z D r Zp Np cF x) (W : Written354 Zp) :
    (P5J.At.N Zp cF).index.1 <
      VerifiableInference.Desc.Sound.nTrees ((D.at OnBytes.Slice.frS.P.T.a).ds₁.take 48237) := by
  rw [P5J.LaidAt.atDepth h.scope h.laid, index_at W, trees_front_of _ D h.laid.data
    (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope
      (LPFD.asks_written h.laid.asks)).1]
  decide

end

/-! ## 3 The listed places have the index masks' seat at the table's own number -/

/-- Two definitions of one short name give one list. -/
theorem told_same {S Cl : Type} (bs : List (Block S Cl)) :
    VerifiableInference.Desc.Sound.toldOf bs = VerifiableInference.Desc.First.toldOf bs := by
  unfold VerifiableInference.Desc.Sound.toldOf VerifiableInference.Desc.First.toldOf
  simp [List.flatMap_id]

set_option maxRecDepth 1000000 in
/-- By the kernel: counted through the trees that the written cut tells, the message at the tenant
(1, 0) has the number 4. -/
theorem no_written : VerifiableInference.Desc.First.msgNoOf VerifiableInference.Desc.First.toldCut
    (1, 0) = 4 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The line can fail: without the first tree told the number is another. -/
theorem no_written_no : VerifiableInference.Desc.First.msgNoOf
    [VerifiableInference.Desc.First.toldCut.flatten.drop 1] (1, 0) ≠ 4 := by decide +kernel

section
variable {Zp : ProofFile.Pub} {cF : Chain P5J.TS ProofFile.Cl}

/-- Where the first chain's cut is the written one, what its sub-protocols tell is the written
list. -/
theorem told_at (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
    VerifiableInference.PlanWritten.cutFirstFull) :
    P5J.At.told cF = VerifiableInference.Desc.First.toldCut :=
  (told_same cF.blocksInOrder).trans (VerifiableInference.Desc.First.told_at_written hc).2

/-- The table's own number of the index masks' message. -/
theorem indexNo_at (W : Written354 Zp) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
    VerifiableInference.PlanWritten.cutFirstFull) : (P5J.At.N Zp cF).indexNo = 4 := by
  have e : (P5J.At.N Zp cF).indexNo =
      VerifiableInference.Desc.First.msgNoOf (P5J.At.told cF) (P5J.At.N Zp cF).index := rfl
  rw [e, index_at W, told_at hc]
  exact no_written

/-- **indexListed, under the four equations and the written cut.** -/
theorem indexListed_at (W : Written354 Zp) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
    VerifiableInference.PlanWritten.cutFirstFull) (L : VerifiableInference.Desc.K12.Door.Laid)
    (hL : VerifiableInference.Desc.K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    L.places[(P5J.At.N Zp cF).indexNo]? = some (P5J.At.N Zp cF).index := by
  rw [indexNo_at W hc, index_at W, laid_of W L hL]
  exact (Prod.mk.inj index_full).1

end

/-! ## 4 The plan's numbers and lists go on with what the test's sendings lay -/

/-- goOnB's body, at four numbers and a list of sendings. -/
def goBody (t t' m m' : ℕ) (S : List (Array OnBytes.OracleNotice))
    (L : VerifiableInference.Desc.K12.Coin.Laid) (codes : OnBytes.Codes) : Bool :=
  match VerifiableInference.Desc.K12.Coin.laidFrom codes t S with
  | none => false
  | some A =>
    t' == t + A.shapes.length && m' == m + A.places.length &&
      (L.places.drop m).take A.places.length == A.places &&
      (L.shapes.drop t).take A.shapes.length == A.shapes

/-- goOnB is its body at the place's sendings, where these are not none. -/
theorem goOnB_body (N : VerifiableInference.Desc.First.Numbers) (p p' : Place)
    (π : VerifiableInference.Desc.K12.P12) (L : VerifiableInference.Desc.K12.Coin.Laid)
    (codes : OnBytes.Codes) (S : List (Array OnBytes.OracleNotice))
    (hS : VerifiableInference.Desc.K12.Coin.sendsFrom π 0 π.nums.stages.tail = S) (hne : S ≠ []) :
    VerifiableInference.Desc.K12.Coin.goOnB N p p' π L codes =
      goBody (N.treesAt (some p)) (N.treesAt (some p')) (N.msgsAt (some p)) (N.msgsAt (some p')) S L
        codes := by
  unfold VerifiableInference.Desc.K12.Coin.goOnB goBody
  cases hst : π.nums.stages with
  | nil =>
    rw [hst] at hS
    exact absurd hS.symm hne
  | cons a rest =>
    rw [hst] at hS
    have hS' : VerifiableInference.Desc.K12.Coin.sendsFrom π 0 rest = S := hS
    simp only [hS']
    cases VerifiableInference.Desc.K12.Coin.laidFrom codes (N.treesAt (some p)) S <;> rfl

set_option maxRecDepth 1000000 in
/-- By the kernel: the two places' borders in the written list of places. -/
theorem borders_written : (VerifiableInference.Desc.First.borderOf
      VerifiableInference.Desc.First.placesCut (some ⟨1, none, 2, .K12⟩),
    VerifiableInference.Desc.First.borderOf VerifiableInference.Desc.First.placesCut
      (some ⟨1, none, 3, .K13⟩)) = (354, 355) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: the trees and the messages that the written cut tells in front of the two
borders. -/
theorem nums_written : (VerifiableInference.Desc.First.treesTold
      VerifiableInference.Desc.First.toldCut 354,
    VerifiableInference.Desc.First.treesTold VerifiableInference.Desc.First.toldCut 355,
    VerifiableInference.Desc.First.msgsTold VerifiableInference.Desc.First.toldCut 354,
    VerifiableInference.Desc.First.msgsTold VerifiableInference.Desc.First.toldCut 355) =
    (77, 82, 187, 197) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The line can fail: one border earlier the counts are others. -/
theorem nums_written_no : (VerifiableInference.Desc.First.treesTold
      VerifiableInference.Desc.First.toldCut 353,
    VerifiableInference.Desc.First.msgsTold VerifiableInference.Desc.First.toldCut 353) ≠
    (77, 187) := by decide +kernel

/-- goOnB's body at the written values, as a test on what the laying of the written notices
returns. -/
def goAt (t t' m m' : ℕ) (S : List (Array OnBytes.OracleNotice))
    (f : VerifiableInference.Desc.K12.Door.Laid → VerifiableInference.Desc.K12.Door.Laid) : Bool :=
  (VerifiableInference.Desc.K12.Door.laidOf Johnson.G.codesFull2 noticesFull).any fun L =>
    goBody t t' m m' S (VerifiableInference.Desc.K12.Door.toTree (f L)) Johnson.G.codesFull2

set_option maxRecDepth 1000000 in
/-- **By the kernel: at the written values the body accepts.** -/
theorem go_written : goAt 77 82 187 197 IM.fiveW id = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Five bent twins, each rejected: one tree more behind · one message more behind · the listed
places cut at the test's front · the listed shapes cut there · no sending. -/
theorem go_written_no : goAt 77 83 187 197 IM.fiveW id = false ∧
    goAt 77 82 187 198 IM.fiveW id = false ∧
    goAt 77 82 187 197 IM.fiveW (fun L => { L with places := L.places.take 187 }) = false ∧
    goAt 77 82 187 197 IM.fiveW (fun L => { L with shapes := L.shapes.take 77 }) = false ∧
    goAt 77 82 187 197 [] id = false := by decide +kernel

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **goOn, under the head, the two entry tests' accepts and the test on the plan at the place.** -/
theorem goOn_at (h : P5J.AtMgA o Z D r Zp Np cF x) (W : Written354 Zp)
    (hm : VerifiableInference.PlanWritten.madeRow Zp = true)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull)
    (hp : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      (H2K.JointK.pL Np) : Block VerifiableInference.Desc.K12.T12 Unit).planOk = true)
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (hL : VerifiableInference.Desc.K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some L)
    (codes : OnBytes.Codes) (hcd : codes = P5J.At.cs Zp) :
    VerifiableInference.Desc.K12.Coin.goOnB (P5J.At.N Zp cF) ⟨1, none, 2, .K12⟩ ⟨1, none, 3, .K13⟩
      (H2K.JointK.pL Np) (VerifiableInference.Desc.K12.Door.toTree L) codes = true := by
  have eπ : H2U.p12OfMade Zp.made = H2K.JointK.pL Np := by
    unfold H2U.p12OfMade
    rw [h.laid.places]
    rfl
  have h5 := IM.five_pinned hm (by rw [eπ]; exact hp)
  rw [eπ] at h5
  have hne : IM.fiveW ≠ [] := fun e => by
    have h5l := IM.five_len
    rw [e] at h5l
    simp at h5l
  rw [goOnB_body _ _ _ _ _ _ IM.fiveW h5 hne]
  have eps : P5J.At.ps = VerifiableInference.Desc.First.placesCut := by
    have e2 : P5J.At.ps = VerifiableInference.Desc.First.flatPlacesOf P5J.fullLinks true := rfl
    rw [e2, links_one, VerifiableInference.Desc.First.placesCut_is]
  have et : ∀ q, (P5J.At.N Zp cF).treesAt q = VerifiableInference.Desc.First.treesTold
      VerifiableInference.Desc.First.toldCut
      (VerifiableInference.Desc.First.borderOf VerifiableInference.Desc.First.placesCut q) := by
    intro q
    have e0 : (P5J.At.N Zp cF).treesAt q = VerifiableInference.Desc.First.treesTold (P5J.At.told cF)
        (VerifiableInference.Desc.First.borderOf P5J.At.ps q) := rfl
    rw [e0, told_at hc, eps]
  have em : ∀ q, (P5J.At.N Zp cF).msgsAt q = VerifiableInference.Desc.First.msgsTold
      VerifiableInference.Desc.First.toldCut
      (VerifiableInference.Desc.First.borderOf VerifiableInference.Desc.First.placesCut q) := by
    intro q
    have e0 : (P5J.At.N Zp cF).msgsAt q = VerifiableInference.Desc.First.msgsTold (P5J.At.told cF)
        (VerifiableInference.Desc.First.borderOf P5J.At.ps q) := rfl
    rw [e0, told_at hc, eps]
  obtain ⟨b1, b2⟩ := Prod.mk.inj borders_written
  obtain ⟨n1, n234⟩ := Prod.mk.inj nums_written
  obtain ⟨n2, n34⟩ := Prod.mk.inj n234
  obtain ⟨n3, n4⟩ := Prod.mk.inj n34
  have ecs : codes = Johnson.G.codesFull2 := by
    rw [hcd]
    exact W.codes
  rw [et, et, em, em, b1, b2, n1, n2, n3, n4, ecs]
  have g := go_written
  unfold goAt at g
  rw [laid_written W L hL] at g
  exact g

end

end H2K12

#print axioms H2K12.pubs_355
#print axioms H2K12.pubs_356_no
#print axioms H2K12.pubsNone_at
#print axioms H2K12.trees_front_of
#print axioms H2K12.roots_behind_no
#print axioms H2K12.index_at
#print axioms H2K12.fence_at
#print axioms H2K12.no_written
#print axioms H2K12.no_written_no
#print axioms H2K12.indexNo_at
#print axioms H2K12.indexListed_at
#print axioms H2K12.goOnB_body
#print axioms H2K12.borders_written
#print axioms H2K12.nums_written
#print axioms H2K12.nums_written_no
#print axioms H2K12.go_written
#print axioms H2K12.go_written_no
#print axioms H2K12.goOn_at
