-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/ColumnsAtTheBook.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the place
W): AT THE MAKER's WRITTEN BOOK, AT THE COINS THAT THE FRAME LENDS THE TEST's PAIR OF PARTS, THE
COLUMNS OF THE JOB's TREES 0 AND 1 ARE THE TWO SENDERS' OWN WRITTEN COLUMNS AT THE SENDERS' OWN
COINS.

WHAT IT IS NOT.
  * It does not say what a thread's table is: so it is not yet "the job's trees are the tables taken
    over". The senders' data is read at the test's own front.
  * hB, that the book is the one made of the written description, is a premise; so are the lending
    (lent) and the two senders' own cuts (cutIndex, cutW): that a book covers them is not shown
    here.
  * The job is any job on three members of which the first two are messages of sendings at the
    written plans parGF and parWF and the written rides, at the addresses senderI and senderW, at
    the place W. That a filling's job is of that make is a premise (the equations and fits).
  * It is no statement on a tree's depth.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; two theorems.

  countOfTheFreshMessage  a message that is a stage's fresh table has as many coins over the
                          extension field as the test's fresh table
  columnsAtTheBook        **the statement**: tree 0's column is col parGF … 1 x, tree 1's is
                          col parWF … 0 x, at the rows that the senders' own coins make

CALLED. columnsOfTwoSentMembers (K12/Part4/ColumnsOfJobW.lean); noCoinInFrontOfTheMask
(K12/Part4/FreshTableOfASending.lean). Of other authors: members_held, fresh_held
(AtFullSide/K12/HeldAtHeadW.lean); lendRow_second (K12/TableOfRun.lean); col_first, col_W
(AtFullSide/K12/FirstArmsK1.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.ColumnsOfJobW
import Johnson.Desc.ProofFile.Honest.K12.TableOfRun
import AtFullSide.K12.HeldAtHeadW
import AtFullSide.K12.FirstArmsK1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Part4
open Johnson.Prover.Send (shapeAt col)
open Fmt.M1 (Stage)
open VerifiableInference.Desc (K1.Par)
open VerifiableInference.Desc.K1 (parGF parWF)
open ProofFile.Honest.K12.Light (ManyJob Mem)
open ProofFile.Honest.K12.AtProof (memK1 senderI senderW placeW)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **A message that is a stage's fresh table has as many coins over the extension field as the
test's fresh table.** -/
theorem countOfTheFreshMessage {s : Stage} {P : K1.Par} {ride : ℕ → Option K1.Ride} {k : ℕ}
    (fits : RidesAtTheStage s P ride k) :
    (K1.dueMsg P.codes (shapeAt P k) (ride k)).e = dueFresh s := by
  obtain ⟨inFront, maskCoins⟩ := noCoinInFrontOfTheMask fits
  have tails : (K1.stepsOf P.codes (shapeAt P k) (ride k)).maskTails = 2 ^ s.h * s.Z.r := by
    show (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).r = _
    rw [fits.maskRows, show (P.codes.mask.getD (shapeAt P k).maskCode default).r = s.Z.r from
      congrArg Fmt.M1.Code.r fits.code]
  unfold K1.dueMsg dueFresh
  split
  · show _ + _ + _ = _
    rw [inFront, maskCoins, tails, Nat.zero_add]
  · show _ + _ = _
    rw [maskCoins, tails]

variable {V W X WI WW : Type} {Bk : ProverCoinCounts}

/-- **At the maker's book, at the coins lent, the two trees' columns are the senders' written
columns at the senders' own coins.** dataI, dataW, firstI, firstW: the two sendings' jobs at the
written plans and rides. f0, f1, mC: the rest of the job's members. -/
theorem columnsAtTheBook
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) (B : ManyJob W X) (firstI firstW : ℕ)
    (dataI : WI → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (dataW : WW → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (liftI : W → WI) (liftW : W → WW) (f0 f1 : Option ℕ × Option ℕ) (mC : Mem W X)
    (members : B.mems =
      [memK1 ⟨parGF, firstI, rideGF, dataI⟩ liftI senderI (parGF.sent.size - 1) f0,
        memK1 ⟨parWF, firstW, rideWF, dataW⟩ liftW senderW 0 f1, mC]) {depth0 depth1 : ℕ}
    (tree0 : B.trees[0]? = some (depth0, [.mask 0]))
    (tree1 : B.trees[1]? = some (depth1, [.main 1, .mask 1, .fresh]))
    (fits : SentMembersFit B.s₀ parGF parWF rideWF f0 f1) (atW : B.p.place = placeW)
    (k : Coins Bk)
    (c : RowCoins [(firstPart B.toRun.toTest : Part V W X), restPart B.toRun.toTest])
    (lent : lendRow Bk (Bk.rowsOf 2) (k.look 2) B.p.place
      [(firstPart B.toRun.toTest : Part V W X), restPart B.toRun.toTest] 0 = .ok c)
    {cI : Cs (K1.dueR parGF rideGF)}
    (cutIndex : (k.look 0 senderI).2.cut ⟨0, 0⟩ (K1.dueR parGF rideGF) = some cI)
    {cW : Cs (K1.dueR parWF rideWF)}
    (cutW : (k.look 0 senderW).2.cut ⟨0, 0⟩ (K1.dueR parWF rideWF) = some cW)
    (w : W) (fr : Front X) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr (restCoins B.toRun.toTest c.2.1).mem
        (B.toRun.toTest.first w fr (restCoins B.toRun.toTest c.2.1))).getD 0
        (0, fun _ => [])).2 x =
      col parGF (K1.rowsR parGF rideGF (dataI (liftI w) fr) cI) 1 x ∧
    ((B.toRun.toTest.trees₀ w fr (restCoins B.toRun.toTest c.2.1).mem
        (B.toRun.toTest.first w fr (restCoins B.toRun.toTest c.2.1))).getD 1
        (0, fun _ => [])).2 x =
      col parWF (K1.rowsR parWF rideWF (dataW (liftW w) fr) cW) 0 x := by
  rw [atW] at lent
  have second := lendRow_second lent
  obtain ⟨heldIndex, heldW⟩ := members_held hB (j := 1) (by simp) k second
  obtain ⟨heldIndexF, heldIndexE⟩ := heldIndex cutIndex
  obtain ⟨heldWF, heldWE⟩ := heldW cutW
  obtain ⟨-, heldFresh⟩ := fresh_held hB k second cutW
  have three : B.toRun.toTest.members.length = 3 := by
    show (B.mems.map (·.sent)).length = 3
    rw [members]
    rfl
  have hide : (restCoins B.toRun.toTest c.2.1).hide =
      (stretches (restPart (V := V) B.toRun.toTest).carries c.2.1.2.2 3).e := by
    show (stretches _ c.2.1.2.2 B.toRun.toTest.members.length).e = _
    rw [three]
  rw [col_first, col_W, ← List.append_assoc]
  exact columnsOfTwoSentMembers B ⟨parGF, firstI, rideGF, dataI⟩ ⟨parWF, firstW, rideWF, dataW⟩
    liftI liftW senderI senderW f0 f1 mC members tree0 tree1 fits w fr
    (restCoins B.toRun.toTest c.2.1) rfl cI cW heldIndexF heldIndexE heldWF heldWE
    (fun i below => by
      rw [hide]
      exact heldFresh i (by rw [countOfTheFreshMessage fits.fresh]; exact below)) x

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.countOfTheFreshMessage
#print axioms AtFullSide.K12.Part4.columnsAtTheBook
