-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtBook.lean: CONDITIONAL: on hS, hR, L and hA.
`Good` (Honest/Side.lean) at every row of K4's lot with its simulators (`k4SLot`, Law/SLot.lean) at
the book and the public data that the maker returns, general in the filling. hS, hR, L: T3's own
premises on the public files. Statements and proofs.

  `noneSpent_of_nil`   the premise on the book from the form of `bookWhole_spent_nil`
      (Honest/BookOwners.lean).
  `atPure_book_at_laid`, `atPure_pub_at_laid`, `atPure_ground_at_laid`   the maker's book, public part
      and ground: `atPure_book_at_head` (Honest/K14/AtPureBookAtHead.lean), `atPure_pub` and
      `atPure_ground` (Law/HgAtPure.lean) under `LaidAt` and the scope alone.
  `k4_good_at_maker`   **`Good` at a row of the lot, at the maker's book.**

Limits. Those of Law/ExactFresh/AtLot.lean, of which nothing is taken back: A := B := False, so plays
and acc hold for nothing; fresh IS AN IDENTITY: the maker's book spends no coin of K4's parts: THAT IS
NOT FRESHNESS OF THE RUNS THAT K4 SPENDS, WHICH IS THE DEBT OF THEIR OWNERS, the sender of each
segment's mask row and the sender of the index-mask message. THE FILLING IS A LETTER: that the filling
lays these rows is another statement, as an equation of halves at one public part and ground: in the
filling K4's lot reads the index through the public part, so no equation of lots holds
(`k4SLot_toHLot`, Law/SLot.lean; `k4_lot_at_widerFill_through`, Law/LotThrough.lean). Kin:
`freshMember_of_no_coin` (Honest/Small/FreshNoCoin.lean, the hash build's) has the field fresh at a
part for which the book's tables have no coin, without `noneSpent`. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookOwners
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Block)
open P5J (TS LaidAt)
open ProofFile.Honest.Small (noneSpent)

/-- Where no entry spends an owner's coins for any spender, `noneSpent` says yes. -/
theorem noneSpent_of_nil {B : ProverCoinCounts} {o : Addr} (h : ∀ q, B.spentBy o q = []) :
    noneSpent B o = true := by
  refine List.all_eq_true.2 fun e he => ?_
  cases ho : e.once with
  | false => rfl
  | true =>
    cases hw : e.owner == o with
    | false => rfl
    | true =>
      have hm : e ∈ B.spentBy o e.spender := List.mem_filter.2 ⟨he, by simp [hw, ho]⟩
      rw [h e.spender] at hm
      cases hm

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {W₀ Rc Tr X₀ X' : Type}

/-- The maker's public part is the one that `LaidAt` opens. -/
theorem atPure_pub_at_laid (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) : A.Z = Zp :=
  Except.ok.inj ((atPure_ok hA).1.symm.trans L.pub)

/-- The maker's ground is the one that is made of that public part. -/
theorem atPure_ground_at_laid (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G :=
  atPure_pub_at_laid L hA ▸ (atPure_ok hA).2.1

/-- The proof of `atPure_book_at_head` (Honest/K14/AtPureBookAtHead.lean), which reads of its head
the scope and `LaidAt` alone. -/
theorem atPure_book_at_laid (hS : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok A.B := by
  obtain ⟨k0, k1, k2, e, p0, p1, p2, hs, hb⟩ := ProofFile.Honest.atPure_book hA
  obtain ⟨-, -, hF, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (hF.symm.trans L.value)
  obtain ⟨En, hEn⟩ := Johnson.AtFull.Sends.sendsWhole_all
  have h1 := VerifiableInference.Desc.LinkJoin.sends_tie L.pub hs
  have h2 := hEn _ (VerifiableInference.PlanWritten.Joined.made_in_scope hS L.pub
    (P5J.pins_of_laid hS L).1)
  have hl := Except.ok.inj (h1.symm.trans h2)
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := hl
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope hS L.pub (P5J.pins_of_laid hS L).1]
  rw [eF] at hb
  exact hb

/-- CONDITIONAL: on hS, hR, L and hA. **`Good` AT A ROW OF K4's LOT WITH ITS SIMULATORS, AT THE BOOK
THAT THE MAKER RETURNS**, at the side that `Side.seated` makes of the first chain at whatever falls,
at every pre, at A := B := False. General in the filling. -/
theorem k4_good_at_maker (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₁ Rc₁ Tr₁ X₁ : Type} (cells : Tr₁ → Cells) (weights : W₁ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    {row : Unlettered (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) X₁ ProofFile.Inst}
    (hr : row ∈ (k4SLot cells weights look).rows A.Z A.G) {fs : List (Fall TS)}
    {σ : Side TS ProofFile.Cl (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) X₁ ProofFile.Inst}
    (hσ : Side.seated cF.blocksInOrder row.place row.row fs = some σ)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) ProofFile.Inst)
    (ord : List Place) (chain firstTree : Nat) :
    Good pre φ σ A.B ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) row.On
      row.bud := by
  have hB := atPure_book_at_laid hS L hA
  have hp := Johnson.RunOne.Sound.placesOk_of_planOk _ L.planOk
  rw [atPure_pub_at_laid L hA] at hr
  exact k4_good_lot hS hR L (atPure_ground_at_laid L hA) cells weights look hr hσ pre φ A.B ord chain
    firstTree fun b hb hn j => noneSpent_of_nil fun q => bookWhole_spent_nil hB hp hb hn j q

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.noneSpent_of_nil
#print axioms ProofFile.Honest.K4.ExactFresh.atPure_book_at_laid
#print axioms ProofFile.Honest.K4.ExactFresh.k4_good_at_maker
