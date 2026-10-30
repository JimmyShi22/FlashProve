-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/GoodAtPlace.lean: the kind "the code switch" (K2): under the library's head and the
opening, at a place of the kind, at the letters of the kind's lot of rows: the side that the frame
seats meets the fields fits, exact and fresh of Good, at the book that the maker returns, wherever the
kind's test on the book says yes at the place; and the bound on positions, in the words of the field
bud₁ of BudDebts. Statements with their proofs, calls.

  good_at_place    Good at the side, at the condition "never" for A and B, at every list of earlier
                   reads: fits by exactOf_at_head, exact by exactOf_at_head, fresh by freshOf_of_book
  bud_at_place     the field bud₁'s body at a member of the side

Limits. Good at "never" says nothing through its fields plays and acc. hbook is a premise here. The
head and the opening are hypotheses here; where the public files pass they are met.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ExactAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshOfBook
import Johnson.Desc.ProofFile.Honest.K2.Law.BudAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Chain Block Place)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest ProofFile.Honest.K2
open ProofFile.Honest.K2.Law (exactOf_at_head freshOf_of_book bud_at_switch)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {p : SwitchPlace}
  {W₀ Rc Xi Tr X : Type}

/-- **Good at the side of a place of the kind.** -/
theorem good_at_place (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    (hbook : ∀ q : Addr, bookFits p.sizes.codes (switchSent p.sizes p.others)
      (K2.switchFresh p.sizes p.others p.foldVars) (B.spentBy ⟨p.place, 0⟩ q)
      (B.knownBy (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) ⟨p.place, 0⟩ q) = true)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (fs : List (Fall TS)) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      Side.seated cF.blocksInOrder p.place (switchRow (coreSender freshTable) D readers
                 (lotClosing Zp Bs.G₀) p
                 (publicOk D Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link))
                 (roundsAt Zp Bs.G₀ p.place)) fs = some σ ∧
      ∀ pre, Good pre .own σ B (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) 0 0
        (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => True) (switchBud p) := by
  obtain ⟨σ, hs, hf, hE⟩ := exactOf_at_head (X := X) h O hp D readers fs 0 0
  obtain ⟨σ', hs', hF⟩ := freshOf_of_book (X := X) h O hp D readers
    (publicOk D Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link)) fs hbook
  obtain rfl : σ = σ' := Option.some.inj (hs.symm.trans hs')
  refine ⟨σ, hs, fun pre => ?_⟩
  exact
    { fits := hf
      plays := fun _ _ _ _ _ hA => hA.elim
      acc := fun _ _ _ _ _ hA => hA.elim
      exact := fun u hu ca m front ds asks _ hseen _ hd hb hh ht =>
        hE u hu ca m front ds asks trivial hseen hd hb hh ht
      fresh := hF }

/-- **The body of the field bud₁ at a member of a side of the kind.** -/
theorem bud_at_place {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {c : Chain TS ProofFile.Cl}
    {SA : ProofFile.SharedSeat} {SB : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c SA SB)
    (hpW : p ∈ ProofFile.Honest.K2.Law.placesW) {Sd : Sender} {D : RowDataOf Xi}
    {readers : Local W₀ Rc Xi Tr → Readers} {closing : Closing} {ok : Xi → Bool}
    {rounds : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)} {fs : List (Fall F.S₁)}
    {σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hσ : Side.seated F.first.blocksInOrder p.place (switchRow Sd D readers closing p ok rounds) fs = some σ)
    (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (hu : u ∈ σ.members)
    (pre t : List (Block F.S₁ F.Cl)) (n : Nat)
    (hcut : F.first.blocksInOrder = pre ++ σ.block :: t)
    (hn : n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number)
    (ρ : Draws) (hρ : ρ.due F = true) :
    switchBud p u.number ((ρ.first.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
        (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum) := by
  have hrow : σ.row = switchRow Sd D readers closing p ok rounds :=
    OnBytes.SendSim.Seat.row_of_seated hσ
  have h0 : u.number = 0 := OnBytes.SendSim.Seat.number_zero hrow u hu
  have hn' : n = (pre.flatMap (·.rounds)).length := by
    rw [hn, h0]
    rfl
  rw [hn']
  exact bud_at_switch hS hL O hpW hcut (OnBytes.SendSim.At.place_of_seated hσ) _ _ ρ hρ _

end AtFullSide.K2

#print axioms AtFullSide.K2.good_at_place
#print axioms AtFullSide.K2.bud_at_place
