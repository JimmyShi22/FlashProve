-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/TiesAtJoinUnderHead.lean: the head's merge's debt by kind (`k11_exchange_by_kind`,
Johnson/Desc/ProofFile/Honest/K11/Plays/ExchangeByKind.lean) at the joined `Script` (`joinQ`,
Honest/Thread/Join.lean), at the book and the prover that `onlineProverFromPublicFiles` returns, at the inputs
`ReadyInput`, under the library's head. The list of lots is fit (`JoinFit`,
Honest/Thread/JoinFit.lean). Its jobs are K1's 52 members by written numbers (`k1MembersW`,
Honest/K1/Law/LotsAtAll.lean). The other senders' share holds the code switches' own share
(`switchShareAt`, Honest/K2/JoinShare.lean), joined to any further share O'. No definition. Lemmas;
none of the library's goals. It lies in the side library because it imports files of it.

  `base_at_head`     the maker's base returns. Nothing here spends it: it says that hb can be met
  `link24W`, `link24W_can_fail`   by Lean's kernel: a written place of the code switches stands at
                     link 24; none at link 26
  `place24_at_head`  so the plan has a switch into link 24
  `k11_exchange_under_head`   the debt by kind, at the inputs `ReadyInput`
                     (Johnson/Desc/ProofFile/Honest/Thread/ReadyInput.lean)

How the last lemma pays the hypotheses of `k11_exchange_at_join` (TiesAtJoin.lean of this folder).
  * The prover's half: from hex and ho (`halfAtAnyFillHead`, `headClaimsByPlace_at_head`,
    Honest/K11/Plays/).
  * All lots of one message agree: the field msgs of F. No other field of F is spent.
  * The opening's job stands at member 2 of the jobs, by their text.
  * The sender of the mask row's message is the switch into link 24 (`place24_at_head`). Its lot
    lies in the share (`senderLot_mem`, MaskLotCovered.lean; `share_msgs_mem`,
    Honest/K2/JoinShare.lean) and covers the merge's lot (`k11MaskLot_covered_at_zero`,
    MaskLotCoveredAtZero.lean, at the book by `book_at_atPure`), where the switch's public test says
    yes at each valid input's instance.
  * That test follows at an instance from six public tests (`publicOk_of_two`,
    Honest/K2/Law/LightAtHead.lean). Five hold under the head; the fifth is `digits_light_at_head`
    (Honest/K2/Law/DigitsLightAtHead.lean). The sixth is hD. An input of which `ReadyInput` holds
    has an instance that passes `okStart`.

What stays a hypothesis.
  * h: the library's head. hA: `onlineProverFromPublicFiles` returns. hb: Bs is what the maker's base returns
    (`base_at_head`: it returns). hb₀: b₀ is at most 346.
  * hex: some lot of the filling has, at the returned public part and ground, the halves of the
    merge's lot `headMergeLot` at the claims `headClaimsByPlace` and the reader `entryOf`. ho: every
    lot of the filling has there halves at places of other kinds than K11 alone, or these halves.
    Both are shown of no filling.
  * F: the list is fit. Shown here of no list. hP, hR: the job at member 2 has the opening's plan
    and ride.
  * hD: the light test at the reads' filling (`ReadsLight`, Honest/K2/Law/LightDebts.lean) says yes
    at each instance that passes `okStart`. Proved by nobody.

Limits. All limits of TiesAtJoin.lean, MaskLotCoveredAtZero.lean, HalfAtAnyFillStatement.lean,
JoinShare.lean and DigitsLightAtHead.lean stand. No list is laid: the jobs' three letters (J₂ and Jw
are jobs, Jl is a family of jobs), the reader wit, the further share O' and what the switches' share
lays at other members' numbers (rest) are parameters. The list seats is a parameter; by the field
whole it has every seat that the flat list declares. The merge's lot is the one whose half does not
keep its tables. The parameter c₀ stands in no hypothesis and in no end: it is handed on to the
lemmas beneath, where it is what `headMergeCoins` returns if the book lends the merge's row nothing.
The switches' data are laid at one choice of sizes (`Sz.ref`). That the thread stands at any state
is not said: where `ReadyInput` holds of no input the last lemma says nothing. Chain 0 alone. Two
closed facts by Lean's kernel, one of them a control, with two options raised. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import AtFullSide.K11.MaskLotCoveredAtZero
import AtFullSide.K11.TiesAtJoin
import Johnson.Desc.ProofFile.Honest.K11.Plays.ClaimsNIs
import Johnson.Desc.ProofFile.Honest.K11.Plays.HalfAtAnyFill
import Johnson.Desc.ProofFile.Honest.K2.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsLightAtHead
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open OnBytes.HonestTrace (Sz)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Strs Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA F0T CellsM TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.SumLaw (SumCoins)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (PlaceIn SendJob k1MembersW mem_k1MembersW mem_k1Members)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces withSwitchData switchShareAt)
open ProofFile.Honest.K2.Law (ReadsLight placesW places_at_head publicOk_of_two digits_light_at_head
  share_msgs_mem)
open ProofFile.Honest.K11

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **Under the head the maker's base returns.** -/
theorem base_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Bs, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs := by
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  exact ⟨Bs, O.made⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A written place stands at link 24. -/
theorem link24W : (placesW.any fun p => p.link == 24) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: none stands at link 26. -/
theorem link24W_can_fail : (placesW.any fun p => p.link == 26) = false := by decide +kernel

/-- **Under the head and the opening the plan has a switch into link 24.** -/
theorem place24_at_head {base : List (Block S ProofFile.Cl)}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) : ∃ p ∈ switchPlaces Zp Bs.G₀, p.link = 24 := by
  rw [places_at_head h.toAtMg O]
  obtain ⟨p, hp, e⟩ := List.any_eq_true.1 link24W
  exact ⟨p, hp, eq_of_beq e⟩

/-- **The merge's debt by kind at a fit list that holds the switches' share, at the book and the
prover that `onlineProverFromPublicFiles` returns, at the inputs `ReadyInput`.** Q is the joined `Script`, by hQ; Oth is
the switches' share joined to O', by hO; Vd is `ReadyInput`, by hV. -/
theorem k11_exchange_under_head {Rc Tr X₀ X Xi Y : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {P : OnlineProverParts Cm.Idx Rc Tr X₀ X}
    {A : OnlineProverWithDescription Cm.Idx Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (front : Nat)
    (tok : Local Cm.Idx Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local Cm.Idx Rc ProofFile.Inst Tr → PlaceIn Xi) (own₀ : Y)
    (J₂ : SendJob (PlaceIn Xi) Y) (Jl : ℕ → Bool → SendJob (PlaceIn Xi) Y)
    (Jw : SendJob (PlaceIn Xi) Y)
    (readers : Local Cm.Idx Rc ProofFile.Inst Tr → Readers)
    (rest : Nat → TreeLot A.B (Local Cm.Idx Rc ProofFile.Inst Tr))
    (O' Oth : Others A.B (Local Cm.Idx Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder front Zp Bs.G₀
      (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers rest).add O')
    (Q : Script A.B (Local Cm.Idx Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hQ : Q = joinQ cF.blocksInOrder front (fun v => VerifiableInference.OnPublicFiles.Flat.matrixOf v.w₀) tok
      (P5J.At.arr Zp) wit own₀ (k1MembersW J₂ Jl Jw) Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local Cm.Idx Rc ProofFile.Inst Tr → Prop)
    (hV : Vd = ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H)
    (Rd : Nat → Local Cm.Idx Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local Cm.Idx Rc ProofFile.Inst Tr)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay))
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (hb₀ : b₀ ≤ 346)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G =
      (headMergeLot headClaimsByPlace fun i => ⟨OnBytes.HonestTrace.entryOf i⟩).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11) ∨ M.halves A.Z A.G =
      (headMergeLot headClaimsByPlace fun i => ⟨OnBytes.HonestTrace.entryOf i⟩).halves A.Z A.G)
    (seats : List (Nat × Nat))
    (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ (k1MembersW J₂ Jl Jw) Oth)
    (hP : J₂.P = firstPar Bs.G₀.first (gpOf Zp))
    (hR : J₂.ride = K1.rideOf (K1.firstFold Bs.G₀.first))
    (hD : ∀ ξ, (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true → ReadsLight Zp Bs.G₀ ξ) :
    ∀ b q, P5J.At.ps[b]? = some q → q.kind = KindName.K11 →
      ∀ j : Item,
      j ∈ ((lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m u, u ∈ P5J.parts4 → j ≠ Item.constr m u) →
      ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b j := by
  subst hV
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hb)
  obtain ⟨p, hp, hl⟩ := place24_at_head h O
  have hh := (halfAtAnyFillHead Z D r Zp Np cF x h Cm.Idx Rc Tr X₀ X P A _ headClaimsByPlace
    (fun i => ⟨OnBytes.HonestTrace.entryOf i⟩) hb hA hex ho).2.2
  rw [headClaimsByPlace_at_head Z D r Zp Np cF x _ h hb] at hh
  subst hO
  exact k11_exchange_at_join h hA A.H front tok wit own₀ (k1MembersW J₂ Jl Jw) _ Q hQ test carryX
    item n₁ n₂ b₀ _ Rd Kp w c₀ hb hb₀ hh F.msgs
    (mem_k1MembersW.2 (Or.inl (mem_k1Members.2 (Or.inl rfl)))) hP hR
    (List.mem_append.2 (Or.inl (share_msgs_mem 0 _ _ readers _ _ _ _ _ _ _ rest hp _
      (senderLot_mem h O hp hl 0 _ readers _ _))))
    (k11MaskLot_covered_at_zero h O hb (book_at_atPure h hA) X _ _ _ readers _ hp hl _ 0 _
      fun v hv => publicOk_of_two h O (digits_light_at_head h O) (hD v.x hv.1) p hp)

end AtFullSide.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.base_at_head
#print axioms AtFullSide.K11.link24W
#print axioms AtFullSide.K11.link24W_can_fail
#print axioms AtFullSide.K11.place24_at_head
#print axioms AtFullSide.K11.k11_exchange_under_head
