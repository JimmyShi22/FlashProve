-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopySharedAtHead.lean: the kind "the code switch" (K2): THE
THREE LAWS OF Honest/K2/Law/CopySharedAtSegment.lean (the rows that a switch lays anew of a message
that a sender of the kind K1 sent are that sender's own rows) AT THE PLAN's OWN SENDERS: under the
library's hypothesis on the public files and the opening THEIR SIX PUBLIC PREMISES ARE PAID, and the
sender's plan and ride are named. THEIR OTHER PREMISES STAY: see the Limits. Statements with their
proofs: joins; no definition.

  `copyShared_first_at_head`   a message of the first segment, in front of the fold's mask: the
                    opening's message of the same number
  `copyShared_mask_at_head`   the first segment's fold's fresh mask: the opening's message of the
                    same number, which rides
  `copyShared_later_at_head`   a message behind a segment's first sending: message 0 of its link's
                    "reads" (q = 0) or "digits" (q = 1)

By: `copyShared_at_first`, `copyShared_at_mask`, `copyShared_at_later` (CopySharedAtSegment.lean) ·
`first_ties_at_head`, `mask_tie_at_head`, `later_ties_at_head` (Honest/K2/Law/K1SendersTies.lean),
of another author: each called once.

Limits. WHAT STAYS A PREMISE: hc: the switch is handed its coins · ho: the sender's cut of the run's
coins · he, t1, t2, t3: the book's entry for the carried stretch: its owner, start and count · hdat:
the sender's filling is the switch's · hR: the segment's rows are laid: where they are not laid
nothing is said · hS, hn, hy: which segment and message · hi: the entry's number. o, the sender's
address, is a letter, bound by ho and t1; P and ρ, the sender's plan and ride, are letters bound by
the equations hP and hρ. The rows, not the texts, nor the tables. WHICH ROWS ARE LAID ANEW: no
sentence on what a coin is for. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopySharedAtSegment
import Johnson.Desc.ProofFile.Honest.K2.Law.K1SendersTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left zeroG)
open VerifiableInference.Desc.K1 (firstPar gpOf parL)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Bk : ProverCoinCounts}
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **A MESSAGE OF THE FIRST SEGMENT, IN FRONT OF THE FOLD's MASK.** n: its number there, and in the
opening's sending. -/
theorem copyShared_first_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      withFresh = .ok R) {n : Nat} (hn : n < (Sg.sent.headD #[]).size - 1)
    {P : VerifiableInference.Desc.K1.Par} (hP : firstPar Bs.G₀.first (gpOf Zp) = P)
    {ρ : Nat → Option K1.Ride} (hρ : K1.rideOf (K1.firstFold Bs.G₀.first) = ρ)
    (o : Addr) {cs : Cs (K1.dueR P ρ)}
    (ho : K1.lentCut k ch o (K1.dueR P ρ) = some cs) (e : Ahead) {i : Nat} (hi : i = b₀ + n)
    (he : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e)
    (t1 : e.owner = o) (t2 : e.start = K1.startR P ρ n)
    (t3 : e.count = K1.dueMsg P.codes (shapeAt P n) (ρ n))
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK n = asShared (shapeAt P n) (dataAtOf Sg prev own n)) :
    R.rows[n]? = some (K1.rowsR P ρ dataK cs n) := by
  subst hP hρ
  have T := first_ties_at_head h O hS hn
  exact copyShared_at_first ch p k c hc hR hn _ _ o ho T.hq T.hc T.hs T.fits T.hw T.hride e hi he
    t1 t2 t3 dataK hdat

/-- **THE FIRST SEGMENT's FOLD's FRESH MASK.** -/
theorem copyShared_mask_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      true = .ok R)
    {P : VerifiableInference.Desc.K1.Par} (hP : firstPar Bs.G₀.first (gpOf Zp) = P)
    {ρ : Nat → Option K1.Ride} (hρ : K1.rideOf (K1.firstFold Bs.G₀.first) = ρ)
    (o : Addr) {cs : Cs (K1.dueR P ρ)}
    (ho : K1.lentCut k ch o (K1.dueR P ρ) = some cs) (e : Ahead) {i : Nat}
    (hi : i = b₀ + ((Sg.sent.headD #[]).size - 1))
    (he : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e)
    (t1 : e.owner = o) (t2 : e.start = K1.startR P ρ ((Sg.sent.headD #[]).size - 1))
    (t3 : e.count = K1.dueMsg P.codes (shapeAt P ((Sg.sent.headD #[]).size - 1))
      (ρ ((Sg.sent.headD #[]).size - 1)))
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK ((Sg.sent.headD #[]).size - 1) =
      asShared (shapeAt P ((Sg.sent.headD #[]).size - 1)) fun _ _ => zeroG) :
    R.fresh = some (K1.rowsR P ρ dataK cs ((Sg.sent.headD #[]).size - 1)) := by
  subst hP hρ
  have T := mask_tie_at_head h O hS
  exact copyShared_at_mask ch p k c hc hR _ _ o ho T.hq T.hc T.hs T.fits T.hw T.hride e hi he
    t1 t2 t3 dataK hdat

/-- **A MESSAGE BEHIND A SEGMENT's FIRST SENDING.** m: the segment. q: its number among these: 0:
the "reads"; 1: the "digits". -/
theorem copyShared_later_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {m : Nat} {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      withFresh = .ok R) {q : Nat} {y : OnBytes.OracleNotice}
    (hy : ((Sg.sent.drop 1).flatMap (·.toList))[q]? = some y)
    {P : VerifiableInference.Desc.K1.Par} (hP : parL Zp Bs.G₀ m (q == 1) = P)
    {ρ : Nat → Option K1.Ride} (hρ : K1.rideOf none = ρ)
    (o : Addr) {cs : Cs (K1.dueR P ρ)}
    (ho : K1.lentCut k ch o (K1.dueR P ρ) = some cs) (e : Ahead) {i : Nat}
    (hi : i = b₀ + ((Sg.sent.headD #[]).size - 1) + (if withFresh then 1 else 0) + q)
    (he : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e)
    (t1 : e.owner = o) (t2 : e.start = K1.startR P ρ 0)
    (t3 : e.count = K1.dueMsg P.codes (shapeAt P 0) (ρ 0))
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK 0 = asShared (shapeAt P 0) (own ((Sg.sent.headD #[]).size - 1 -
      (if prev.isSome then 1 + Sg.sizes.kept.length else 0) + q))) :
    R.rows[(Sg.sent.headD #[]).size - 1 + q]? = some (K1.rowsR P ρ dataK cs 0) := by
  subst hP hρ
  have T := (later_ties_at_head h O hS).2 q y hy
  exact copyShared_at_later ch p k c hc hR hy _ _ o ho T.hq T.hc T.hs T.fits T.hw T.hride e hi he
    t1 t2 t3 dataK hdat

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copyShared_first_at_head
#print axioms ProofFile.Honest.K2.Law.copyShared_mask_at_head
#print axioms ProofFile.Honest.K2.Law.copyShared_later_at_head
