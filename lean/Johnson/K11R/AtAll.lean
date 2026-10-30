-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/AtAll.lean: THE PREMISES THAT THE LAW OF THE MERGE OF THE CLAIMS ON THE
COMMITTED TABLE (kind K11) ASKS OF A FILLING OF THE TABLE OF JOINTS HOLD AT THE COMPOSED MEANING's
CLOSED CONSTANT. Two theorems with their proofs. It proves nothing of any sub-protocol: a joining of
others' lemmas.

What is said. `mergeFill_atAll`: `MergeFill` (Johnson/Top/H0/MergeLaw/TieThreeFour.lean), all eleven
fields, at `mgAtAll h` (Johnson/P5J/MgAtAll.lean), at the written list
of places, border 346, segment 24, AT ONE CLAIM: with the merge's numbers `parOf Zp Bs.G₀`, Bs the
opening's letter, the reader of a cell by its numbers, and two members xM, xI, WHICH ARE ARGUMENTS:
xM is the first member of the constant's own list at a place pM of the head's first sending; xI the
first at the index masks' place. (So whoever calls the theorem holds the two members themselves, not
their places alone: the law's other premises read their shapes.)
  `members_atAll`: such pM, xM, xI are there, pM being the place at which the planner's seats have
    the segment's first message with mask rows (`maskPlace`): from one test off the public
    parameters alone (`k11AtRB`, K11MembersAtR.lean: it reads the members' places alone, which do
    not hang on the radii).

FROM WHAT.
  h: the constant's own head (`AtMgA`), at the concrete second hash function. O: an opening of the
    IOP as written in Lean at the head's own letters (the head's field "laid" holds one).
  TWO NAMED TESTS, each with code, each off the public parameters alone: tn (`numsB`, three in one):
    the planner's segment 24 has as many slots as the public parameters' head; THE CONSTANT's INDEX,
    the written number of rows 3,076,096, is the number of rows of the committed table's layout; the
    row's shape has as many column bits as the layout; tc: the planner's segment 24 states one claim
    (`nclB`).
  hM, hI, hp: what xM, xI and pM are (above).
  hwt: the lemma that joins the two sentences for "weights", under a letter Wa on the state in
    front.

HOW THE TWENTY PREMISES OF `mergeFill_at` (Johnson/Desc/Sound/MgAt/K11.lean) FALL. The six closed
facts on the table: `k11_six` (K11Closed.lean), by the kernel. hns, hlay, hnR, hkC: `nums_of_test`,
`hlay_at` (Johnson/Top/H0/MergeLaw/PlanNumsAt.lean), from tn: the constant lays the very terms of
which these speak. The two facts on the planner's numbers: `lay_room_at` (the same file), from the
head. The five on the two members: from hM, hI and hp, by what "the first member at a place" says.
The number of claims: `ncl_of_test` (Johnson/Top/H0/MergeLaw/PlanNclAt.lean), from tc. hlk, hst, hr:
`merge_at_linkAt` (ToldDesc/MergeAtLinkAt.lean), from the head. hmat: `matOfCells_low`
(Johnson/Desc/K13/Law/MatOfCells.lean). hwt: the premise.

Limits. A MEMBER OF THE HEAD IS PROVED AT THE SECOND HASH FUNCTION `OnBytes.secondHashFunction`, AT THE TWO
WRITTEN SETS OF PUBLIC FILES `VerifierAndGoals.storedPublicFiles` AND `VerifierAndGoals.zGap`, IN THE SIDE LIBRARY (AtFullSide/Top/:
`headMember_zFull`, `headMember_zGap`); AT OTHER FILES OR ANOTHER HASH NONE IS SHOWN: its authors
ask that no law be ended in the constant on their word yet: THIS FILE IS TYPED AGAINST ITS FORM. The
tests are evaluated here at nothing. ni, R, posI and Wa are letters. hwt speaks of the constant's
own term for "weights". Nothing on soundness.
-/
import Johnson.ToldDescR.MergeAtLinkAt
import Johnson.P5J.MgAtAll
import Johnson.Desc.Sound.MgAt.K11
import Johnson.Desc.Sound.MgAt.K11Closed
import Johnson.Desc.Sound.MgAt.K11MembersAtR
import Johnson.Top.H0.MergeLaw.PlanNclAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes.Maker OnBytes.Slice
open OnBytes.Model (WsShape wsLayOf)
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw
open P5J (AtMgA mgAtAll TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
  {base : List (VerifiableInference.Desc.Block S ProofFile.Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE MERGE's PREMISES ON THE FILLING HOLD AT THE COMPOSED MEANING's CONSTANT**, from its head,
two named tests, what the two members are, and the lemma that joins the two sentences for
"weights". -/
theorem mergeFill_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B)
    (tn : numsB Zp 24 OnBytes.Flat.numsFull.rows = true)
    (tc : nclB Zp 24 1 = true) (pM : ℕ × ℕ) (xM xI : Mem)
    (hM : xAt (P5J.At.ms Zp Z.lay) pM = some xM)
    (hI : xAt (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF).index = some xI)
    (hp : pM ∈ (P5J.At.N Zp cF).sent 24 0)
    (posI : ℕ → Bool × ℕ × ℕ) (ni R : ℕ) (Wa : S → Prop)
    (hwt : ∀ a y w, Wa a.2 → VerifiableInference.Desc.First.FillP1.wtP1 (parOf Zp Bs.G₀) ni
      (fun w => VerifiableInference.Desc.K13.Law.cellAtNo w.cells)
      (maskRowAt h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N 24) a y w →
      h.𝔇.wt 24 a y w) :
    ∃ (s₀ : WsShape) (p3 : Bool) (lkW : ℕ)
      (hw : wsLayOf s₀ p3 lkW = .ok (parOf Zp Bs.G₀).lay)
      (hn : 2 * (parOf Zp Bs.G₀).lay.lk + 3 ≤ (parOf Zp Bs.G₀).nMsg),
      MergeFill h.𝔇.cs h.𝔇.G h.𝔇.arr
        (fun z s => h.𝔇.smp (z, s))
        (fun c => VerifiableInference.Desc.K13.Law.cellAtNo c)
        (fun z c s => h.𝔇.decT c (z, s)) 1
        h.𝔇.d1.lin xM xI (posMask R) posI (parOf Zp Bs.G₀) hw hn ni
        (h.𝔇.N.group 24) R Wa (idxAt h.𝔇 ni posI xI) h.𝔇.N
        (mgAtAll h) h.𝔇.links psFull 346 24 := by
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := (IM.base_made O.made).2.2.1
  obtain ⟨⟨s₀, p3, lkW, hw⟩, hn⟩ := lay_room_at OnBytes.secondHashFunction hG h.laid.publicO
  have eM : seatOf xM = pM :=
    of_decide_eq_true (List.find?_some (p := fun y => decide (seatOf y = pM)) hM)
  have a5 : seatOf xI = (P5J.At.N Zp cF).index := of_decide_eq_true
    (List.find?_some (p := fun y => decide (seatOf y = (P5J.At.N Zp cF).index)) hI)
  have a1 : xM ∈ P5J.At.ms Zp Z.lay := List.mem_of_find?_eq_some hM
  have a2 : seatOf xM ∈ (P5J.At.N Zp cF).sent 24 0 := eM ▸ hp
  have a3 : ((P5J.At.ms Zp Z.lay).find? fun y => decide (seatOf y = seatOf xM)) = some xM := by
    rw [eM]
    exact hM
  have a4 : xI ∈ P5J.At.ms Zp Z.lay := List.mem_of_find?_eq_some hI
  have hc : h.𝔇.d1.ncl 24 = 1 := ncl_of_test tc
  obtain ⟨l, name, rr, hlk, hst, hr⟩ := ToldDesc.merge_at_linkAt h.scope h.reads O
  obtain ⟨n1, n3, n4⟩ := nums_of_test hG tn
  have n2 := hlay_at hG
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := k11_six h.𝔇 mgBase rfl rfl
  refine ⟨s₀, p3, lkW, hw, hn, ?_⟩
  rw [← hc]
  exact mergeFill_at h.𝔇 mgBase (fun c => VerifiableInference.Desc.K13.Law.cellAtNo c) xM
      xI posI (parOf Zp Bs.G₀) hw hn ni R psFull 346 24 l name Wa c1 c2 c3 c4 c5 c6 n1 a1 a2 a3 a4
      a5 hlk rr hst hr hwt n2 n3 n4
      (fun M i C hC => VerifiableInference.Desc.K13.Law.matOfCells_low _ _ M i C hC)

/-- **The two members are there**, at the constant's own list: from the test off the public
parameters alone: pM is the place at which the planner's seats have the segment's first message
with mask rows. -/
theorem members_atAll (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (lay : ByteArray)
    (tm : k11AtRB Zp 24 = true) :
    ∃ (pM : ℕ × ℕ) (xM xI : Mem),
      maskPlace (P5T.planSeats Zp Zp.D.1) Zp.first.shape 24 = some pM ∧
      xAt (P5J.At.ms Zp lay) pM = some xM ∧
      xAt (P5J.At.ms Zp lay) (P5J.At.N Zp cF).index = some xI ∧
      pM ∈ (P5J.At.N Zp cF).sent 24 0 := by
  unfold k11AtRB at tm
  cases hp : maskPlace (P5T.planSeats Zp Zp.D.1) Zp.first.shape 24 with
  | none => rw [hp] at tm; cases tm
  | some pM =>
    rw [hp] at tm
    have h' : membersAtB (P5T.msAtR Zp (P5J.At.rad Zp lay))
        (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)) 24 pM = true :=
      (membersAtB_seats _ _ (seats_atR Zp (P5J.At.rad Zp lay) fun _ _ => 0) _ 24 pM).trans tm
    unfold membersAtB at h'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    obtain ⟨xM, hM⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨xI, hI⟩ := Option.isSome_iff_exists.1 h3
    exact ⟨pM, xM, xI, rfl, hM, hI, h2⟩

end K11

#print axioms K11.members_atAll
#print axioms K11.mergeFill_atAll
