-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/K03WtBackAt.lean: THE LOOKUP ARGUMENT ON THE DIGITS AT THE OUTPUT HEAD's SEGMENT: THE
PREMISE hWt OF THE LOOKUP's FILES' `ridesAtR_digits_head`
(Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean [not imported here]): "THE SENTENCE weights GOES BACK
OVER AN ACCEPT OF THE SUB-PROTOCOL", IN ITS OWN TEXT, AT THE CLOSED CONSTANT, UNDER THE HEAD
`AtMgA`, A VALUE OF `Free` AND ITS THREE EQUATIONS. A join of other files' theorems.
  What the sentence is: `𝔇.wt` is the output head's `wtK6` (Johnson/Desc/Kinds/Law/WtK6.lean): it
    reads no string; of the verifier's state it reads `WeightAt` alone.
  `heard_345`: at a state reached at border 345 of the first chain: it stands in the head's
    segment, its ledger has its sizes, and the head's seat's reader "heard" answers. AFTER
    ANOTHER FILE's OWN PROOF: the first three quarters of `waK6_at_346`
    (Johnson/P4R/WaK6At346.lean): the walk back to the head's own sub-protocol at 341; "heard"
    answers behind its accept (`mergeClaim_behind`); the three sub-protocols between keep it
    (`kept_342`, `kept_343`, `kept_344`, `heard_kept`).
  **`k03_hWt`**: THE PREMISE: `digits_at_head` (Johnson/Desc/Kinds/Law/DigitsKeptAtDecide.lean: an
    accept of the stated sub-protocol at the head's digits is `KeptW`) and `weightAt_kept`
    (Johnson/Desc/Kinds/Law/WeightAtSame.lean: `WeightAt` is one at two states that are `KeptW`,
    where "heard" answers at the earlier).

FOR OTHER SPENDERS. The general form lies already in another file: `weightAt_kept`: the sentence
goes back over ANY step that gives `KeptW`, where "heard" answers in front. `heard_345` is general
in the opened description.

Limits. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). At
OnBytes.secondHashFunction. The full size alone.
Nothing on soundness.

-/
import Johnson.P5J.K03PiecesAt
import Johnson.P5J.MgAtAll
import Johnson.P5J.RchAtMg
import Johnson.P4R.WaK6At346
import Johnson.IMR.SeatOpen
import Johnson.Desc.Kinds.Law.DigitsKeptAtDecide
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.Desc.Kinds.Law.MergeClaimAt
import Johnson.Desc.Kinds.Law.WtK6
import Johnson.Desc.Sound.MgAt.K3RidesDigStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain FileDescription Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn start)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.PscRun (Sized)
open P4 (peel yes_341 kept_342 kept_343 kept_344 wellLaid_341 plan_at)

/-- **At a state reached at border 345: the head's segment, a ledger with its sizes, and "heard"
answers.** -/
theorem heard_345 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {XP : Type} {start : XP → S} {z : XP} {s345 : S}
    (h345 : Reach 0 (c.blocksInOrder.map below) start 345 (z, s345)) :
    (∃ o, s345.here = .head o ∧ Sized o.F) ∧
      ∃ H, (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).heard s345 = some H := by
  obtain ⟨s344, B4, r4, g4, h344, hB4, -, d4⟩ := peel h345
  obtain ⟨s343, B3, r3, g3, h343, hB3, -, d3⟩ := peel h344
  obtain ⟨s342, B2, r2, g2, h342, hB2, -, d2⟩ := peel h343
  obtain ⟨s341, B1, r1, g1, h341, hB1, hc1, d1⟩ := peel h342
  have c1 := yes_341 hS hR O hB1 d1
  have c2 : WellLaid ((seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).ledger s341) :=
    wellLaid_341 hS hR O (plan_at O hOk 340) (reach_raw h341) _ _
  obtain ⟨a, F1, X0, Q, -, hop, -, e⟩ := Came.decide_record _ _ _ _ c1
  have ho2 : s342.here = .head { a with F := F1, x := some X0, squaresP := some Q } := by rw [e]
  have eL : (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).ledger s342 = F1 := by
    rw [e]
    show (S.fork? _).getD {} = F1
    simp [S.fork?, hop]
  have hz2 : Sized ({ a with F := F1, x := some X0, squaresP := some Q } : HeadOwn).F := by
    have hL := blockAt_later _ _ _ _ s341 s342 r1 g1 c1
    rw [eL] at hL
    exact hL.sized (sized_of_wellLaid c2)
  obtain ⟨-, H, -, -, -, -, -, hH, -⟩ := Came.mergeClaim_behind Bs.G₀.W 24 c1 c2 hc1
  have k2 := kept_342 hS hR O hB2 d2 ho2
  obtain ⟨o3, ho3, hz3⟩ := k2.next ho2 hz2
  have k3 := kept_343 hS hR O hB3 d3 ho3
  obtain ⟨o4, ho4, hz4⟩ := k3.next ho3 hz3
  have k4 := kept_344 hS hR O hB4 d4 ho4
  obtain ⟨o5, ho5, hz5⟩ := k4.next ho4 hz4
  exact ⟨⟨o5, ho5, hz5⟩, H, heard_kept _ _ ((k2.trans k3).trans k4) H hH⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **hWt AT THE CONSTANT.** -/
theorem k03_hWt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K 24 true)
        (.forms 24 kk "weights") →
      ¬ insQ linksFull PS (k3K 24 true) (.forms 24 kk "weights") →
      ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ w, (h.toAtMg.𝔇 h.𝔇).wt 24 (z, v.1) (strsOf FrD v.2) w →
        (h.toAtMg.𝔇 h.𝔇).wt 24 (z, u.1) (strsOf FrD u.2) w := by
  intro b' hb kk _ _ z u v _ hr _ _ ⟨rs, gs, hd⟩ w H
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape 24 true b' hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 345 (z, u.1) :=
    h.toAtMg.rch_is_reach _ _ hr
  obtain ⟨⟨o, ho, hz⟩, hh⟩ := heard_345 h.scope h.reads O h.laid.planOk hr'
  rw [O.W] at hh
  have hH : VerifiableInference.Desc.K3.isHead (At.X Zp) 24 = true := by
    unfold VerifiableInference.Desc.K3.isHead
    rw [if_pos hp4, hN]
    rfl
  have K := (digits_at_head K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes
    Zp.first.shape (IM.k3Place 24 true) b' hb (Pc.planOk 24 (by omega) true b' hb) 24 rfl hpc hH
    u.1 v.1 rs gs hd ho hz).1
  have H' : AtTable.wtK6 (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
      (At.layout Zp) (At.num Zp) (At.num Zp 24 0) 0 24 (z, v.1) (strsOf FrD v.2) w := H
  show AtTable.wtK6 (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
      (At.layout Zp) (At.num Zp) (At.num Zp 24 0) 0 24 (z, u.1) (strsOf FrD u.2) w
  intro h24 hrg
  exact (weightAt_kept (At.X Zp) K hh _ _).1 (H' h24 hrg)

end P5J

#print axioms P5J.heard_345
#print axioms P5J.k03_hWt
