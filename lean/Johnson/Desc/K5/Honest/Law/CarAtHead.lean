-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/CarAtHead.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): THE FOUR MEMBERS OF THE FIRST CHAIN's FLAT LIST
BETWEEN THE OWN ROUNDS OF AN ATTENTION SEGMENT AND THE SEGMENT's BATCHING CARRY, in the library's
sense `CarK5` (Johnson/Desc/First/Att/Claims/WalkK5.lean): from the state in front of a yes of the
member's decision to the state behind it, what the segment's own rounds heard stands, and a sized
ledger is followed by a later sized one. On the verifier's chain alone.

How. EVERY LAW ON A KIND IS THE LIBRARY's, CALLED; what is done here is to show which block stands
at which number under the head. The two sendings: `commitAtS_steps`; the quiet step:
`readsAtSO_carries` (both WalkK5.lean); the smallness test's draw: `k8_steps` (WalkK8.lean beside
it). The lookup on the digits: the ledger: `k3_digits_step_leaves`
(Johnson/Desc/First/Look/K3DigitsStep.lean); what was heard: `k3_digits_step_attStays`
(K3DigitsOwnStays.lean beside it): the open attention segment's structure is kept but for two
fields. Their three premises: the block's test on the plan: `flat_ok` (Johnson/P5J/FoldJ1.lean) and
`alone_planOk`; the address's link: by its text; its piece: `piece_digits`
(Johnson/Desc/First/Link/Law/FourAtBatch.lean).

The library's nearest text: `behind_k5_carry` (Johnson/Desc/First/Att/Claims/WalkSeat.lean): four
blocks, as one seat lays them, each steps along `CarK5`, the lookup on the digits under a named
premise; `quietDigits_carries`, `seated7_steps` (WalkDigits.lean beside it). What stands here beside
it: the blocks are those of the description's own flat list under the head, found by number; the
member at + 5 is met as it is seated there; and the named premise is paid, by the two laws on the
digits' lookup that lie elsewhere in the library.

Main names:
  `decide_of_k5`: a yes of the member at 14 l + 4 is a yes of the kind's own decision. It finds the
    block as `k5_member` does (Johnson/Desc/ProofFile/Honest/K5/Law/Member.lean, which stands over
    the proof file's frame and so cannot be imported here); its end is the first conjunct of one
    direction of that file's `DecidesAs.decides`, with the parameters under ∃: the weaker of the
    two.
  `car_reads`, `car_draw`, `car_digits`, `car_look`: the members at + 5, + 6, + 7, + 8.
  `car_to_batch`: **the four, joined: from behind the segment's own rounds to the state in front of
    the batching.**

Limits. The head is a hypothesis. The decisions' yes are premises: shown together at nothing here.
The decisions alone: nothing on a run of claims (a run's mark of payment lays a ledger: of that the
library has `carK5_putFork`, WalkK5.lean). At the function `OnBytes.secondHashFunction`, of which nothing is
asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.DrawAt
import Johnson.Desc.First.Att.Claims.WalkK5
import Johnson.Desc.First.Att.Claims.WalkK8
import Johnson.Desc.First.Look.K3DigitsStep
import Johnson.Desc.First.Look.K3DigitsOwnStays
import Johnson.Desc.First.Link.Law.FourAtBatch
import Johnson.P5J.FoldJ1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att (readsAtSO)
open VerifiableInference.Desc.First.Att.P (Heard)
open K5Law (CarK5 carK5_pre)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **A yes of the member at 14 l + 4 is a yes of the kind's own decision**, at parameters whose
structure of rounds is the plan's. Conditional: the head; hg; ea; f4; d4. -/
theorem decide_of_k5 {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4) {s4 s5 : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d4 : b4.decide s4 rs gs = .ok s5) :
    ∃ p : Att.P.Par, p.own = a.own ∧ Att.P.decide Att.P.seatSO p s4 rs = .ok s5 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h4, g', hg', e⟩ := Att.P.att_only O.pub O.blank
    (IM.subs_att h.scope h.reads O.pub O.blank hg)
  obtain rfl : g' = g := by omega
  obtain ⟨Lk, Eb, b', e1, e2, hat, hla⟩ := Att.P.k5_alone O h4 hg'
  have e3 := IM.flatIx_scope h.scope h.reads O (l := 2 * g' + 1) (by omega) 2
  have hfl : cF.blocksInOrder[14 * (2 * g' + 1) + 4]? = some Eb := by
    have hfl0 := IM.hear_at_flat e1 e2
    rw [e3, show 14 * (2 * g' + 1) + 2 + 2 = 14 * (2 * g' + 1) + 4 by omega] at hfl0
    exact hfl0
  obtain rfl : Eb = b4 := Option.some.inj (hfl.symm.trans f4)
  have hd' := ((IM.yes_alone hla (fun e => nomatch e) s4 s5 rs gs).1 d4).1
  obtain ⟨a', ea', eb⟩ := Att.P.k5AtN_is _ _ _ _ _ hat
  rw [O.W] at ea'
  obtain rfl : a' = a := Option.some.inj (ea'.symm.trans ea)
  subst eb
  exact ⟨Att.P.parO Bs.G₀.W (2 * g' + 1) a' _, rfl, hd'⟩

/-- The sending of the reads with its quiet step carries. Conditional: the head; hg; ea; f5; d5. -/
theorem car_reads {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b5 : Block S ProofFile.Cl}
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d5 : b5.decide s rs gs = .ok t) : CarK5 s t := by
  obtain ⟨G₀, Xl, pd, reads, digits, b, M⟩ := member_at_head h hg
  have hA : G₀.W.A[Xl.g]? = some a := by
    rw [M.group, M.pubW]
    exact ea
  obtain rfl : b = b5 := Option.some.inj (M.flat.symm.trans f5)
  rw [M.is] at d5
  obtain ⟨m, h1, hm⟩ := seated_reads_inv Zp G₀ (2 * g + 1) Xl reads b.name M.kind hA d5
  exact carK5_pre.trans _ _ _ (K5Law.commitAtS_steps _ _ _ _ _ _ _ _ h1)
    (K5Law.readsAtSO_carries hm)

/-- The smallness test's draw carries. Conditional: the head; hg; f6; d6. -/
theorem car_draw {g : ℕ} (hg : g < 12) {b6 : Block S ProofFile.Cl}
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d6 : b6.decide s rs gs = .ok t) : CarK5 s t := by
  obtain ⟨G₀, Xl, pd, reads, digits, b, M⟩ := member_at_head h hg
  obtain ⟨b₈, hf, hla⟩ := draw_member h hg M
  obtain rfl : b₈ = b6 := Option.some.inj (hf.symm.trans f6)
  exact K5Law.k8_steps _ _ _ _ _ ((IM.k8_yes hla s t rs gs).1 d6).1

/-- The sending of the digits carries. Conditional: the head; hg; f7; d7. -/
theorem car_digits {g : ℕ} (hg : g < 12) {b7 : Block S ProofFile.Cl}
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d7 : b7.decide s rs gs = .ok t) : CarK5 s t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hk : (kindsBeforeBatching .attention (2 * g + 1 == 0))[5]? = some KindName.K1 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, _, hn, hor⟩ :=
    IM.k1_later O (2 * g + 1) .attention (IM.subs_att h.scope h.reads O.pub O.blank hg) 5 hk
      (by decide)
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g + 1) (by omega) 5,
    show 14 * (2 * g + 1) + 2 + 5 = 14 * (2 * g + 1) + 7 by omega] at hfl
  obtain rfl : b = b7 := Option.some.inj (hfl.symm.trans f7)
  rcases hor with ⟨ep, _⟩ | ⟨_, hla⟩
  · rcases IM.numbers_pieces hn with ⟨p1, _⟩ | ⟨p1, _⟩ <;> omega
  · exact K5Law.commitAtS_steps (Cl := Unit) _ _ _ _ _ _ _ _
      ((IM.yes_alone hla (fun e => nomatch e) s t rs gs).1 d7).1

/-- **The lookup on the digits carries.** Conditional: the head; hg; f8; d8. -/
theorem car_look {g : ℕ} (hg : g < 12) {b8 : Block S ProofFile.Cl}
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d8 : b8.decide s rs gs = .ok t) : CarK5 s t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', e1, e2, h3, hla⟩ := IM.k3_of h.scope h.reads O (2 * g + 1) (by omega) true
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by omega) (IM.k3Ix (2 * g + 1) true)] at iB
  have hix : IM.k3Ix (2 * g + 1) true = 6 := by
    show (if true = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0) = 6
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
    rfl
  rw [hix, show 14 * (2 * g + 1) + 2 + 6 = 14 * (2 * g + 1) + 8 by omega] at iB
  obtain rfl : b = b8 := Option.some.inj (iB.symm.trans f8)
  have hd' := ((IM.yes_alone hla (fun e => nomatch e) s t rs gs).1 d8).1
  have hOk : b'.planOk = true := by
    rw [← IM.alone_planOk hla]
    exact P5J.flat_ok h.toAtMg b (List.mem_of_getElem? f8)
  have h7 : 7 ≤ (IM.k3Place (2 * g + 1) true).piece := by
    show 7 ≤ IM.k3Ix (2 * g + 1) true + 1
    rw [hix]
  have hpc := LinkJoin.piece_digits _ _ _ _ _ _ b' h3 (2 * g + 1) rfl h7
  obtain ⟨F, Gk, hF, hG, _, hZ, _⟩ :=
    VerifiableInference.OnPublicFiles.k3_digits_step_leaves _ _ _ _ _ _ b' h3 hOk (2 * g + 1) rfl hpc
      s t rs gs hd'
  have hA := VerifiableInference.OnPublicFiles.k3_digits_step_attStays _ _ _ _ _ _ b' h3 hOk
    (2 * g + 1) rfl hpc s t rs gs hd'
  refine ⟨fun hd e => ?_, fun F' hF' sF' => ?_⟩
  · cases hh : s.here with
    | att a =>
      obtain ⟨w, hw, k⟩ := hA a hh
      unfold S.heard5? at e ⊢
      rw [hh] at e
      rw [hw]
      exact (congrArg (·.heard5) (k a.tl a.F)).trans e
    | _ =>
      unfold S.heard5? at e
      rw [hh] at e
      exact nomatch e
  · obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
    obtain ⟨l1, l2, _⟩ := hZ sF'
    exact ⟨Gk, hG, l1, l2⟩

/-- **The four members carry, to the state in front of the batching.** Conditional: the head; hg;
ea; f5 … f8: which four members; d5 … d8: their yes, each at its own rounds. -/
theorem car_to_batch {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s5 s6 s7 s8 s9 : S}
    {rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d5 : b5.decide s5 rs5 gs5 = .ok s6) (d6 : b6.decide s6 rs6 gs6 = .ok s7)
    (d7 : b7.decide s7 rs7 gs7 = .ok s8) (d8 : b8.decide s8 rs8 gs8 = .ok s9) : CarK5 s5 s9 :=
  carK5_pre.trans _ _ _ (car_reads h hg ea f5 d5)
    (carK5_pre.trans _ _ _ (car_draw h hg f6 d6)
      (carK5_pre.trans _ _ _ (car_digits h hg f7 d7) (car_look h hg f8 d8)))

end H2K5.Honest

#print axioms H2K5.Honest.decide_of_k5
#print axioms H2K5.Honest.car_reads
#print axioms H2K5.Honest.car_draw
#print axioms H2K5.Honest.car_digits
#print axioms H2K5.Honest.car_look
#print axioms H2K5.Honest.car_to_batch
