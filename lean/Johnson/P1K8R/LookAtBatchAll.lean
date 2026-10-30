-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/LookAtBatchAll.lean: AT AN ATTENTION SEGMENT AND AT THE HEAD's WHAT THE LOOKUP ON THE
CALLS HAS HEARD BEHIND ITS OWN BLOCK STANDS IN FRONT OF THE BATCHING; SO THERE IT HAS HEARD
SOMETHING, AND ITS ROWS NAME NO ENTRY. AT STATES THAT THE FIRST CHAIN's OWN BLOCKS REACH; UNDER THE
SCOPE, THE FILES READ, IM.Open AND THE DESCRIPTION's TEST ON ITS PLAN, which comes in through the
lookups' blocks alone. Lemmas; none of the library's goals. No prover stands in them; nothing on
completeness, soundness or hiding. A joining.

  **`look_back_att`**, **`callsRows_att`**   five blocks back, from 14 (2 g + 1) + 9 to 14 (2 g + 1)
      + 4, each in OnPublicFiles.KeepsLook (Johnson/K11R/LeavesAt346.lean): `look_back_digits`
      (Johnson/P1K8R/LookAtBatch.lean); LinkJoin.back_k1_of, back_k8_of
      (Johnson/Desc/First/Link/Law/StretchParts.lean) at MergeLaw.laterAt_keeps, k8_keeps
      (LeavesAt346.lean); LinkJoin.back_of (StretchBack.lean) at IM.k1_reads_of
      (Johnson/IMR/K1Scope.lean) with MergeLaw.retype_decides (Johnson/K11R/MaskSeat.lean) over
      k1Reads_keeps; back_of at IM.k5_of (Johnson/IMR/K5Seat.lean) with Att.P.k5AtN_whole
      (Johnson/Desc/First/Att/K05Leaves.lean), lay_keeps_heard (K05Crossing.lean),
      OnPublicFiles.look_putFork (Johnson/Top/H/Keep/LookBlind.lean). Then `callsRows_behind`
      (Johnson/P1K8R/HeardAtBatch.lean)
  **`look_back_head`**   six blocks back, from 347 to 341: LinkJoin.back_k11_of at
      MergeLaw.decide_leaves_look (Johnson/Top/H0/MergeLaw/StepsFo.lean); MergeLaw.back_keeps at
      seated_five (LeavesAt346.lean)
  `callsRows_341`, **`callsRows_head`**   the first: ITS LINES ARE THE FIRST FIVE OF THE PROOF OF
      P4.bare_341 (Johnson/P4R/BareAt341.lean), whose end says less: of whatever is heard, not that
      something is. That is wanted here: KeepsLook runs forward alone
Limits. Nothing on what the head's lookup on the digits has heard. Nothing on the two other forms
that a lookup hears; whoever shows something of what is heard behind the lookup on the calls has it
in front of the batching, by the two walks. Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.LookAtBatch
import Johnson.K11R.LeavesAt346
import Johnson.K11R.MaskSeat
import Johnson.Desc.First.Link.Law.StretchParts
import Johnson.Top.H0.MergeLaw.StepsFo
import Johnson.Desc.First.Att.K05Leaves
import Johnson.Desc.First.Att.K05Crossing
import Johnson.Top.H.Keep.LookBlind
import Johnson.IMR.K1Scope
import Johnson.IMR.K5Seat
import Johnson.P4R.BareAt341

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **AT AN ATTENTION SEGMENT: WHAT THE LOOKUP ON THE CALLS HAS HEARD BEHIND ITS OWN BLOCK STANDS IN
FRONT OF THE BATCHING**: five blocks back. -/
theorem look_back_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 4) (z, s) ∧ OnPublicFiles.KeepsLook s s' := by
  have n24 : ¬ 2 * g + 1 = 24 := by omega
  have i1 : IM.k1Ix (2 * g + 1) true = 5 := by
    show (if true = true then 5 else 3) + (if 2 * g + 1 = 24 then 1 else 0) = 5
    rw [if_pos rfl, if_neg n24]
  have i0 : IM.k1Ix (2 * g + 1) false = 3 := by
    show (if false = true then 5 else 3) + (if 2 * g + 1 = 24 then 1 else 0) = 3
    rw [if_neg (by decide), if_neg n24]
  have i8 : LinkJoin.k8Ix (2 * g + 1) = 4 := by
    show 4 + (if 2 * g + 1 = 24 then 1 else 0) = 4
    rw [if_neg n24]
  obtain ⟨s8, r8, k8⟩ := look_back_digits hS hR O hOk (l := 2 * g + 1) (by omega) h
  obtain ⟨s7, r7, k7⟩ := LinkJoin.back_k1_of (R := OnPublicFiles.KeepsLook)
    (fun q gp link piece moment arrays => MergeLaw.laterAt_keeps q gp link piece moment arrays)
    hS hR O (l := 2 * g + 1) (by omega) (z := z) (s' := s8) (by rw [i1]; exact r8)
  rw [i1] at r7
  obtain ⟨s6, r6, k6⟩ := LinkJoin.back_k8_of (R := OnPublicFiles.KeepsLook) MergeLaw.k8_keeps
    hS hR O (l := 2 * g + 1) (by omega) (z := z) (s' := s7) (by rw [i8]; exact r7)
  rw [i8] at r6
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, -, -, e4⟩ :=
    IM.k1_reads_of hS hR O (2 * g + 1) (by omega)
  rw [i0] at e2
  obtain ⟨s5, r5, k5⟩ := LinkJoin.back_of (R := OnPublicFiles.KeepsLook) hS hR O (l := 2 * g + 1)
    (i := 3) (by omega) e1 e2 e4 (fun q => nomatch q)
    (MergeLaw.retype_decides (MergeLaw.k1Reads_keeps Z Bs.G₀ (2 * g + 1) Xl _ reads)) r6
  obtain ⟨Lk', b5, b5', a, f1, f2, f3, f4, -⟩ := IM.k5_of hS hR O g hg
  obtain ⟨s4, r4, k4⟩ := LinkJoin.back_of (R := OnPublicFiles.KeepsLook) hS hR O (l := 2 * g + 1)
    (i := 2) (by omega) f1 f2 f4 (fun q => nomatch q)
    (fun s rs gs t hd => (Att.P.k5AtN_whole OnPublicFiles.KeepsLook (fun _ _ hx => hx)
      (fun s G => OnPublicFiles.keepsLook_of_eq (OnPublicFiles.look_putFork s G))
      (fun _ _ _ _ e => OnPublicFiles.keepsLook_of_eq (Att.P.lay_keeps_heard e)) f3).1 s rs gs t hd) r5
  exact ⟨s4, r4, (((k4.trans k5).trans k6).trans k7).trans k8⟩

/-- **So, at an attention segment, in front of the batching: the lookup on the calls has heard
something, and its rows name no entry.** -/
theorem callsRows_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ k, s.lookHeard? = some k ∧ ∀ f ∈ k.rows.toList, f.ents = #[] := by
  obtain ⟨s4, r4, e⟩ := look_back_att hS hR O hOk hg h
  obtain ⟨k, hk, hb⟩ := callsRows_behind hS hR O hOk (l := 2 * g + 1) (by omega) r4
  exact ⟨k, e k hk, hb⟩

/-- **AT THE HEAD's SEGMENT: WHAT THE LOOKUP ON THE CALLS HAS HEARD BEHIND ITS OWN BLOCK (341)
STANDS IN FRONT OF THE BATCHING (347)**: six blocks back. -/
theorem look_back_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start 341 (z, s) ∧ OnPublicFiles.KeepsLook s s' := by
  obtain ⟨s6, r6, k6⟩ := LinkJoin.back_k11_of (R := OnPublicFiles.KeepsLook)
    (fun Pm s rs _ t hd => OnPublicFiles.keepsLook_of_eq (MergeLaw.decide_leaves_look Pm hd)) hS hR O h
  obtain ⟨s1, r1, k1⟩ := MergeLaw.back_keeps (k := 341) 5 (MergeLaw.seated_five hS hR O hOk) z s6 r6
  exact ⟨s1, r1, k1.trans k6⟩

/-- **Behind the lookup on the calls of the head's segment: it has heard something, and its rows
name no entry.** P4.bare_341 (Johnson/P4R/BareAt341.lean) has the second half, for whatever is
heard; its proof's lines are these. -/
theorem callsRows_341 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start 341 (z, s)) :
    ∃ k, s.lookHeard? = some k ∧ ∀ f ∈ k.rows.toList, f.ents = #[] := by
  obtain ⟨_, _, s340, -, -, ⟨p, n, HP, rs, gs, a2⟩, b3, Qp, sent, laid, rs3, gs3, f3, hv, hp⟩ :=
    P4.back_341 hS hR O h
  obtain ⟨G, hG, hs, -, -⟩ := Kinds.Head.Law.placeH2_free a2
  exact OnPublicFiles.calls_rowsBare K3Lot.ofForm 3 laid sent Qp [] s340 s rs3 gs3
    (K3.Law.blockVia_decide (hp (P4.plan_at O hOk 340 b3 f3)) hv) hG hs

/-- **So, at the head's segment, in front of the batching: the like.** -/
theorem callsRows_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start 347 (z, s)) :
    ∃ k, s.lookHeard? = some k ∧ ∀ f ∈ k.rows.toList, f.ents = #[] := by
  obtain ⟨s1, r1, e⟩ := look_back_head hS hR O hOk h
  obtain ⟨k, hk, hb⟩ := callsRows_341 hS hR O hOk r1
  exact ⟨k, e k hk, hb⟩

end

end P1K8

#print axioms P1K8.look_back_att
#print axioms P1K8.callsRows_att
#print axioms P1K8.look_back_head
#print axioms P1K8.callsRows_341
#print axioms P1K8.callsRows_head
