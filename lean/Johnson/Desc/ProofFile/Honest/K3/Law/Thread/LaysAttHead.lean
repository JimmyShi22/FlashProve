-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LaysAttHead.lean: the member at the lookup on the calls
of an attention link lays a rider's clause on the field g of the own part of the open attention
link, at the thread of `lettersHead` (Honest/Thread/FirstHead.lean), which is stated under the
library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). The theorem is general in the sentence
R on g. Theorems: each is a composition of earlier ones; no definition.

Terms. Honest/K3/GLOSSARY.md ("rider"). In this file: attention group g stands at link 2 g + 1; the
border in front of its lookup on the calls has the number 14 (2 g + 1) + 3. "Reached" is the
library's `Reach` (Johnson/Top/H0/Walk/Reach.lean). The hearing at public parameters p is
`hearVia p F rs` (Johnson/Desc/First/Look/Via/Via.lean). `LaysAt` and `RiderCl` are definitions of
Honest/Thread/Riders.lean.

What is shown.
  `linksW_odd`: the sort that `IM.linksW` (Johnson/IMR/WrittenList.lean) gives at link 2 g + 1, g <
    12, is "attention".
  `att_front_head`: at every state reached in front of that member the open part is an attention
    link's own.
  `calls_att_head`: behind that member's accepting step from such a state: an attention link's own
    part is open, and its field g holds what the hearing returned on the same rounds, at public
    parameters whose shape is the plan's.
  `lays_att_head`: so the member lays the clause "an attention link's own part w is open and R w.g",
    from the border behind it on, in the form `LaysAt`.
The clause is written out as a `RiderCl`: lo := 14 (2 g + 1) + 4, hi := 14 (2 g + 1) + 9. That it
stays past the five members between is not shown in this file.

Hypotheses that remain.
  `h`, `hg`: the library's hypothesis `P5J.AtMgA`; g is below 12.
  `ha`: a is the plan at g.
  `hr`: (in `att_front_head`; inside `calls_att_head`) the state in front is reached at the border.
  `hR`: (in `lays_att_head`) at all public parameters of the shape a.fs, R holds of whatever the
    hearing returns. It is shown here of no R.
What R can say. R reads the field g alone: neither the rounds nor the ledger. `hR` asks it of
whatever the hearing returns, at every ledger and all rounds, at all public parameters of that
shape. So R can say only what holds of every such return. A sentence that ties g to the run's own
rounds is no such R.

Imported: Honest/Thread/FirstHead.lean, Honest/Thread/Riders.lean and Honest/Thread/ReachFacts.lean.

How the proof goes. The theorems call `site_calls_head` (Honest/K3/Law/Thread/SiteThereHead.lean),
`site_fs_att_head` and `border_odd` (Honest/K3/Law/Thread/AttBackHead.lean), `site_hub`
(Honest/K3/Law/Thread/AtLink.lean) and `calls_here` (Honest/K3/Law/Thread/StateHere.lean);
`thr_reach` (Honest/Thread/ReachFacts.lean); and the library's `Meaning.K2.att_fold`
(Johnson/IMR/SortDigits.lean) and `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean).

Limits. On the verifier's side alone. At the full size and the earlier hash (`OnBytes.secondHashFunction`)
alone. At the twelve attention links 1, 3, ..., 23 alone. In `calls_att_head` the first tree's
number at the step is arbitrary, while "reached" stands at 0; in `lays_att_head` it is the thread's
own. No statement of this file shows that the thread holds at any run. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AttBackHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateHere
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.IMR.SortDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain Place Strs OpenedColumn)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF thr_reach)

/-- The sort that `IM.linksW` gives at an odd link. -/
theorem linksW_odd : ∀ g, g < 12 →
    IM.linksW[2 * g + 1]? = some VerifiableInference.Desc.First.ModelPart.attention := by
  decide

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At every state reached in front of the member an attention link's own part is open.**
Conditional on `P5J.AtMgA`. -/
theorem att_front_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12)
    (a : ProofFile.InstPub × TS)
    (hr : Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 3) a) :
    ∃ w, a.2.here = .att w := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, rs, cols, f⟩ := hr.fold
  exact _root_.Meaning.K2.att_fold h.scope h.reads O (by omega) f (linksW_odd g hg)

/-- **Behind the member's accepting step from a reached state**: an attention link's own part
is open, and its field g holds what the hearing returned on the same rounds. Conditional on
`P5J.AtMgA` and g < 12. No instance of these hypotheses is exhibited in this file. -/
theorem calls_att_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∀ (a : OnBytes.Attention.Plan) (blk₃ : Block TS ProofFile.Cl), (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : P, p.shape = some a.fs ∧
        ∀ (z : ProofFile.InstPub) (ft : Nat) (sj s' : TS) (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat),
          Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 3)
            (z, sj) →
          blk₃.step ft sj rs c = .ok (s', n) →
          ∃ F H G₁ w, hearVia p F rs = some (H, G₁) ∧ s'.here = .att w ∧ w.g = some H := by
  intro a blk₃ ha hb
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨s, hs, e1, e2, _, _⟩ := site_calls_head h (2 * g + 1) hl
  refine ⟨s.p, site_fs_att_head h s hs g e1 e2 a ha, fun z ft sj s' rs c n hr hstep => ?_⟩
  obtain ⟨Fd, Bs, base, A, B, lot, O, hlot, hbs, hm⟩ := site_hub h s hs (by rw [e1]; exact hl)
  have hb' : cF.blocksInOrder[borderOf s.link s.digits]? = some blk₃ := by
    rw [e1, e2, border_odd]
    exact hb
  obtain ⟨m1, m2, m3⟩ := hm blk₃ hb'
  obtain ⟨F, H, G, _, _, hv, hC, _⟩ := calls_here _ _ _ _ Fd Zp Bs base cF A B O s hs e2 lot blk₃
    hlot hbs m1 m2 m3 ft sj s' n rs c hstep
  obtain ⟨w₀, hw₀⟩ := att_front_head h g hg (z, sj) hr
  have hw : sj.here = .att w₀ := hw₀
  rcases hC with ⟨q, hq, _⟩ | ⟨q, _, e⟩ | ⟨q, hq, _, _⟩
  · rw [hw] at hq
    cases hq
  · exact ⟨F, H, G, _, hv, by rw [e], rfl⟩
  · rw [hw] at hq
    cases hq

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The member lays the clause.** Conditional on `P5J.AtMgA`, g < 12, the plan at g, and `hR`,
which is shown here of no R. No instance of these hypotheses is exhibited in this file. -/
theorem lays_att_head (g : Nat) (hg : g < 12) (a : OnBytes.Attention.Plan)
    (ha : (P5J.At.X Zp).A[g]? = some a) (R : Option OnBytes.Model.Forest.Heard → Prop)
    (hR : ∀ p : P, p.shape = some a.fs → ∀ F rs Hd G₁, hearVia p F rs = some (Hd, G₁) →
      R (some Hd)) :
    LaysAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (14 * (2 * g + 1) + 3)
      ⟨14 * (2 * g + 1) + 4, 14 * (2 * g + 1) + 9, fun _ _ s => ∃ v, s.here = .att v ∧ R v.g⟩ := by
  intro blk hblk k st m E ds y cols s' hA _ hSt
  have hblk' : cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk := hblk
  obtain ⟨p, hp, hB⟩ := calls_att_head h g hg a blk ha hblk'
  have hb : 14 * (2 * g + 1) + 3 ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk').1
  obtain ⟨F, Hd, G₁, v, hv, hv1, hv2⟩ := hB _ _ st s' _ cols _
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA) hSt.2
  exact ⟨v, hv1, by rw [hv2]; exact hR p hp F _ Hd G₁ hv⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.linksW_odd
#print axioms ProofFile.Honest.K3.Law.AtThr.att_front_head
#print axioms ProofFile.Honest.K3.Law.AtThr.calls_att_head
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_att_head
