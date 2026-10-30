-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/AheadAt.lean: FOR THE ITEM "totalB": "NOTHING IS AHEAD IN FRONT OF THE BATCHING",
UNDER THE LIBRARY's HEAD: AT A REACHED STATE WITHOUT A MARK, AND AT EVERY STAND OF THE BATCHING AT THE FRAME's OWN
THREAD. Statements and proofs: calls; no goal is stated.
  `ahead_none_reach`   under the head, l < 25: at a state that is reached by the members' own steps from the start's
      state, at every public part z, at the border number 14 l + nAt l + 2, and bears no mark: whatever part
      `K9.segAt?` reads there, `K9.aheadIn sent own a c = none`, at every sent, own and c: the library's
      `ahead_none_of_facts` (Johnson/Desc/First/Link/Law/FrameFullOf.lean) at the frame's `foldFacts_raw`
      (Honest/Thread/ReachFacts.lean); its closed test on the plan's numbers by the library's `LPFK9.hall_of_moments`
      at the library's theorem `P5J.AtMg.shape_moments` (Johnson/P5T/ShapeAtMg.lean: under the head the shape is the
      written one; the evaluation is Johnson/P5T/ShapeFacts.lean's)
  **`noAhead_at_head`**   so at T := the thread of `lettersHead …`, b := the number of segment l's batching in the
      head's own table (that it is the border above is typed here), at every link Lk and place p: what
      `rest_back_ahead` (Honest/K9/RestBack.lean) asks, at every stand; called by Honest/K9/TotalAtt.lean,
      TotalHead.lean and TotalLay.lean: "reached" by the frame's `thr_reach`, "no mark" by the thread's own form (what
      `head_form` says, by unfolding: not called)
No premise but the head and l < 25. At the full size and the format's second hash function alone: the head's.
GROUND: beside the sealed library, the frame's files (Honest/, Honest/Law/, Honest/Law/Rule/, Honest/Thread/: live,
not sealed) and our own (Honest/K9/). No other house's.
SINCE THIS FILE, at the head: the two premises that the head of Johnson/Desc/First/Link/Law/FrameFullOf.lean names
under its limits (`FoldFacts` itself; the closed test, "NOT EVALUATED HERE"), and "SHOWN OF NO SHAPE HERE" in that of
Johnson/LPFK9R/HallOfMoments.lean, are met by the calls above.
WHAT IS NOT CLAIMED. That a stand is there. Of a stand only the thread's half is spent (fit, step, bat: not); at a
link or place that is not the seated one a stand may not be there: idle, not false. No member of the head. Nothing on
any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.XkEqReach
import Johnson.Desc.ProofFile.Honest.K9.RwFrontAt
import Johnson.Desc.First.Link.Law.FrameFullOf
import Johnson.LPFK9R.HallOfMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- **Nothing is ahead at a reached state without a mark, in front of the batching.** -/
theorem ahead_none_reach {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s : S}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 2 + 0) (z, s)) (h0 : s.failed = none)
    (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) :
    ∀ a, Desc.K9.segAt? s = some a → ∀ c, Desc.K9.aheadIn sent own a c = none := by
  intro a ha
  obtain ⟨p, _, h1, _, h3, h4⟩ := LPFK9.HandsAt.place_W (l := l) (i := 0) hl (by omega)
  have FF := ProofFile.Honest.FirstThread.foldFacts_raw h.toAtMg
    (fun k (a : ProofFile.InstPub × S) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a) (fun _ _ hr => hr)
    (P5J.laid_at_head h.toAtMg) (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  rw [P5J.placesW_at] at h1
  have hn := LPFK9.HandsAt.hearN_W hl
  have h9 := LPFK9.HandsAt.nAt_le l
  refine LinkJoin.ahead_none_of_facts FF (14 * l + IM.nAt l + 2 + 0) (z, s) p l a hR h0 h1 h3 ha ?_ ?_
    (LPFK9.hall_of_moments _ _ _ _ _ l (h.toAtMg.shape_moments l)) sent own
  · rw [h4, hn]
    unfold IM.nAt shiftAt
    by_cases e : l = 24
    · subst e
      decide
    · rw [if_neg e]
      split <;> omega
  · rw [h4, hn]
    unfold IM.nAt shiftAt
    by_cases e : l = 24
    · subst e
      decide
    · rw [if_neg e]
      omega

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **Nothing is ahead at a stand of the batching, at the frame's own thread.** -/
theorem noAhead_at_head {l : ℕ} (hl : l < 25) (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where)
    (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) :
    ∀ κ s m En ds y cols s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G →
      ∀ a, Desc.K9.segAt? s = some a → ∀ c, Desc.K9.aheadIn sent own a c = none := by
  intro κ s m En ds y cols s' x' z G St
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb : batchAt P5J.At.links P5J.At.ps l = 14 * l + IM.nAt l + 2 + 0 := by
    by_cases e : l = 24
    · subst e
      rw [batch_at.2]
      rfl
    · rw [batch_at.1 l (by omega)]
      unfold IM.nAt
      rw [if_neg e]
  have h9 := LPFK9.HandsAt.nAt_le l
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb] at hq
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 St.thr.1.2.2.1.1
  exact ahead_none_reach h hl hq h0 sent own

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.ahead_none_reach
#print axioms ProofFile.Honest.K9.noAhead_at_head
