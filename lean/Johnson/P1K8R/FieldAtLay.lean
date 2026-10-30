-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FieldAtLay.lean: THE HONEST SIDE's FRAME: AT THE STATES THAT THE FIELD hP' HANDS AT A
RUN, AT THE BATCHING OF A FEED-FORWARD SEGMENT, THE ONE SENTENCE THAT THE BATCHING's AUTHORS' BOUND
ASKS OF THE STATE (THEIR BatFrontLay): THEIR batFrontLay_handed_marks IN THE FIELD's OWN WORDS, AT
THE FRAME's AUTHORS' LIST OF MARKS. A lemma; NONE OF THE LIBRARY's GOALS. No new argument. Nothing
on completeness, soundness or hiding.

  **`layE_handed`**   the batching's authors' batFrontLay_handed_marks
      (Johnson/Desc/ProofFile/Honest/K9/BatFrontHandedMarks.lean); `handed_letters`
      (Johnson/P1K8R/HandedLetters.lean); `length_of_member` (FieldAtAtt.lean); LPFK9.places_nodup
      (Johnson/LPFK9R/ToldInScope.lean); k3_sub, k4_sub (the frame's authors')
Limits. fs and Pv are letters: no filling is named. What the field hands is the state of a walk that
returns, at challenges at which no mark asked has spoken: the lookups' marks, the feed-forward
layers' wider marks and the fit's are spent: where there is no such walk, nothing is said. What that
silence costs is not told here. Four of the field's premises are carried and not spent: the seat, "0
≤", that no listed fall has been met, and "reached". THE BATCHING's AUTHORS' HEAVIEST LIMIT HOLDS:
their sentence is had at no run: no walk, state or list of marks is given at which the premises hold
together; that any walk returns is proved nowhere. THE BATCHING's AUTHORS' AND THE FEED-FORWARD
LAYERS' AUTHORS' OWN LIMITS HOLD: the event that the layers' fall names is not saved: it has moved
into the layers' own yes: whoever sums shares may not drop that fall's. The head h is a hypothesis;
the full size alone. One option is raised (maxHeartbeats). No tactic that searches.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.FieldAtAtt
import Johnson.Desc.ProofFile.Honest.K9.BatFrontHandedMarks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT WholeD chainsOf)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest.K3.Good (markK3 markOut)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt KindFits Fall Mark MarkDebt FirstAsks firstAsks_cut fellBy silentQ
  fitMarks drawsFit walk groupOf localFall ChainAt Local fallSeat markSeat cut_first repsAt
  priceAt hin_reps hp₁_sum hp₂_sum places_nodup ChainProgress Mid marksQuiet Prover Ready at₁
  letter_starts letter_tree file_head hz_head Sides ProverCoinCounts Coins ready fallAt drawsAt gates₁ gates₂
  gates₃ kit_two falls_five fallsFull fallsFull_seats marksHead qMHead hq0_head part1_sub k3_sub
  k5_sub k6_sub fallsHead linkFalls)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open ProofFile.Honest (k4_sub)
open H2K5.Honest (HeldLive)
open ProofFile.Honest.K3.Good.Live (Clause)
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

set_option maxHeartbeats 4000000 in
/-- **THE BATCHING's AUTHORS' SENTENCE AT A FEED-FORWARD SEGMENT's BATCHING, AT WHAT THE FIELD
HANDS**: the premises are the field hP''s own, at the marks marksHead and the fit's; the end is the
third part of the condition in `firstAsks_lay`. -/
theorem layE_handed {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs) (fs : List (Fall S))
    {Ky X₀ : Type} (Pv : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    {pre₁ : List (Block S Claim)} {e₁ : Block S Claim} (x : ProofFile.Inst)
    (w₀ : W₀) (rc : Rc) (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (cut : c.blocksInOrder = pre₁ ++ [e₁]) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R) (0 +
                             (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Z Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R).start = some a →
      walk (at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R).lay
        ((at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R).steps.take (0 + (A.flatMap
                      (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      ∀ g, g < 12 → c.blocksInOrder[14 * (2 * g) + 9]? = some b →
      ∀ p4 u, LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 →
      Desc.K9.testsWhere Z.p.X (2 * g) 0 = some u →
      ProofFile.Honest.K9.BatFrontLay p4 u.2.2.filled s' := by
  intro A b b' B e hs hr fr a z s' h1 h2 h3 h4 y1 y2 hv hw g hg hb p4 u e4 eu
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  have hnd : (c.blocksInOrder.map (·.place)).Nodup := LPFK9.places_nodup h.scope h.reads O
  obtain ⟨hall₀, hft, ⟨m₀, hm₀, ha⟩, hlen, hq, hfit⟩ :=
    handed_letters (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R _ rfl
      (marksHead Z Bs.G₀) cut e h2 h4 y1
  have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := hall₀
  exact ProofFile.Honest.K9.batFrontLay_handed_marks h hB Bs.G₀ hg (marksHead Z Bs.G₀ ++ fitMarks pre₁)
    (fun mk hk => List.mem_append_left _ (k3_sub Z Bs.G₀ mk hk))
    (fun mk hk => List.mem_append_left _ (k4_sub Z Bs.G₀ mk hk)) hall hfit
    (length_of_member (·.place) hnd hall hb) (List.length_pos_iff.2 hr) _ hft hm₀ ha hlen hq y2 hv
    e4 eu

end

end P1K8

#print axioms P1K8.layE_handed
