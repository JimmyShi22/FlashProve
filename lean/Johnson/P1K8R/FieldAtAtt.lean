-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FieldAtAtt.lean: THE HONEST SIDE's FRAME: AT THE STATES THAT THE FIELD hP' HANDS AT A
RUN, AT THE BATCHING OF AN ATTENTION SEGMENT, THE THREE SENTENCES THAT THE BATCHING's AUTHORS' BOUND
ASKS OF THE STATE: `attClauses_handed` (Johnson/P1K8R/ClausesAtFrame.lean) IN THE FIELD's OWN WORDS,
AT THE FRAME's AUTHORS' LIST OF MARKS. Lemmas; NONE OF THE LIBRARY's GOALS. No new argument. Nothing
on completeness, soundness or hiding.

  **`length_of_member`**   List.getElem?_inj
  **`attE_handed`**   `attClauses_handed`; `handed_letters` (Johnson/P1K8R/HandedLetters.lean);
      `length_of_member`; LPFK9.places_nodup (Johnson/LPFK9R/ToldInScope.lean); k3_sub, k5_sub (the
      frame's authors')
Limits. fs and Pv are letters: no filling is named. What the field hands is the state of a walk that
returns, at challenges at which no mark asked has spoken: where there is none, nothing is said. That
any walk returns is proved nowhere here. What that silence costs is not told here. Four of the
field's premises are carried and not spent: the seat, "0 ≤", that no listed fall has been met, and
"reached". The head h is a hypothesis; the full size alone. One option is raised (maxHeartbeats).
Tactics that search: simp twice.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.FallsAtMarks
import Johnson.P1K8R.ClausesAtFrame
import Johnson.P1K8R.HandedLetters

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
open H2K5.Honest (HeldLive)
open ProofFile.Honest.K3.Good.Live (Clause)
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

/-- In a list whose images under f are distinct, the member b that stands behind A stands at no
other index. -/
theorem length_of_member {α β : Type} (f : α → β) {l A t : List α} {b : α}
    (hnd : (l.map f).Nodup) (hall : l = A ++ b :: t) {k : Nat} (hb : l[k]? = some b) :
    A.length = k := by
  have e0 : l[A.length]? = some b := by
    rw [hall]
    simp
  have hlt : A.length < (l.map f).length := by
    rw [hall]
    simp
  refine List.getElem?_inj hlt hnd ?_
  rw [List.getElem?_map, List.getElem?_map, e0, hb]

set_option maxHeartbeats 4000000 in
/-- **THE THREE SENTENCES AT AN ATTENTION SEGMENT's BATCHING, AT WHAT THE FIELD HANDS**: the
premises are the field hP''s own, at the marks marksHead and the fit's; the end is the second half
of the condition in `firstAsks_att`. -/
theorem attE_handed {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
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
      ∀ g, g < 12 → c.blocksInOrder[14 * (2 * g + 1) + 9]? = some b →
      ∀ a pC pD, (P5J.At.X Z).A[g]? = some a →
      Look.placeAt (P5J.At.X Z) (2 * g + 1) false = some pC →
      Look.placeAt (P5J.At.X Z) (2 * g + 1) true = some pD →
      HeldLive a.own (Forest.elems a.fs) s' ∧ Clause pC s'.lookHeard? ∧
        Clause pD (s'.tl?.bind (·.heard)) := by
  intro A b b' B e hs hr fr a z s' h1 h2 h3 h4 y1 y2 hv hw g hg hb pl pC pD ea hC hD
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  have hnd : (c.blocksInOrder.map (·.place)).Nodup := LPFK9.places_nodup h.scope h.reads O
  obtain ⟨hall₀, hft, ⟨m₀, hm₀, ha⟩, hlen, hq, hfit⟩ :=
    handed_letters (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R _ rfl
      (marksHead Z Bs.G₀) cut e h2 h4 y1
  have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := hall₀
  exact attClauses_handed h Bs.G₀ hB hg ea hC hD (marksHead Z Bs.G₀ ++ fitMarks pre₁)
    (fun mk hk => List.mem_append_left _ (k3_sub Z Bs.G₀ mk hk))
    (fun mk hk => List.mem_append_left _ (k5_sub Z Bs.G₀ mk hk)) hall hfit
    (length_of_member (·.place) hnd hall hb) (List.length_pos_iff.2 hr) _ hft hm₀ ha hlen hq y2 hv

end

end P1K8

#print axioms P1K8.length_of_member
#print axioms P1K8.attE_handed
