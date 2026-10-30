-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverAsksReps.lean: a member of `FirstAsks`
(Honest/Law/CoverAsks.lean) from eight of its sixteen fields and three hypotheses on the file
(`hcut`, `cut`, `hpl`). The structure lists what `falls_asks` asks at a description's first chain.
Five fields speak of the chain's sub-protocols alone: `members_cut` (Honest/Law/CoverCut.lean)
proves them where the chain's cut into sub-protocols is the library's written one (`hcut`). Three
fields hold by a choice: the counted falls are laid as `repsAt` (Honest/Law/CoverReps.lean), which
proves `hin`, and the numbers `p₁` as `priceAt` (Honest/Law/CoverSum.lean), which proves `hp₁` and
`hp₂`. That the chain's places are distinct comes from the description's own test on its places
(`hpl`; `places_nodup`, Honest/Law/Cuts.lean).

  1  `firstAsks_reps`   the member

Limits.
  * The eight fields that are left (`hz`, `hfs`, `hseat`, `hq0`, `hM`, `hPM`, `hF`, `hP'`) are
    hypotheses. None is proved here of any description. At the list `fallsHead`,
    `fallsHead_seats_full` (Honest/Law/FallsHeadFull.lean) proves `hfs`.
  * `hcut`, `cut` and `hpl` are hypotheses here. `file_head` (Honest/Law/CoverHeadFile.lean) proves
    `hcut` and `hpl` of the proof file's description under the library's `P5J.AtMg`.
  * With these choices `hF` asks a bound for each fall of the list that stands near a sub-protocol
    with a round at a fall's seat, and the first chain's part of the bound of `falls_asks` is the
    sum of the stated numbers (`p₂` and `p₃` are free and may be 0).
  * The full size alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverAsksCut
import Johnson.Desc.ProofFile.Honest.Law.CoverReps
import Johnson.Desc.ProofFile.Honest.Law.CoverSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)

variable {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 : Type}

set_option maxHeartbeats 2000000 in
/-- A member of `FirstAsks` at `fallSeat`, `markSeat`, `repsAt` and `priceAt`, from `hcut`, `cut`,
`hpl` and the eight fields that are left. -/
theorem firstAsks_reps (C : CK) {F : FileDescription Xi} (fs : List (Fall F.S₁)) (hm : List Mark)
    {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl} (x : Xi)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (PM : Block F.S₁ F.Cl → List Fmt.Drawn → Prop) (qM : Block F.S₁ F.Cl → Mark → ℝ≥0∞)
    (P : Block F.S₁ F.Cl → List Fmt.Drawn → F.S₁ → Prop)
    (qF : Block F.S₁ F.Cl → Fall F.S₁ → ℝ≥0∞)
    (hcut : cutOf F.first.blocksInOrder = cutFirstFull) (cut : F.first.blocksInOrder = pre₁ ++ [e₁])
    (hpl : F.placesOk = true)
    (hz : ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hfs : ∀ f ∈ fs, (fallSeat P5J.At.links) f.place = true)
    (hseat : ∀ mk ∈ hm, markSeat mk.place = true)
    (hq0 : ∀ b ∈ pre₁, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy F.first.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (hF : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g ∈ repsAt F.first.blocksInOrder fs b, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g 0 b (b' :: B ++ [e₁]) dsb [] (P b) (qF b g))
    (hP' : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy F.first.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (F.first.blocksInOrder.map below) F.start₁ A.length (F.pub x, s')) →
      P b fr s') :
    FirstAsks C fs hm (priceAt pre₁ hm qM (repsAt F.first.blocksInOrder fs) qF) pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM P qF (repsAt F.first.blocksInOrder fs) :=
  firstAsks_cut C fs hm _ x Xc PM qM P qF _ hcut cut hz hfs hseat hq0 hM hPM hF
    (hin_reps cut (places_nodup hpl).1 fs _ P) hP'
    (hp₁_sum hm qM _ qF pre₁ _) (hp₂_sum hm qM _ qF pre₁ _)

end ProofFile.Honest

#print axioms ProofFile.Honest.firstAsks_reps
