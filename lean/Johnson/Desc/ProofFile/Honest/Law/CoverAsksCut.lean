-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverAsksCut.lean: a member of `FirstAsks`
(Honest/Law/CoverAsks.lean) from eleven of its sixteen fields and two hypotheses on the chain
(`hcut`, `cut`). The structure lists what `falls_asks` asks at a description's first chain. Five of
its fields speak of the chain's sub-protocols alone: where the last ones stand and which have a
round. `members_cut` (Honest/Law/CoverCut.lean) proves these five where the chain's cut into
sub-protocols is the library's written one (`hcut`) and the two tests on a place are `fallSeat` and
`markSeat` (Honest/Law/CoverSeats.lean).

  1  `firstAsks_cut`   the member

Limits.
  * The eleven fields that are left (`hz`, `hfs`, `hseat`, `hq0`, `hM`, `hPM`, `hF`, `hin`, `hP'`,
    `hp₁`, `hp₂`) are hypotheses. None is proved here of any description.
  * `hcut` is a hypothesis here. `members_head` (Honest/Law/CoverCutHead.lean) shows where the
    library proves it, under the hypothesis `P5J.AtMg`.
  * The full size alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverAsks
import Johnson.Desc.ProofFile.Honest.Law.CoverCut

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
/-- A member of `FirstAsks` at `fallSeat` and `markSeat`, from `hcut`, `cut` and the eleven fields
that do not speak of the chain's sub-protocols alone. -/
theorem firstAsks_cut (C : CK) {F : FileDescription Xi} (fs : List (Fall F.S₁)) (hm : List Mark)
    (p₁ : Nat → ℝ≥0∞) {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl} (x : Xi)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (PM : Block F.S₁ F.Cl → List Fmt.Drawn → Prop) (qM : Block F.S₁ F.Cl → Mark → ℝ≥0∞)
    (P : Block F.S₁ F.Cl → List Fmt.Drawn → F.S₁ → Prop)
    (qF : Block F.S₁ F.Cl → Fall F.S₁ → ℝ≥0∞) (reps : Block F.S₁ F.Cl → List (Fall F.S₁))
    (hcut : cutOf F.first.blocksInOrder = cutFirstFull) (cut : F.first.blocksInOrder = pre₁ ++ [e₁])
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
      ∀ g ∈ reps b, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g 0 b (b' :: B ++ [e₁]) dsb [] (P b) (qF b g))
    (hin : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ [e₁]), f.place = d.place) →
      ∃ g ∈ reps b, ∀ fr s' own, P b fr s' →
        localFall [f] 0 (b :: (b' :: B ++ [e₁])) s' own →
        localFall [g] 0 (b :: (b' :: B ++ [e₁])) s' own)
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
      P b fr s')
    (hp₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        p₁ (0 + A.length))
    (hp₂ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = false →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤ p₁ (0 + A.length)) :
    FirstAsks C fs hm p₁ pre₁ e₁ x Xc (fallSeat P5J.At.links) markSeat PM qM P qF reps :=
  { hz := hz, hfs := hfs, hseat := hseat, Hs := (members_cut hcut cut).1
    he := (members_cut hcut cut).2.1, hlast := (members_cut hcut cut).2.2.1
    hend := (members_cut hcut cut).2.2.2.1, hmr := (members_cut hcut cut).2.2.2.2.1, hq0 := hq0
    hM := hM, hPM := hPM, hF := hF, hin := hin, hP' := hP', hp₁ := hp₁, hp₂ := hp₂ }

end ProofFile.Honest

#print axioms ProofFile.Honest.firstAsks_cut
