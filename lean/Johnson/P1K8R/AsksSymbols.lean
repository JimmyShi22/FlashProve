-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AsksSymbols.lean: THE SMALLNESS TEST's SECOND FALL IN THE HONEST SIDE's FRAME: THE
MEMBER OF `FirstAsks` OF Johnson/P1K8R/AsksReps.lean WITH LESS ASKED AT OUR 25 BLOCKS: THE TEST ON
THE DRAWN MATRIX (`symbolsLive`) COMES OF THE SILENCE OF TWO MARKS, WHICH THE FRAME's FIELD HANDS.
Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  `RestLive`, `shareLive_of_rest`   the three tests that are left; with the fourth they are
      `ShareLive`
  `dead_mem_part1`   the mark stands in `part1Marks` (Johnson/P1K8R/Part1MarksCode.lean):
      `part1Marks_eq` (Part1Marks.lean)
  **`firstAsks_symbols_reps`**   `firstAsks_head_reps` by one call; `symbols_at_handed`,
      `built_there` (Johnson/P1K8R/BehindLast.lean), K8.fits_sizeAt (Johnson/Desc/First/K8/Law.lean)
  **`firstAsks_symbols_letter`**   the same at the frame's authors' own `at₁`: letter_starts,
      letter_tree (Johnson/Desc/ProofFile/Honest/Law/CoverLetter.lean)
Limits. As in the files beneath: A MEMBER UNDER PREMISES: NONE OF THEM IS SHOWN HERE OF ANYTHING,
NOR THAT THEY CAN BE MET TOGETHER. IN THE FIRST FORM THREE PREMISES MORE THAN THERE: hX and hft, in
the form of the ends of the frame's authors' letter_starts and letter_tree; hmk: a condition on the
list of marks. IN THE SECOND FORM hX and hft are paid, at their `at₁`; a prover, its inputs and a
`Ready` are letters there: nothing is asked or shown of them. ONE OF FOUR TESTS IS PAID. At strings
of hash blocks alone. Like every file of this road it takes a cone under Johnson/Goal/ (through the
sealed Johnson/IMR/ seats). `falls_asks` itself is not called. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.AsksReps
import Johnson.P1K8R.SymbolsAtFrame
import Johnson.P1K8R.Part1Marks
import Johnson.Desc.ProofFile.Honest.Law.CoverLetter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt KindFits Fall Mark MarkDebt FirstAsks firstAsks_cut fellBy silentQ
  fitMarks drawsFit walk groupOf localFall ChainAt Local fallSeat markSeat cut_first repsAt
  priceAt hin_reps hp₁_sum hp₂_sum places_nodup ChainProgress Mid marksQuiet Prover Ready at₁
  letter_starts letter_tree)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

/-- Three of the four tests of `ShareLive` (Johnson/P1K8R/ShareLiveOf.lean): all but the one on the
drawn matrix. -/
def RestLive (s' : S) : Prop :=
  ∀ tl F', s'.tl? = some tl → s'.fork? = some F' →
    planesLive tl = true ∧ digitsLive tl = true ∧ readsLive tl = true

/-- With the fourth test they are `ShareLive`. -/
theorem shareLive_of_rest {s' : S} (h : RestLive s')
    (hs : ∃ tl, s'.tl? = some tl ∧ symbolsLive tl = true) : ShareLive s' := by
  intro tl F' ht hF
  obtain ⟨tl', ht', hl'⟩ := hs
  obtain rfl : tl' = tl := Option.some.inj (ht'.symm.trans ht)
  obtain ⟨h1, h2, h3⟩ := h tl' F' ht hF
  exact ⟨h1, h2, h3, hl'⟩

/-- The mark "a column of the drawn matrix is all 0" at a built segment stands in part 1's list. -/
theorem dead_mem_part1 (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) {l : ℕ} (hl : l < 25) {X : LinkH}
    (hX : G₀.built[l]? = some X) :
    deadMark l (if l = 24 then 1 else 0) (szAt Zp G₀ X l) ∈ part1Marks Zp G₀ := by
  rw [part1Marks_eq]
  refine List.mem_append_left _ (List.mem_filterMap.2 ⟨l, List.mem_range.2 hl, ?_⟩)
  rw [hX]
  rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

set_option maxHeartbeats 2000000 in
/-- **`firstAsks_head_reps` (Johnson/P1K8R/AsksReps.lean) WITH THE FIRST OF `ShareLive`'s FOUR TESTS
PAID FROM THE MARKS' SILENCE**: in its premise hLeft `RestLive s'` stands in `ShareLive s'`'s place.
Three premises more: the frame's own law on where the chain's walk starts (hX: at the empty list of
columns) at first tree 0 (hft), and that part 1's marks are among those asked (hmk). By
`symbols_at_handed` (Johnson/P1K8R/SymbolsAtFrame.lean) at what the field hands. -/
theorem firstAsks_symbols_reps (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hOk : F.planOk = true)
    (fs : List (Fall S)) (hm : List Mark) {pre₁ : List (Block S Claim)}
    {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop) (qM : Block S Claim → Mark → ℝ≥0∞)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (hX : ∀ base a, (Xc base).start = some a → ∃ m₀ : Option (Mid (Local W₀ Rc ProofFile.Inst Tr) X₁),
      m₀.isSome = true ∧
        ChainProgress.start (Xc base).lay c.blocksInOrder m₀ (some (ProofFile.startS Z x.pub)) [] = .ok a)
    (hft : ∀ base, (Xc base).lay.firstTree = 0)
    (hmk : ∀ mk ∈ part1Marks Z Bs.G₀, mk ∈ hm)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hz : ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hfs : ∀ f ∈ fs, (fallSeat P5J.At.links) f.place = true)
    (hseat : ∀ mk ∈ hm, markSeat mk.place = true)
    (hq0 : ∀ b ∈ pre₁, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (qM b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (hFr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g ∈ repsAt c.blocksInOrder fs b, ¬ ShareFallAt Bs (k8ShareAt Z Bs.G₀) A.length g → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) g 0 b (b' :: B ++ [e₁]) dsb []
        (PWith Z c Bs Pr b) (qF b g))
    (hqF : ∀ b g, g.share.val ≤ qF b g)
    (hPr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      Pr b fr s')
    (hLeft : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      ∀ l, l < 25 → A.length = 14 * l + (if l = 24 then 11 else 9) →
      RestLive s' ∧ LiveFore s' ∧ (l = 24 → HeardAtZ s')) :
    FirstAsks (F := descAt Z A₂ B₂ c) (_root_.Run.ckP .two) fs hm
      (priceAt pre₁ hm qM (repsAt c.blocksInOrder fs) qF) pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF (repsAt c.blocksInOrder fs) := by
  refine firstAsks_head_reps hE hS hR O hOk fs hm x Xc PM qM Pr qF hcut cut hz hfs hseat hq0
    hM hPM hFr hqF hPr ?_
  intro A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA
  obtain ⟨g2, g3, g4⟩ := hLeft A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA
  refine ⟨shareLive_of_rest g2 ?_, g3, g4⟩
  have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
    rw [cut, e]
    simp
  obtain ⟨X, hXl⟩ := built_there hS hR O hl
  obtain ⟨m₀, hm₀, ha⟩ := hX _ a y1
  have htk : pre₁.take (0 + A.length) = A := by
    rw [e, Nat.zero_add]
    exact List.take_left' rfl
  have hq : marksQuiet (hm ++ fitMarks pre₁) A [] fr = true := by
    have h4' : marksQuiet (hm ++ fitMarks pre₁) (pre₁.take (0 + A.length)) (fr.take 0)
      (fr.drop 0) = true := h4
    rw [htk] at h4'
    exact h4'
  exact symbols_at_handed hS hR O hl hXl (hm ++ fitMarks pre₁)
    (sz := szAt Z Bs.G₀ X l) (K8.fits_sizeAt (ProofFile.k8Par Z Bs.G₀ X l) _)
    (List.mem_append_left _ (hmk _ (dead_mem_part1 Z Bs.G₀ hl hXl))) hall
    (fun d hd => List.mem_append_right _ (List.mem_map.2
      ⟨d, by rw [e]; exact List.mem_append_left _ hd, rfl⟩))
    hA (List.length_pos_iff.2 hn) _ (hft _) hm₀ ha (by simpa using h2) hq y2 hv

set_option maxHeartbeats 2000000 in
/-- **The same AT THE FRAME's AUTHORS' OWN CHOICE OF WHERE THE WALK STARTS** (`at₁`,
Johnson/Desc/ProofFile/Honest/Law/CoverFile.lean: the one that their `falls_asks` takes): hX and hft
are their theorems there: letter_starts, letter_tree (CoverLetter.lean). -/
theorem firstAsks_symbols_letter (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hOk : F.planOk = true)
    (fs : List (Fall S)) (hm : List Mark) {pre₁ : List (Block S Claim)}
    {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop) (qM : Block S Claim → Mark → ℝ≥0∞)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    {Ky X₀ : Type} (Pv : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁) (w₀ : W₀) (rc : Rc)
    (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hXc : Xc = fun _ => at₁ (descAt Z A₂ B₂ c) Pv w₀ rc x R)
    (hmk : ∀ mk ∈ part1Marks Z Bs.G₀, mk ∈ hm)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hz : ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hfs : ∀ f ∈ fs, (fallSeat P5J.At.links) f.place = true)
    (hseat : ∀ mk ∈ hm, markSeat mk.place = true)
    (hq0 : ∀ b ∈ pre₁, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (qM b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (hFr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g ∈ repsAt c.blocksInOrder fs b, ¬ ShareFallAt Bs (k8ShareAt Z Bs.G₀) A.length g → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) g 0 b (b' :: B ++ [e₁]) dsb []
        (PWith Z c Bs Pr b) (qF b g))
    (hqF : ∀ b g, g.share.val ≤ qF b g)
    (hPr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      Pr b fr s')
    (hLeft : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      ∀ l, l < 25 → A.length = 14 * l + (if l = 24 then 11 else 9) →
      RestLive s' ∧ LiveFore s' ∧ (l = 24 → HeardAtZ s')) :
    FirstAsks (F := descAt Z A₂ B₂ c) (_root_.Run.ckP .two) fs hm
      (priceAt pre₁ hm qM (repsAt c.blocksInOrder fs) qF) pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF (repsAt c.blocksInOrder fs) :=
  firstAsks_symbols_reps hE hS hR O hOk fs hm x Xc PM qM Pr qF
    (letter_starts (descAt Z A₂ B₂ c) Pv w₀ rc x R Xc hXc)
    (letter_tree (descAt Z A₂ B₂ c) Pv w₀ rc x R Xc hXc) hmk hcut cut hz hfs hseat hq0 hM hPM hFr
    hqF hPr hLeft

end

end P1K8

#print axioms P1K8.RestLive
#print axioms P1K8.shareLive_of_rest
#print axioms P1K8.dead_mem_part1
#print axioms P1K8.firstAsks_symbols_reps
#print axioms P1K8.firstAsks_symbols_letter
