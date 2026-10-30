-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AsksLooks.lean: THE SMALLNESS TEST's SECOND FALL IN THE HONEST SIDE's FRAME: THE
MEMBER OF `FirstAsks` OF Johnson/P1K8R/AsksSymbols.lean WITH ONE TEST ALONE ASKED OF THE STATE AT
OUR 25 BLOCKS (`readsLive`): THE TWO TESTS ON WHAT THE LOOKUP ON THE DIGITS HAS HEARD (`planesLive`,
`digitsLive`) COME OF THE SILENCE OF THE LOOKUP's TWO MARKS, WHICH THE FRAME's FIELD HANDS;
`HeardAtZ` OF THE REACHED STATE THAT IT HANDS, AT ALL 25; `LiveFore` OF BOTH TOGETHER. AND THE
MEMBER UNDER THE DESCRIPTION's HEAD ALONE, AT THE SEATED DESCRIPTION's OWN TERM. Lemmas; NONE OF THE
LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  `ReadsStill`, `LooksMarked`, `restLive_of_looks`   the one test that is left; the premise on the
      list of marks
  **`firstAsks_looks_letter`**   `firstAsks_symbols_letter` by one call; `looks_below_handed`,
      `looks_head_handed` (Johnson/P1K8R/LooksAtFrame.lean); `liveFore_below_handed`,
      `liveFore_head_handed` (LiveForeAtFrame.lean); `heardAtZ_all` (StillAtAll.lean),
      `wrapEnd_of_handed` (LastAtFrame.lean); letter_starts, letter_tree
      (Johnson/Desc/ProofFile/Honest/Law/CoverLetter.lean)
  **`firstAsks_looks_head`**   the head's fields scope, reads, laid.opened, laid.planOk
      (Johnson/P5J/AtMg.lean, LaidOpens.lean)
Limits. As in the files beneath: A MEMBER UNDER PREMISES: NONE OF THEM IS SHOWN HERE OF ANYTHING,
NOR THAT THEY CAN BE MET TOGETHER. THREE OF FOUR TESTS, `LiveFore` AND `HeardAtZ` ARE PAID HERE;
`readsLive` STAYS ASKED OF THE STATE (it is paid in Johnson/P1K8R/AsksAllLive.lean). The head h is a
hypothesis; the full size alone. `LooksMarked` is a condition on the list of marks: whoever lays the
list pays it; IT BRINGS FIFTY MARKS MORE INTO hm, AND WITH THEM hseat AND hM AT EACH: neither is
paid here (for hM the files of the kind "lookup" have conditional bounds:
Johnson/Desc/ProofFile/Honest/K3/Good/MarkDebt.lean, MarkOut.lean). That the marks are silent is
what the field hands: the chance that they speak is their stated numbers' matter (hM). A prover, its
inputs and a `Ready` are letters: nothing is asked or shown of them. At strings of hash blocks
alone. Like every file of this road it takes a cone under Johnson/Goal/. `falls_asks` itself is not
called. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.AsksSymbols
import Johnson.P1K8R.LooksAtFrame
import Johnson.P1K8R.LiveForeAtFrame
import Johnson.P1K8R.StillAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT WholeD)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest.K3.Good (markK3 markOut)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt KindFits Fall Mark MarkDebt FirstAsks firstAsks_cut fellBy silentQ
  fitMarks drawsFit walk groupOf localFall ChainAt Local fallSeat markSeat cut_first repsAt
  priceAt hin_reps hp₁_sum hp₂_sum places_nodup ChainProgress Mid marksQuiet Prover Ready at₁
  letter_starts letter_tree)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

/-- The one of the four tests of `ShareLive` (Johnson/P1K8R/ShareLiveOf.lean) that is left: on the
closed list of tables. -/
def ReadsStill (s' : S) : Prop :=
  ∀ tl F', s'.tl? = some tl → s'.fork? = some F' → readsLive tl = true

/-- **The two marks of the lookup on the digits are among the marks asked, at each of the 25
segments**: at the place of the chain's own member there, at the face of the public part's own built
segment. -/
def LooksMarked (Z : ProofFile.Pub) (c : Chain S Claim) (hm : List Mark) : Prop :=
  ∀ l < 25, ∀ (X : LinkH) (blk : Block S Claim), Z.p.built.links[l]? = some X →
    c.blocksInOrder[borderOf l true]? = some blk →
    markK3 blk.place (K3.faceOf X.tl.f9) ∈ hm ∧ markOut blk.place (K3.faceOf X.tl.f9) ∈ hm

/-- With the two tests on what the lookup has heard it is `RestLive`. -/
theorem restLive_of_looks {s' : S} (h : ReadsStill s')
    (hs : ∃ tl, s'.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true) : RestLive s' := by
  intro tl F' ht hF
  obtain ⟨tl', ht', h1, h2⟩ := hs
  obtain rfl : tl' = tl := Option.some.inj (ht'.symm.trans ht)
  exact ⟨h1, h2, h tl' F' ht hF⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

set_option maxHeartbeats 4000000 in
/-- **`firstAsks_symbols_letter` (Johnson/P1K8R/AsksSymbols.lean) WITH ALL BUT ONE TEST PAID**: its
premise hLeft ends in `ReadsStill s'` where that one's ends in `RestLive s' ∧ LiveFore s' ∧ (l = 24
→ HeardAtZ s')`. Two premises more: the description's head h, at the opening's own letters Z and c
(its files Pz and the opening's P are two letters here; the head's form below lays them together),
and that the lookup's two marks are among those asked (hk3). `planesLive` and `digitsLive` by
`looks_below_handed`, `looks_head_handed` (Johnson/P1K8R/LooksAtFrame.lean); `HeardAtZ` by
`heardAtZ_all` (StillAtAll.lean) at the reached state that the field hands; `LiveFore` by
`liveFore_below_handed`, `liveFore_head_handed` (LiveForeAtFrame.lean) from the marks' silence and
`HeardAtZ`. -/
theorem firstAsks_looks_letter {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
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
    (hk3 : LooksMarked Z c hm)
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
      ReadsStill s') :
    FirstAsks (F := descAt Z A₂ B₂ c) (_root_.Run.ckP .two) fs hm
      (priceAt pre₁ hm qM (repsAt c.blocksInOrder fs) qF) pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF (repsAt c.blocksInOrder fs) := by
  refine firstAsks_symbols_letter hE hS hR O hOk fs hm x Xc PM qM Pr qF Pv w₀ rc R hXc hmk hcut cut
    hz hfs hseat hq0 hM hPM hFr hqF hPr ?_
  intro A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA
  have g2 := hLeft A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA
  have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
    rw [cut, e]
    simp
  have hH : HeardAtZ s' :=
    heardAtZ_all hS hR O hOk hl (wrapEnd_of_handed hS hR O hl hall hA hr)
  obtain ⟨m₀, hm₀, ha⟩ := letter_starts (descAt Z A₂ B₂ c) Pv w₀ rc x R Xc hXc _ a y1
  have hft := letter_tree (descAt Z A₂ B₂ c) Pv w₀ rc x R Xc hXc (fr.take 0)
  have htk : pre₁.take (0 + A.length) = A := by
    rw [e, Nat.zero_add]
    exact List.take_left' rfl
  have hq : marksQuiet (hm ++ fitMarks pre₁) A [] fr = true := by
    have h4' : marksQuiet (hm ++ fitMarks pre₁) (pre₁.take (0 + A.length)) (fr.take 0)
      (fr.drop 0) = true := h4
    rw [htk] at h4'
    exact h4'
  have hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ hm ++ fitMarks pre₁ := fun d hd =>
    List.mem_append_right _ (List.mem_map.2
      ⟨d, by rw [e]; exact List.mem_append_left _ hd, rfl⟩)
  obtain ⟨X, hX, -⟩ := hE l hl
  have hlen : A.length < c.blocksInOrder.length := by
    rw [hall, List.length_append, List.length_cons]
    omega
  by_cases h24 : l = 24
  · subst h24
    have hA' : A.length = 347 := hA
    have i5 : borderOf 24 true < c.blocksInOrder.length := by
      have e5 : borderOf 24 true = 345 := rfl
      omega
    have i6 : 346 < c.blocksInOrder.length := by omega
    obtain ⟨k3, ko⟩ := hk3 24 (by omega) X _ hX (List.getElem?_eq_getElem i5)
    exact ⟨restLive_of_looks g2 (looks_head_handed h hX (hm ++ fitMarks pre₁)
        (List.getElem?_eq_getElem i5) (List.getElem?_eq_getElem i6) (List.mem_append_left _ k3)
        (List.mem_append_left _ ko) hall hfit hA' (List.length_pos_iff.2 hn) _ hft hm₀ ha
        (by simpa using h2) hq y2 hv),
      liveFore_head_handed h hX (hm ++ fitMarks pre₁) (List.getElem?_eq_getElem i5)
        (List.getElem?_eq_getElem i6) (List.mem_append_left _ k3) (List.mem_append_left _ ko)
        hall hfit hA' (List.length_pos_iff.2 hn) _ hft hm₀ ha (by simpa using h2) hq y2 hv hH,
      fun _ => hH⟩
  · have hl' : l < 24 := by omega
    have hA' : A.length = 14 * l + 9 := by
      rw [hA, if_neg h24]
    have i8 : borderOf l true < c.blocksInOrder.length := by
      have e8 := border_next hl'
      omega
    obtain ⟨k3, ko⟩ := hk3 l hl X _ hX (List.getElem?_eq_getElem i8)
    exact ⟨restLive_of_looks g2 (looks_below_handed h hl' hX (hm ++ fitMarks pre₁)
        (List.getElem?_eq_getElem i8) (List.mem_append_left _ k3) (List.mem_append_left _ ko)
        hall hfit hA' (List.length_pos_iff.2 hn) _ hft hm₀ ha (by simpa using h2) hq y2 hv),
      liveFore_below_handed h hl' hX (hm ++ fitMarks pre₁) (List.getElem?_eq_getElem i8)
        (List.mem_append_left _ k3) (List.mem_append_left _ ko) hall hfit hA'
        (List.length_pos_iff.2 hn) _ hft hm₀ ha (by simpa using h2) hq y2 hv hH,
      fun _ => hH⟩

set_option maxHeartbeats 4000000 in
/-- **THE SAME UNDER THE DESCRIPTION's HEAD ALONE, AT THE SEATED DESCRIPTION's OWN TERM**
(`P5J.F0T`, Johnson/P5J/AtTerm.lean): scope, reader, opening and the test on the plan are the head's
own fields; hB says which base Bs is. -/
theorem firstAsks_looks_head {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs) (hE : RowsAsked Z)
    (fs : List (Fall S)) (hm : List Mark) {pre₁ : List (Block S Claim)}
    {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop) (qM : Block S Claim → Mark → ℝ≥0∞)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    {Ky X₀ : Type} (Pv : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁) (w₀ : W₀) (rc : Rc)
    (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hXc : Xc = fun _ => at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R)
    (hmk : ∀ mk ∈ part1Marks Z Bs.G₀, mk ∈ hm)
    (hk3 : LooksMarked Z c hm)
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
      ReadsStill s') :
    FirstAsks (F := P5J.F0T OnBytes.secondHashFunction Z Np c) (_root_.Run.ckP .two) fs hm
      (priceAt pre₁ hm qM (repsAt c.blocksInOrder fs) qF) pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF (repsAt c.blocksInOrder fs) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact firstAsks_looks_letter h hE h.scope h.reads O h.laid.planOk fs hm x Xc PM qM Pr qF Pv w₀
    rc R hXc hmk hk3 hcut cut hz hfs hseat hq0 hM hPM hFr hqF hPr hLeft

end

end P1K8

#print axioms P1K8.ReadsStill
#print axioms P1K8.LooksMarked
#print axioms P1K8.restLive_of_looks
#print axioms P1K8.firstAsks_looks_letter
#print axioms P1K8.firstAsks_looks_head
