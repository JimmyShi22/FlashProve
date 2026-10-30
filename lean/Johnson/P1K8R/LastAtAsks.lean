-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LastAtAsks.lean: THE SMALLNESS TEST's SECOND FALL, LAID INTO THE HONEST SIDE's FRAME:
A MEMBER OF THE FRAME's STRUCTURE `FirstAsks` (Johnson/Desc/ProofFile/Honest/Law/CoverAsks.lean:
what its theorem `falls_asks`, the bound on the chance that a run meets a fall, asks at a
description's first chain), AT THE PROOF FILE's OWN DESCRIPTION, IN WHICH THE CLAUSE OF THE FIELD hF
AT OUR FALL AT EACH OF THE 25 BATCHINGS IS `last_hF` (Johnson/P1K8R/LastAtFrame.lean), AND `WrapEnd`
AT THESE BLOCKS COMES OUT OF THE FIELD hP''s OWN LAST PREMISE. Definitions and lemmas; NONE OF THE
LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  `shareNumber`, `shareNumberB`   the written sums of `share_fallDebt_last`,
      `share_fallDebt_last_blocks`, by names
  `ShareFallAt`, `PWith`   which counted fall is ours; the condition for all gated sub-protocols:
      the others' Pr, and `PLast` at our blocks
  `fallDebt_mono`   a bound on one fall stands under a stronger condition and at a larger number
  `length_of_cut`   cut_first (Johnson/Desc/ProofFile/Honest/Law/Cuts.lean)
  **`firstAsks_share_blocks`**, **`firstAsks_share`**   the member: `firstAsks_cut`
      (CoverAsksCut.lean)
Limits. A MEMBER UNDER PREMISES: NONE OF THEM IS SHOWN HERE OF ANYTHING, NOR THAT THEY CAN BE MET
TOGETHER: nine of the frame's eleven fields as they stand (hz, hfs, hseat, hq0, hM, hPM, hin, hp₁,
hp₂); hcut and cut; the bounds for all other counted falls (hFr), among them the smallness test's
first fall and the batching's authors' fall at the same blocks; the others' condition (hPr); hq; at
our blocks `ShareLive`, `LiveFore` and `StillAtZ` (hLeft); and `RowsAsked Z`. hin and hFr speak of
`PWith`. `falls_asks` itself is not called. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LastAtFrame
import Johnson.P1K8R.FallAtRun
import Johnson.Desc.ProofFile.Honest.Law.CoverAsksCut

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
  fitMarks drawsFit walk groupOf localFall ChainAt Local fallSeat markSeat cut_first)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

/-- The written sum of `share_fallDebt_last` (Johnson/P1K8R/BehindLast.lean), by a name: at typed
challenges. -/
noncomputable def shareNumber (Bs : ProofFile.PureBase) (p : K9.Where) (X : LinkH) : ℝ≥0∞ :=
  ((((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
  ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
  ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) + 0))))))

/-- The same at strings of hash blocks. -/
noncomputable def shareNumberB (Bs : ProofFile.PureBase) (p : K9.Where) (X : LinkH) : ℝ≥0∞ :=
  (kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
  ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (kapSl 128 ^ 3 * ((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
  ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (kapSl 128 ^ 3 * ((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) /
  ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (kapSl 128 ^ 3 * ((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) /
  ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (kapSl 128 ^ 3 * ((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) /
  ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  (kapSl 128 ^ 3 * ((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
  0))))))

/-- The fall g is the smallness test's second fall of a segment l, with the share that `share`
states for l, and n is the number of that segment's batching in the first chain's list. -/
def ShareFallAt (Bs : ProofFile.PureBase) (share : ℕ → Odds) (n : ℕ) (g : Fall S) : Prop :=
  ∃ l X, l < 25 ∧ n = 14 * l + (if l = 24 then 11 else 9) ∧ Bs.G₀.built.toList[l]? = some X ∧
    g = k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) (share l)

/-- **A condition for all gated sub-protocols**: the others' condition Pr, and besides, at the
batching of a segment l, `PLast` (Johnson/P1K8R/LastAtFrame.lean). -/
def PWith (Z : ProofFile.Pub) (c : Chain S Claim) (Bs : ProofFile.PureBase)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) :
    Block S Claim → List Fmt.Drawn → S → Prop :=
  fun b fr s' => Pr b fr s' ∧
    ∀ l, l < 25 → c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b → PLast Z c Bs l fr s'

/-- A bound on one fall stands under a stronger condition and at a larger number. -/
theorem fallDebt_mono {C : _root_.Run.PQ.CK} {f : Fall S} {ft : ℕ} {b : Block S Claim}
    {t : List (Block S Claim)} {dsb : List RDT} {tl : List Fmt.Drawn}
    {Q Q' : List Fmt.Drawn → S → Prop} {q q' : ℝ≥0∞} (h : FallDebt C f ft b t dsb tl Q q)
    (hQ : ∀ fr s', Q' fr s' → Q fr s') (hq : q ≤ q') : FallDebt C f ft b t dsb tl Q' q' :=
  fun fr s' h' => le_trans (h fr s' (hQ fr s' h')) hq

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

/-- Where no two sub-protocols stand at one place, a cut of the first chain's list at a member says
that member's number. -/
theorem length_of_cut (hpl : (descAt Z A₂ B₂ c).placesOk = true) {A t : List (Block S Claim)}
    {b : Block S Claim} (hall : c.blocksInOrder = A ++ b :: t) {n : ℕ} (hb : c.blocksInOrder[n]? = some b) :
    A.length = n := by
  obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.1 hb
  have hsp : c.blocksInOrder = c.blocksInOrder.take n ++ b :: c.blocksInOrder.drop (n + 1) := by
    rw [← hg, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  obtain ⟨eA, -⟩ := cut_first (F := descAt Z A₂ B₂ c) hpl hall hsp
  rw [eA, List.length_take]
  omega

set_option maxHeartbeats 2000000 in
/-- **A MEMBER OF THE FRAME's `FirstAsks` (Johnson/Desc/ProofFile/Honest/Law/CoverAsks.lean) AT THE
PROOF FILE's DESCRIPTION, WITH THE SECOND FALL's SENTENCE LAID IN AT ALL 25 BATCHINGS: at strings of
hash blocks.** By `firstAsks_cut` (CoverAsksCut.lean, in the form whose four fields ask a round of
the block). Of its eleven fields nine are premises here as they stand there. Its hF is asked as it
stands there, at `PWith`, for every counted fall but ours (hFr); ours is `last_hF_blocks`, at any
number that is at least the written sum (hq). Its hP' is asked at Pr (hPr); at our blocks `WrapEnd`
comes out of that field's own last premise, and the three clauses left are asked (hLeft). -/
theorem firstAsks_share_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hOk : F.planOk = true)
    (fs : List (Fall S)) (hm : List Mark) (p₁ : ℕ → ℝ≥0∞) {pre₁ : List (Block S Claim)}
    {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop) (qM : Block S Claim → Mark → ℝ≥0∞)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (reps : Block S Claim → List (Fall S)) (share : ℕ → Odds)
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
      ∀ g ∈ reps b, ¬ ShareFallAt Bs share A.length g → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) g 0 b (b' :: B ++ [e₁]) dsb []
        (PWith Z c Bs Pr b) (qF b g))
    (hq : ∀ l, l < 25 → ∀ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b → IM.k9At Z l = some p →
      Bs.G₀.built.toList[l]? = some X →
      shareNumberB Bs p X ≤
        qF b (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) (share l)))
    (hin : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ [e₁]), f.place = d.place) →
      ∃ g ∈ reps b, ∀ fr s' own, PWith Z c Bs Pr b fr s' →
        localFall [f] 0 (b :: (b' :: B ++ [e₁])) s' own →
        localFall [g] 0 (b :: (b' :: B ++ [e₁])) s' own)
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
      ShareLive s' ∧ LiveFore s' ∧ StillAtZ Z Bs l s')
    (hp₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        p₁ (0 + A.length))
    (hp₂ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = false →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤ p₁ (0 + A.length)) :
    FirstAsks (F := descAt Z A₂ B₂ c) (_root_.Run.ckP .two) fs hm p₁ pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF reps := by
  have hpl : (descAt Z A₂ B₂ c).placesOk = true := by
    have h := ((FileDescription.planOk_ok F).1 hOk).places
    rw [O.desc] at h
    exact h
  refine firstAsks_cut (F := descAt Z A₂ B₂ c) (_root_.Run.ckP .two) fs hm p₁ x Xc PM qM
    (PWith Z c Bs Pr) qF reps hcut cut hz hfs hseat hq0 hM hPM ?_ hin ?_ hp₁ hp₂
  · intro (A : List (Block S Claim)) (b : Block S Claim) (b' : Block S Claim)
      (B : List (Block S Claim)) e hs hn (g : Fall S) hg dsb hd
    have e' : pre₁ = A ++ b :: b' :: B := e
    by_cases ho : ShareFallAt Bs share A.length g
    · obtain ⟨l, X, hl, hA, hX, rfl⟩ := ho
      obtain ⟨b₀, p, X₀, hb₀, hp, hX₀, H⟩ := last_hF_blocks hE hS hR O hOk hl
      have hall : c.blocksInOrder = (A ++ b :: b' :: B) ++ [e₁] := by rw [cut, e']
      have hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b := by
        rw [hall, ← hA]
        simp
      obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
      obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
      have D := H 0 (share l) dsb hd
      rw [← hA, drop_split hall] at D
      exact fallDebt_mono D (fun _ _ h => h.2 l hl hb) (hq l hl _ p _ hb hp hX)
    · exact hFr A b b' B e hs hn g hg ho dsb hd
  · intro (A : List (Block S Claim)) (b : Block S Claim) (b' : Block S Claim)
      (B : List (Block S Claim)) e hs hn fr a z (s' : S) h1 h2 h3 h4 y1 y2 hv hr
    have e' : pre₁ = A ++ b :: b' :: B := e
    refine ⟨hPr A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr, fun l hl hb => ?_⟩
    have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
      rw [cut, e']
      simp
    have hA : A.length = 14 * l + (if l = 24 then 11 else 9) :=
      length_of_cut hpl hall hb
    obtain ⟨g2, g3, g4⟩ := hLeft A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA
    exact last_hP hS hR O hl hall hA hr g2 g3 g4 fr

set_option maxHeartbeats 2000000 in
/-- **The same at typed challenges.** -/
theorem firstAsks_share (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hOk : F.planOk = true)
    (fs : List (Fall S)) (hm : List Mark) (p₁ : ℕ → ℝ≥0∞) {pre₁ : List (Block S Claim)}
    {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop) (qM : Block S Claim → Mark → ℝ≥0∞)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (reps : Block S Claim → List (Fall S)) (share : ℕ → Odds)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hz : ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hfs : ∀ f ∈ fs, (fallSeat P5J.At.links) f.place = true)
    (hseat : ∀ mk ∈ hm, markSeat mk.place = true)
    (hq0 : ∀ b ∈ pre₁, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt (_root_.Run.ck .two) mk dsb (PM b) (qM b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (hFr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g ∈ reps b, ¬ ShareFallAt Bs share A.length g → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ck .two) g 0 b (b' :: B ++ [e₁]) dsb []
        (PWith Z c Bs Pr b) (qF b g))
    (hq : ∀ l, l < 25 → ∀ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b → IM.k9At Z l = some p →
      Bs.G₀.built.toList[l]? = some X →
      shareNumber Bs p X ≤
        qF b (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) (share l)))
    (hin : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ [e₁]), f.place = d.place) →
      ∃ g ∈ reps b, ∀ fr s' own, PWith Z c Bs Pr b fr s' →
        localFall [f] 0 (b :: (b' :: B ++ [e₁])) s' own →
        localFall [g] 0 (b :: (b' :: B ++ [e₁])) s' own)
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
      ShareLive s' ∧ LiveFore s' ∧ StillAtZ Z Bs l s')
    (hp₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        p₁ (0 + A.length))
    (hp₂ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = false →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤ p₁ (0 + A.length)) :
    FirstAsks (F := descAt Z A₂ B₂ c) (_root_.Run.ck .two) fs hm p₁ pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF reps := by
  have hpl : (descAt Z A₂ B₂ c).placesOk = true := by
    have h := ((FileDescription.planOk_ok F).1 hOk).places
    rw [O.desc] at h
    exact h
  refine firstAsks_cut (F := descAt Z A₂ B₂ c) (_root_.Run.ck .two) fs hm p₁ x Xc PM qM
    (PWith Z c Bs Pr) qF reps hcut cut hz hfs hseat hq0 hM hPM ?_ hin ?_ hp₁ hp₂
  · intro (A : List (Block S Claim)) (b : Block S Claim) (b' : Block S Claim)
      (B : List (Block S Claim)) e hs hn (g : Fall S) hg dsb hd
    have e' : pre₁ = A ++ b :: b' :: B := e
    by_cases ho : ShareFallAt Bs share A.length g
    · obtain ⟨l, X, hl, hA, hX, rfl⟩ := ho
      obtain ⟨b₀, p, X₀, hb₀, hp, hX₀, H⟩ := last_hF hE hS hR O hOk hl
      have hall : c.blocksInOrder = (A ++ b :: b' :: B) ++ [e₁] := by rw [cut, e']
      have hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b := by
        rw [hall, ← hA]
        simp
      obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
      obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
      have D := H 0 (share l) dsb hd
      rw [← hA, drop_split hall] at D
      exact fallDebt_mono D (fun _ _ h => h.2 l hl hb) (hq l hl _ p _ hb hp hX)
    · exact hFr A b b' B e hs hn g hg ho dsb hd
  · intro (A : List (Block S Claim)) (b : Block S Claim) (b' : Block S Claim)
      (B : List (Block S Claim)) e hs hn fr a z (s' : S) h1 h2 h3 h4 y1 y2 hv hr
    have e' : pre₁ = A ++ b :: b' :: B := e
    refine ⟨hPr A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr, fun l hl hb => ?_⟩
    have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
      rw [cut, e']
      simp
    have hA : A.length = 14 * l + (if l = 24 then 11 else 9) :=
      length_of_cut hpl hall hb
    obtain ⟨g2, g3, g4⟩ := hLeft A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA
    exact last_hP hS hR O hl hall hA hr g2 g3 g4 fr

end

end P1K8

#print axioms P1K8.shareNumber
#print axioms P1K8.shareNumberB
#print axioms P1K8.ShareFallAt
#print axioms P1K8.PWith
#print axioms P1K8.fallDebt_mono
#print axioms P1K8.length_of_cut
#print axioms P1K8.firstAsks_share_blocks
#print axioms P1K8.firstAsks_share
