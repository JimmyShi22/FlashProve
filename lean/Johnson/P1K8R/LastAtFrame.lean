-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LastAtFrame.lean: THE SMALLNESS TEST's SECOND FALL: THE SENTENCE OF
`share_fallDebt_last` (Johnson/P1K8R/BehindLast.lean) IN THE FORM IN WHICH THE HONEST SIDE's FRAME
TAKES A STATEMENT ON ONE FALL (the hypotheses hF and hP' of `localDebts_own`,
Johnson/Desc/ProofFile/Honest/Law/CoverOwn.lean): AT ALL DATA THAT FIT THE BATCHING BLOCK's DECLARED
ROUNDS; WITH ONE CONDITION `PLast` FOR THE LETTER P; AND `WrapEnd`, THE FIRST OF `PLast`'s FOUR
CLAUSES, IS WHAT THAT FRAME HANDS TO WHOEVER PROVES P. A definition and lemmas; NONE OF THE
LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding. THE FRAME's FILE IS NOT
IMPORTED: the forms were read off its text; no call of `localDebts_own` is typed here.

  `PLast Z c Bs l`   the four clauses as one condition
  `one_of_fits`, `batch_rounds_are`   the block has one declared round, of K9's entry (IM.k9_of,
      Johnson/IMR/LinkSeat.lean; IM.alone_rounds, SeatForm.lean; P1K8S.batch_behind,
      Johnson/P1K8R/WideAtSeat.lean); data that fit it (KindFits,
      Johnson/Desc/ProofFile/Honest/Law/Due.lean) are one round's, of the kind "elements"
  `drop_split`   the list behind the block, in the frame's form
  **`wrapEnd_of_handed`**, **`last_hP`**   `WrapEnd` from the reached state that the frame hands;
      `PLast` from it and the three clauses left
  **`last_hF`**, **`last_hF_blocks`**   `share_fallDebt_last`, `share_fallDebt_last_blocks` by one
      call each
Limits. THE OBLIGATION MOVES; IT IS NOT MET: `ShareLive`, `LiveFore`, `StillAtZ` and `RowsAsked Z`
are premises; none is shown of any state or plan here. At first tree 0 and the description's own
start alone. That the frame's other hypotheses can be met is not spoken of. The fall's own stated
share stays a letter: the sentence's number is a written sum, not that share's value. No number is
evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.BehindLast
import Johnson.Desc.ProofFile.Honest.Law.Due

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
open ProofFile.Honest (Odds FallDebt KindFits)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

/-- **What `share_fallDebt_last` (Johnson/P1K8R/BehindLast.lean) asks of its letter Q, as one
condition on the challenges in front and the verifier's state in front of the batching of the
segment l**, in the form of the letter P of the frame's `FallDebt`. The challenges are not read. -/
def PLast (Z : ProofFile.Pub) (c : Chain S Claim) (Bs : ProofFile.PureBase) (l : ℕ) :
    List Fmt.Drawn → S → Prop :=
  fun _ s' => WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s' ∧ StillAtZ Z Bs l s'

/-- Data that fit the batching's one declared round are one round's, of its entry, and of a kind
that is neither "seeds" nor "sealed": the entry's name is of the kind "elements". -/
theorem one_of_fits {p : K9.Where} {dsb : List RDT}
    (h : List.Forall₂ KindFits dsb [({ entry := K9.entry p } : Fmt.DeclaredRound)]) :
    ∃ d, dsb = [d] ∧ d.entry = K9.entry p ∧ d.kind ≠ .seeds ∧ d.kind ≠ .sealed := by
  cases h with
  | cons hd ht =>
    cases ht
    obtain ⟨e1, e2⟩ := hd
    have hk : Fmt.kindOf "BAT-sigma" = some Fmt.Kind.elems := by decide
    have ek := Option.some.inj (hk.symm.trans e2)
    refine ⟨_, rfl, e1, ?_, ?_⟩
    · rw [← ek]
      decide
    · rw [← ek]
      decide

/-- A list cut as (A ++ b :: b' :: B) ++ R, with its first A.length + 1 members dropped, is
b' :: B ++ R: the list behind b, in the frame's form. -/
theorem drop_split {α : Type} {L A B R : List α} {b b' : α}
    (h : L = (A ++ b :: b' :: B) ++ R) : L.drop (A.length + 1) = b' :: B ++ R := by
  rw [h, List.append_assoc, show A.length + 1 = (A ++ [b]).length by simp,
    show A ++ (b :: b' :: B ++ R) = (A ++ [b]) ++ (b' :: B ++ R) by simp]
  exact List.drop_left

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The seated batching block's rounds**: one, of K9's entry at the segment's numbers. -/
theorem batch_rounds_are (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {b : Block S Claim} (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b)
    {p : K9.Where} (hp : IM.k9At Z l = some p) : b.rounds = [{ entry := K9.entry p }] := by
  obtain ⟨Lk', p', w, T, e1', hp', -, -, -, -, hbL, -⟩ := (IM.k9_of hS hR O).2 l hl
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨Lk, e1, hflat⟩ := P1K8S.batch_behind hS hR O _ hx
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have hflat' : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? =
      some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
    rw [← e]
    exact hflat
  obtain rfl := Option.some.inj (hflat'.symm.trans hb)
  rw [IM.alone_rounds (hbL _)]
  rfl

/-- **`WrapEnd` IS WHAT THE FRAME HANDS**: the last premise of the hypothesis hP' of the frame's
`localDebts_own` (Johnson/Desc/ProofFile/Honest/Law/CoverOwn.lean, not imported here), at the first
chain's list, the description's own start and first tree 0, where the list is cut at the batching
of the segment l. -/
theorem wrapEnd_of_handed (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {A₀ t : List (Block S Claim)} {b : Block S Claim} (hall : c.blocksInOrder = A₀ ++ b :: t)
    (hA : A₀.length = 14 * l + (if l = 24 then 11 else 9)) {zp : ProofFile.InstPub} {s' : S}
    (h : b.rounds ≠ [] →
      Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A₀.length (zp, s')) :
    WrapEnd Z c l s' := by
  have hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b := by
    rw [hall, ← hA]
    simp
  obtain ⟨-, p, -, -, -, hp, -⟩ := (IM.k9_of hS hR O).2 l hl
  have hr : b.rounds ≠ [] := by
    rw [batch_rounds_are hS hR O hl hb hp]
    simp
  have r := h hr
  rw [hA] at r
  exact ⟨zp, r⟩

/-- **SO `PLast` AT WHAT THE FRAME HANDS, FROM THE THREE THAT ARE LEFT.** -/
theorem last_hP (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {A₀ t : List (Block S Claim)} {b : Block S Claim} (hall : c.blocksInOrder = A₀ ++ b :: t)
    (hA : A₀.length = 14 * l + (if l = 24 then 11 else 9)) {zp : ProofFile.InstPub} {s' : S}
    (h : b.rounds ≠ [] →
      Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A₀.length (zp, s'))
    (h2 : ShareLive s') (h3 : LiveFore s') (h4 : StillAtZ Z Bs l s') (fr : List Fmt.Drawn) :
    PLast Z c Bs l fr s' :=
  ⟨wrapEnd_of_handed hS hR O hl hall hA h, h2, h3, h4⟩

/-- **THE SECOND FALL's SENTENCE IN THE FORM OF THE FRAME's HYPOTHESIS hF: at typed challenges**:
at all data that fit the block's declared rounds, with `PLast` for the letter P. The sentence and
the number of `share_fallDebt_last`. With `drop_split` the list behind is the frame's. -/
theorem last_hF (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (ft : ℕ) (share : Odds) (dsb : List RDT), List.Forall₂ KindFits dsb b.rounds →
        FallDebt (_root_.Run.ck .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) dsb [] (PLast Z c Bs l)
          ((((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
              (((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) + 0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_last hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun ft share dsb hd => ?_⟩
  rw [batch_rounds_are hS hR O hl hb hp] at hd
  obtain ⟨d, rfl, e1, e2, e3⟩ := one_of_fits hd
  exact H d e1 e2 e3 ft share (PLast Z c Bs l) fun _ _ h => h

/-- **The same at strings of hash blocks.** -/
theorem last_hF_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (ft : ℕ) (share : Odds) (dsb : List RDT), List.Forall₂ KindFits dsb b.rounds →
        FallDebt (_root_.Run.ckP .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) dsb [] (PLast Z c Bs l)
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
                0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_last_blocks hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun ft share dsb hd => ?_⟩
  rw [batch_rounds_are hS hR O hl hb hp] at hd
  obtain ⟨d, rfl, e1, e2, e3⟩ := one_of_fits hd
  exact H d e1 e2 e3 ft share (PLast Z c Bs l) fun _ _ h => h

end

end P1K8

#print axioms P1K8.PLast
#print axioms P1K8.one_of_fits
#print axioms P1K8.drop_split
#print axioms P1K8.batch_rounds_are
#print axioms P1K8.wrapEnd_of_handed
#print axioms P1K8.last_hP
#print axioms P1K8.last_hF
#print axioms P1K8.last_hF_blocks
