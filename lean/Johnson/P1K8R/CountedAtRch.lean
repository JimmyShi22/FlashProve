-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/CountedAtRch.lean: THE SMALLNESS TEST's SECOND FALL: THE SENTENCE OF
`share_fallDebt_counted` (Johnson/P1K8R/SecondCount.lean) AT THE STATES THAT THE WRAPPED BLOCKS
REACH (RchAt, Johnson/Top/H0/Walk/ReachAt.lean): THE SAME FallDebt WITH THE SAME WRITTEN NUMBER; OF
THE LETTER Q IT ASKS `WrapEnd` WHERE THAT ONE ASKS `FoldEnd`, AND, WHERE THAT ONE ASKS `SecondOwed`,
ITS FIRST CLAUSE AND THE LIST `StillAt`. UNDER THE SCOPE, THE FILES READ, IM.Open, `RowsAsked Z`
AND, MORE THAN THAT ONE, THE DESCRIPTION's TEST ON ITS PLAN. Definitions, a structure and lemmas;
NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding. Why. The second clause of
`SecondOwed`, `SecondEqs` behind every yes, follows at such a state from what
Johnson/P1K8R/BehindPaid.lean leaves; at the head's segment the library's laws on what the head has
heard stand at the wrapped family alone.

  `WrapEnd Z c l s'`   the wrapped blocks reach s' in front of the batching of the segment l
  `SecondFore s'`   the first clause of `SecondOwed`, by a name
  `StillAt Z Bs l s`   what BehindPaid.lean leaves, at the segment l, whatever its sort: three
      fields
  `foldEnd_of_wrap`   `WrapEnd` gives `FoldEnd` (Johnson/P1K8R/DebtsK8.lean): reach_raw,
      reach_fold (Johnson/Top/H0/Walk/Reach.lean)
  `there_at_wrap`   the data and a ledger are there: `u2_at_batch` (Johnson/P1K8R/ThirdTie.lean),
      `sized_at_batch` (HeardAtBatch.lean), `head_at_rch` (BehindAtRch.lean)
  **`behind_at_wrap`**   `BehindEqs` at all 25 segments in one sentence: `paid_rch_layers`,
      `paid_rch_att`, `paid_rch_head`
  **`secondOwed_at_wrap`**   `SecondOwed` there: `secondOwed_of` (SecondOwedOf.lean)
  **`share_fallDebt_wrapped`**, **`share_fallDebt_wrapped_blocks`**   `share_fallDebt_counted`,
      `share_fallDebt_counted_blocks` by one call each
Limits. THE OBLIGATION MOVES; IT IS NOT MET: `WrapEnd`, `ShareLive`, `SecondFore`, `StillAt` and
`RowsAsked Z` are premises; none is shown of any state or plan here. Whoever fills Q must show its
states reached by the wrapped blocks. The fall's own stated share stays a letter: the sentence's
number is a written sum, not that share's value. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.BehindPaid
import Johnson.P1K8R.SecondOwedOf

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
open ProofFile.Honest (Odds FallDebt)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

/-- **The state is one that the WRAPPED blocks reach in front of the batching of the segment l**:
RchAt (Johnson/Top/H0/Walk/ReachAt.lean) at the opened letters, unfolded. -/
def WrapEnd (Z : ProofFile.Pub) (c : Chain S Claim) (l : ℕ) (s' : S) : Prop :=
  ∃ zp : ProofFile.InstPub, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
    (14 * l + (if l = 24 then 11 else 9)) (zp, s')

/-- The first clause of `SecondOwed` (Johnson/P1K8R/SecondCount.lean), by a name: what is asked in
front of the batching on the frame and on what the lookup has heard. -/
def SecondFore (s' : S) : Prop :=
  ∀ tl F', s'.tl? = some tl → s'.fork? = some F' → SecondLaid tl F' ∧
    ∀ g₀ nbW W, tl.heard = some g₀ → tl.wants = some (nbW, W) → PieceLive tl g₀ W

/-- **What is left for `SecondEqs` behind every yes, at the segment l, whatever its sort**: what
Johnson/P1K8R/BehindPaid.lean leaves at the wrapped blocks, each at its own sort of segment. At an
even l below 24 the field layers speaks, at an odd l the field att, and the other holds emptily; at
l = 24 both do. The field row of `StillCore` is the second clause of `SecondLaid`
(Johnson/Desc/K8/Honest/SecondFew.lean), which `SecondFore` asks too: beside `SecondFore` it asks
nothing more. -/
structure StillAt (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (l : ℕ) (s : S) : Prop where
  core : ∀ Xl tl G, Bs.G₀.built[l]? = some Xl → s.tl? = some tl → s.fork? = some G →
    StillCore Xl tl G
  layers : ∀ g p4 o, l = 2 * g → g < 12 → LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 →
    s.own? = some o → ProofFile.Honest.K4.RunAsks p4 o 0
  att : ∀ g Ap, l = 2 * g + 1 → Bs.G₀.W.A[g]? = some Ap → StillAtt2 Ap s

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- What the wrapped blocks reach is the end of a fold over the chain's own blocks. -/
theorem foldEnd_of_wrap {l : ℕ} {s' : S} (w : WrapEnd Z c l s') : FoldEnd Z c l s' := by
  obtain ⟨zp, h⟩ := w
  obtain ⟨-, rs, cols, f⟩ := reach_fold.1 (reach_raw h)
  exact ⟨zp, rs, [], cols, [], f⟩

/-- **At such a state the data and a ledger are there**, at all 25 segments. -/
theorem there_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {s' : S} (w : WrapEnd Z c l s') :
    ∃ tl G, s'.tl? = some tl ∧ s'.fork? = some G := by
  obtain ⟨zp, h⟩ := w
  obtain ⟨tl, ht, -⟩ := u2_at_batch hS hR O hl (reach_raw h)
  by_cases h24 : l = 24
  · rw [if_pos h24] at h
    subst h24
    have r : RchAt (P4.FD Z A B c) 347 ((zp, s'), ()) := h
    obtain ⟨o, ho, hop, -⟩ := head_at_rch hS hR O hOk _ r
    have ho' : s'.here = .head o := ho
    exact ⟨tl, o.F, ht, by simp [S.fork?, ho', hop]⟩
  · rw [if_neg h24] at h
    obtain ⟨G, hG, -⟩ := sized_at_batch hS hR O hOk (l := l) (by omega) (reach_raw h)
    exact ⟨tl, G, ht, hG⟩

/-- **`SecondEqs` BEHIND EVERY YES OF THE SEATED BATCHING BLOCK, AT ALL 25 SEGMENTS IN ONE
SENTENCE**: `paid_rch_layers`, `paid_rch_att`, `paid_rch_head` (Johnson/P1K8R/BehindPaid.lean), each
at its sort. -/
theorem behind_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {b : Block S Claim}
    (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) {s' : S}
    (w : WrapEnd Z c l s') (T : StillAt Z Bs l s') : BehindEqs b s' := by
  obtain ⟨tl, G, ht, hG⟩ := there_at_wrap hS hR O hOk hl w
  obtain ⟨zp, h⟩ := w
  by_cases h24 : l = 24
  · rw [if_pos h24] at h hb
    subst h24
    have r : RchAt (P4.FD Z A B c) 347 ((zp, s'), ()) := h
    have hb2 : c.blocksInOrder[347]? = some b := hb
    obtain ⟨b', Xl, hb', e3, H⟩ := paid_rch_head hS hR O hOk
    obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb2)
    exact H Unit _ r tl G ht hG (T.core Xl tl G e3 ht hG)
  · rw [if_neg h24] at h hb
    obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    rcases hg with rfl | rfl
    · have hg : g < 12 := by omega
      rw [show 14 * (2 * g) + 9 = 28 * g + 9 by omega] at h hb
      have r : RchAt (P4.FD Z A B c) (28 * g + 9) ((zp, s'), ()) := h
      obtain ⟨b', p4, Xl, hb', hp, e3, H⟩ := paid_rch_layers hS hR O hOk hg
      obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
      exact H Unit _ r tl G ht hG (T.core Xl tl G e3 ht hG)
        fun o ho => T.layers g p4 o rfl hg hp ho
    · have hg : g < 12 := by omega
      have r : RchAt (P4.FD Z A B c) (14 * (2 * g + 1) + 9) ((zp, s'), ()) := h
      obtain ⟨b', Ap, Xl, hb', hA, e3, H⟩ := paid_rch_att hS hR O hOk hg
      obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
      exact H Unit _ r tl G ht hG (T.core Xl tl G e3 ht hG) (T.att g Ap rfl hA)

/-- **`SecondOwed` at such a state**, from its first clause and `StillAt`. -/
theorem secondOwed_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {b : Block S Claim}
    (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) {s' : S}
    (w : WrapEnd Z c l s') (h1 : SecondFore s') (T : StillAt Z Bs l s') : SecondOwed b s' :=
  secondOwed_of h1 (behind_at_wrap hS hR O hOk hl hb w T)

/-- **THE SECOND FALL's SENTENCE AT THE WRAPPED FAMILY: at typed challenges.** The sentence and the
number of `share_fallDebt_counted` (Johnson/P1K8R/SecondCount.lean); what is asked of the letter Q
is other: `WrapEnd` for `FoldEnd`, and for `SecondOwed` its first clause and `StillAt`. One premise
more stands in front: the description's test on its plan (hOk). -/
theorem share_fallDebt_wrapped (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ SecondFore s' ∧ StillAt Z Bs l s') →
        FallDebt (_root_.Run.ck .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          ((((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
              (((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) + 0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_counted hE hS hR O hl
  exact ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ =>
    H d he h5 h6 ft share Q fun fr s' hq =>
      ⟨foldEnd_of_wrap (hQ fr s' hq).1, (hQ fr s' hq).2.1,
        secondOwed_at_wrap hS hR O hOk hl hb (hQ fr s' hq).1 (hQ fr s' hq).2.2.1
          (hQ fr s' hq).2.2.2⟩⟩

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_wrapped_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ SecondFore s' ∧ StillAt Z Bs l s') →
        FallDebt (_root_.Run.ckP .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_counted_blocks hE hS hR O hl
  exact ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ =>
    H d he h5 h6 ft share Q fun fr s' hq =>
      ⟨foldEnd_of_wrap (hQ fr s' hq).1, (hQ fr s' hq).2.1,
        secondOwed_at_wrap hS hR O hOk hl hb (hQ fr s' hq).1 (hQ fr s' hq).2.2.1
          (hQ fr s' hq).2.2.2⟩⟩

end

end P1K8

#print axioms P1K8.WrapEnd
#print axioms P1K8.SecondFore
#print axioms P1K8.StillAt
#print axioms P1K8.foldEnd_of_wrap
#print axioms P1K8.there_at_wrap
#print axioms P1K8.behind_at_wrap
#print axioms P1K8.secondOwed_at_wrap
#print axioms P1K8.share_fallDebt_wrapped
#print axioms P1K8.share_fallDebt_wrapped_blocks
