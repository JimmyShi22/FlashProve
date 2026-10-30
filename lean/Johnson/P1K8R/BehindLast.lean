-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BehindLast.lean: THE SMALLNESS TEST's SECOND FALL: THE SENTENCE OF
`share_fallDebt_left` (Johnson/P1K8R/BehindLeft.lean) WITH FOUR MORE PAYMENTS LAID IN: THE SAME
FallDebt WITH THE SAME WRITTEN NUMBER, UNDER THE SAME PREMISES; OF THE LETTER Q IT ASKS LESS:
`LiveFore` FOR `SecondFore` (`SecondLaid` HAS FALLEN WHOLE), `StillAtZ` FOR `StillAtL` (THE BOUND ON
THE MATRICES' ROWS OF CELLS AND THE FIELD here OF `StillAtt2` HAVE FALLEN). Definitions and lemmas;
NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  `LiveFore s'`, `StillAtZ Z Bs l s`   what is left of `SecondFore` and of `StillAtL`
  `built_there`   P1K8S.sitsAt_open (Johnson/P1K8R/OrderAtSeat.lean)
  **`secondLaid_reached`**   `secondLaid_at_batch` (Johnson/P1K8R/SecondLaidAtBatch.lean); its
      premise by `fronts_at_batch` (Johnson/Desc/K8/Honest/ArraysAtBatch.lean) and `hasRow_of_rows`
      (PlaneEqs.lean)
  **`secondFore_of_live`**, **`stillAtL_of_z`**   at the wrapped family: `cells_at_batch`
      (Johnson/P1K8R/CellsAtBatch.lean), `here_at_batch` (HereAtBatch.lean)
  **`share_fallDebt_last`**, **`share_fallDebt_last_blocks`**   `share_fallDebt_left`,
      `share_fallDebt_left_blocks` by one call each
Limits. THE OBLIGATION MOVES; IT IS NOT MET: `WrapEnd`, `ShareLive`, `LiveFore`, `StillAtZ` and
`RowsAsked Z` are premises; none is shown of any state or plan here. The fall's own stated share
stays a letter: the sentence's number is a written sum, not that share's value. No number is
evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.BehindLeft
import Johnson.P1K8R.CellsAtBatch
import Johnson.P1K8R.SecondLaidAtBatch
import Johnson.P1K8R.HereAtBatch
import Johnson.Desc.K8.Honest.ArraysAtBatch

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

/-- The second half of `SecondFore` (Johnson/P1K8R/CountedAtRch.lean), by a name: on what the lookup
on the digits has heard: weights that are not 0. -/
def LiveFore (s' : S) : Prop :=
  ∀ (tl : HTailF2) (F' : Fork), s'.tl? = some tl → s'.fork? = some F' →
    ∀ g₀ nbW W, tl.heard = some g₀ → tl.wants = some (nbW, W) → PieceLive tl g₀ W

/-- **What is left of `StillAtL` (Johnson/P1K8R/BehindLeft.lean)**: the field heard of `StillLeft`;
at the layers' segments what stood there; at the attention segments the field five of `StillAtt2`
(Johnson/P1K8R/BehindPaid.lean). -/
structure StillAtZ (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (l : ℕ) (s : S) : Prop where
  heard : ∀ tl, s.tl? = some tl → ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) →
    ∀ w ∈ W, (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n ∧
      g.e.getD w.call zeroE = callWeightAgain g w.call
  layers : ∀ g p4 o, l = 2 * g → g < 12 → LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 →
    s.own? = some o → ProofFile.Honest.K4.RunAsks p4 o 0
  five : ∀ (g : ℕ) (Ap : Attention.Plan), l = 2 * g + 1 → Bs.G₀.W.A[g]? = some Ap →
    ∃ hd, s.heard5? = some hd ∧ K5Law.HeardPlain hd

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope there is a built segment at each number below 25. -/
theorem built_there (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ∃ Xl, Bs.G₀.built[l]? = some Xl := by
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨-, -, Xl, -, -, -, hXl, -⟩ := P1K8S.sitsAt_open hS hR O _ hp
  exact ⟨Xl, hXl⟩

/-- **`SecondLaid`, WHOLE, AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING**: its second
clause by `fronts_at_batch` (Johnson/Desc/K8/Honest/ArraysAtBatch.lean): each matrix's array has one
virtual row. -/
theorem secondLaid_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    SecondLaid tl G :=
  secondLaid_at_batch hS hR O hl e3 h ht fun mu hmu =>
    hasRow_of_rows ((fronts_at_batch hS hR O hl e3 h ht hG).2.1.rows mu hmu) (by omega)

/-- `SecondFore` at a state that the wrapped blocks reach, from its second half. -/
theorem secondFore_of_live (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {s' : S}
    (w : WrapEnd Z c l s') (L : LiveFore s') : SecondFore s' := by
  obtain ⟨zp, h⟩ := w
  obtain ⟨Xl, e3⟩ := built_there hS hR O hl
  exact fun tl F' ht hF => ⟨secondLaid_reached hS hR O hl e3 (reach_raw h) ht hF, L tl F' ht hF⟩

/-- `StillAtL` at a state that the wrapped blocks reach, from `StillAtZ`. -/
theorem stillAtL_of_z (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {s' : S}
    (w : WrapEnd Z c l s') (T : StillAtZ Z Bs l s') : StillAtL Z Bs l s' := by
  obtain ⟨zp, h⟩ := w
  obtain ⟨Xl, e3⟩ := built_there hS hR O hl
  refine ⟨fun tl ht => ⟨cells_at_batch hS hR O hl e3 (reach_raw h) ht, T.heard tl ht⟩, T.layers,
    fun g Ap e hA => ?_⟩
  obtain ⟨hd, h5, hP⟩ := T.five g Ap e hA
  subst e
  have hg : g < 12 := by omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (zp, s') := by
    have r := reach_raw h
    rw [if_neg (by omega)] at r
    exact r
  exact ⟨⟨hd, h5, hP⟩, here_at_batch hS hR O hg hA h' h5⟩

/-- **THE SECOND FALL's SENTENCE AT THE WRAPPED FAMILY, WITH ALL PAYMENTS LAID IN: at typed
challenges.** The sentence and the number of `share_fallDebt_left` (Johnson/P1K8R/BehindLeft.lean);
of the letter Q it asks `LiveFore` where that one asks `SecondFore`, and `StillAtZ` where that one
asks `StillAtL`. -/
theorem share_fallDebt_last (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s' ∧ StillAtZ Z Bs l s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_left hE hS hR O hOk hl
  exact ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ =>
    H d he h5 h6 ft share Q fun fr s' hq =>
      ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1,
        secondFore_of_live hS hR O hl (hQ fr s' hq).1 (hQ fr s' hq).2.2.1,
        stillAtL_of_z hS hR O hl (hQ fr s' hq).1 (hQ fr s' hq).2.2.2⟩⟩

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_last_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s' ∧ StillAtZ Z Bs l s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_left_blocks hE hS hR O hOk hl
  exact ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ =>
    H d he h5 h6 ft share Q fun fr s' hq =>
      ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1,
        secondFore_of_live hS hR O hl (hQ fr s' hq).1 (hQ fr s' hq).2.2.1,
        stillAtL_of_z hS hR O hl (hQ fr s' hq).1 (hQ fr s' hq).2.2.2⟩⟩

end

end P1K8

#print axioms P1K8.LiveFore
#print axioms P1K8.StillAtZ
#print axioms P1K8.built_there
#print axioms P1K8.secondLaid_reached
#print axioms P1K8.secondFore_of_live
#print axioms P1K8.stillAtL_of_z
#print axioms P1K8.share_fallDebt_last
#print axioms P1K8.share_fallDebt_last_blocks
