-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BehindLeft.lean: THE SMALLNESS TEST's SECOND FALL: THE SENTENCE OF
`share_fallDebt_wrapped` (Johnson/P1K8R/CountedAtRch.lean) WITH THREE PAYMENTS LAID IN: THE SAME
FallDebt WITH THE SAME WRITTEN NUMBER; OF THE LETTER Q IT ASKS, WHERE THAT ONE ASKS `StillCore`
(five fields; Johnson/P1K8R/BehindPaid.lean), `StillLeft`: ONE BOUND ON PLANNED NUMBERS AND TWO
SENTENCES ON WHAT THE LOOKUP ON THE DIGITS HAS HEARD. UNDER THE SAME PREMISES. Structures and
lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  `StillLeft tl`, `StillAtL Z Bs l s`   what is left of `StillCore`; `StillAt` with it
  **`stillCore_at_batch`**   static: `static_at_built` (Johnson/P1K8R/StaticAtBuilt.lean); front:
      `drawn_at_batch`, `tieFront_of_drawn` (DrawAtBatch.lean) and the field cells; want:
      `want_at_batch`, `pieceFront_of_planned` (WantAtBatch.lean) and the field heard; rows:
      `rows_at_batch` (WantAtBatch.lean); row: a premise
  **`stillAt_of_left`**   at the wrapped family; row out of `SecondFore`
  **`share_fallDebt_left`**, **`share_fallDebt_left_blocks`**   `share_fallDebt_wrapped`,
      `share_fallDebt_wrapped_blocks` by one call each
Limits. THE OBLIGATION MOVES; IT IS NOT MET: `WrapEnd`, `ShareLive`, `SecondFore`, `StillAtL` and
`RowsAsked Z` are premises; none is shown of any state or plan here. At the layers
ProofFile.Honest.K4.RunAsks, at attention `StillAtt2` stay as they were. The fall's own stated share stays
a letter: the sentence's number is a written sum, not that share's value. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.CountedAtRch
import Johnson.P1K8R.WantAtBatch

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

/-- **What is left of `StillCore` (Johnson/P1K8R/BehindPaid.lean) at a state that is reached in
front of a batching, beside `SecondFore`**: one bound on planned numbers, and two sentences on what
the lookup on the digits has heard, at every expected piece. -/
structure StillLeft (tl : HTailF2) : Prop where
  cells : ∀ nu, nu < tl.NM → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64
  heard : ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) → ∀ w ∈ W,
    (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n ∧
      g.e.getD w.call zeroE = callWeightAgain g w.call

/-- `StillAt` (Johnson/P1K8R/CountedAtRch.lean) with `StillLeft` for `StillCore`. -/
structure StillAtL (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (l : ℕ) (s : S) : Prop where
  left : ∀ tl, s.tl? = some tl → StillLeft tl
  layers : ∀ g p4 o, l = 2 * g → g < 12 → LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 →
    s.own? = some o → ProofFile.Honest.K4.RunAsks p4 o 0
  att : ∀ g Ap, l = 2 * g + 1 → Bs.G₀.W.A[g]? = some Ap → StillAtt2 Ap s

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`StillCore` AT EVERY STATE THAT THE CHAIN's OWN BLOCKS REACH IN FRONT OF A BATCHING, FROM
`StillLeft` AND "EACH MATRIX's ARRAY HAS A VIRTUAL ROW 0"**, at all 25 segments. -/
theorem stillCore_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    (hr : ∀ mu, mu < tl.NM → Fo.HasRow G (tl.gtTree.getD mu 0) 0) (L : StillLeft tl) :
    StillCore Xl tl G := by
  obtain ⟨t, a, D, hT⟩ := drawn_at_batch hS hR O hl h
  rw [Option.some.inj (a.symm.trans ht)] at D hT
  exact ⟨static_at_built hS O hl e3, tieFront_of_drawn hT L.cells D, hr,
    fun g nbW W hg hw w hm =>
      pieceFront_of_planned (want_at_batch hS hR O hOk hl e3 h ht nbW W hw w hm)
        (L.heard g nbW W hg hw w hm).1 (L.heard g nbW W hg hw w hm).2,
    rows_at_batch hS hR O hOk hl e3 h ht hG⟩

/-- **`StillAt` at a state that the wrapped blocks reach**, from `SecondFore` and `StillAtL`: the
virtual rows are the second clause of `SecondLaid` (Johnson/Desc/K8/Honest/SecondFew.lean). -/
theorem stillAt_of_left (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {s' : S} (w : WrapEnd Z c l s') (h1 : SecondFore s')
    (T : StillAtL Z Bs l s') : StillAt Z Bs l s' := by
  obtain ⟨zp, h⟩ := w
  exact ⟨fun Xl tl G e3 ht hG =>
    stillCore_at_batch hS hR O hOk hl e3 (reach_raw h) ht hG (h1 tl G ht hG).1.2.1 (T.left tl ht),
    T.layers, T.att⟩

/-- **THE SECOND FALL's SENTENCE AT THE WRAPPED FAMILY, WITH THE PAYMENTS LAID IN: at typed
challenges.** The sentence and the number of `share_fallDebt_wrapped`
(Johnson/P1K8R/CountedAtRch.lean); of the letter Q it asks `StillAtL` where that one asks
`StillAt`. -/
theorem share_fallDebt_left (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ SecondFore s' ∧ StillAtL Z Bs l s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_wrapped hE hS hR O hOk hl
  exact ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ =>
    H d he h5 h6 ft share Q fun fr s' hq =>
      ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1, (hQ fr s' hq).2.2.1,
        stillAt_of_left hS hR O hOk hl (hQ fr s' hq).1 (hQ fr s' hq).2.2.1 (hQ fr s' hq).2.2.2⟩⟩

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_left_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ SecondFore s' ∧ StillAtL Z Bs l s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_wrapped_blocks hE hS hR O hOk hl
  exact ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ =>
    H d he h5 h6 ft share Q fun fr s' hq =>
      ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1, (hQ fr s' hq).2.2.1,
        stillAt_of_left hS hR O hOk hl (hQ fr s' hq).1 (hQ fr s' hq).2.2.1 (hQ fr s' hq).2.2.2⟩⟩

end

end P1K8

#print axioms P1K8.StillLeft
#print axioms P1K8.StillAtL
#print axioms P1K8.stillCore_at_batch
#print axioms P1K8.stillAt_of_left
#print axioms P1K8.share_fallDebt_left
#print axioms P1K8.share_fallDebt_left_blocks
