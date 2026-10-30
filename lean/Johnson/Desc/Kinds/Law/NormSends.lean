-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormSends.lean.
What it does not show. A toy: an honest prover's tape built in Lean,
at the kind's own hearing text, for cells that hold: NO FILE IN SCOPE, no stored proof, not what the
prover's program sends. THAT CELLS WHICH HOLD EXIST is a premise ((dataOf c).Holds). That the ledger
which the verifier makes in front of the head is WellLaid and Fresh: premises (fresh_ledger shows
that such ledgers exist). THE END VALUES ARE ARBITRARY HERE: so nothing is said yet on the norm's 26
forms (that the rows and the end values' forms are worth 0): norm_level and norm_products hand out
"the row is worth 0 in every world that fits" for whoever picks the end values. "normed" and the
head's own sumcheck: not here. No soundness, no probability, nothing on hiding.
WHAT IT IS. THE SENDER OF THE NORM's ROUNDS, BESIDE THE TEXT (Norm.lean: hear), AND THAT NormTruth
(Law/NormTrue.lean) CAN BE MET, FOR ALL DRAWS.
  all_rests, hide_hidden, shownOf (a hidden scalar is shown with its mask entry), start_value_at
  norm_front     the point's round and the nine sums' round: the hidden sums are the true ones at
                 pV; the squares' start form has a public part; its hidden value IS the sum sigS.
  norm_level     the squares' level: at Law/LevelLaw.lean's own muT and tqL: SquaresTrue.
  batch_honest   a batching round.
  norm_products  the products' sumcheck: at Law/SumLaw.lean's own muG and tqG: ProductsTrue.
  norm_sends     FOR EVERY point, batching elements, eps, challenges, LINE's element and end values
                 (canonical writings, the right lengths): THERE ARE rounds rs, canonical, with
                 Norm.hear F rs = some (H, G, []), NormTruth c mask F rs, and so (norm_true)
                 Sound.NoBad (normRuleC c mask F) rs; the draws are the given; G is Fresh.
  fresh_ledger   a fresh ledger of n numbers is WellLaid and Fresh.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HonestParts
import Johnson.Desc.Kinds.Law.PublicPart
import Johnson.Desc.Kinds.Law.NormTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE okE)
open OnBytes.Model (Aff Fork Reading World)
open Polynomial
open Norm (lt ls d lPd T S2)
open Came (val bind_eq Consumes)
open Part.MaskedSum (rvOf readAll leadScalars movesOf ownSlots rowForm)
open OnBytes.Desc.First.P1 (honest honest_poly)
open Came (vsG kG cvG tqG muG specG hcoefG tqL specL hcoefL SHL)

/-! ## Tools -/

theorem all_rests {α : Type} {x : Hear α} (hx : Consumes x) {F G : Fork} {p : List Fmt.RoundView} {a : α}
    (h : x F p = some (a, G, [])) : ∀ q, x F (p ++ q) = some (a, G, q) := by
  obtain ⟨pre, e, c⟩ := hx _ _ _ _ _ h
  rw [List.append_nil] at e
  subst e
  exact c

/-- The hidden scalars behind a laying with the factor 1. -/
theorem hide_hidden {F Fa : Fork} (hW : WellLaid F) {v : List E} {c : Array Hid}
    (h : hide v F [] = some (c, Fa, [])) (mask : Nat → E) {s : Nat} (hs : s < v.length) :
    rd (hidden Fa mask (F.next + s)) = rd (v.getD s zeroE) - rd (mask (F.next + s)) := by
  obtain ⟨run, _⟩ := hide_unfold h
  obtain ⟨_, _, _, w4, w5⟩ := hideRun_frame
    (F := ({ F with next := F.next + v.length } : Fork)) hW run
  unfold hidden
  rw [w4, w5, if_pos ⟨by omega, by rw [List.size_toArray]; omega⟩,
    if_pos ⟨by omega, by rw [List.size_toArray]; omega⟩, rd_sub, rd_mul]
  have e1 : rd oneE = 1 := Reading.gl.one
  have e2 : v.toArray.toList.getD (F.next + s - F.next) (0 : E) = v.getD s zeroE := by
    rw [Nat.add_sub_cancel_left]
    show v.getD s (0 : E) = v.getD s zeroE
    rw [List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ hs]
  rw [e1, e2, one_mul]

/-- What an honest prover shows for n hidden scalars v 0, v 1, ..: each with its mask entry. -/
noncomputable def shownOf (mask : Nat → E) (first n : Nat) (v : Nat → K) : List E :=
  (List.range n).map fun s => ofK (v s + rd (mask (first + s)))

theorem shownOf_length (mask : Nat → E) (first n : Nat) (v : Nat → K) :
    (shownOf mask first n v).length = n := by
  unfold shownOf
  rw [List.length_map, List.length_range]

theorem shownOf_ok (mask : Nat → E) (first n : Nat) (v : Nat → K) :
    ∀ x ∈ shownOf mask first n v, okE x = true := by
  intro x hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
  exact okE_ofK _

theorem shownOf_getD (mask : Nat → E) (first n : Nat) (v : Nat → K) {s : Nat} (hs : s < n) :
    rd ((shownOf mask first n v).getD s zeroE) = v s + rd (mask (first + s)) := by
  unfold shownOf
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hs),
    List.getElem_map, List.getElem_range, rd_ofK]

variable [Sizes] [Policy] [Request] [Token]

/-- The start form of the squares' level, at any world, sums and batching element. -/
theorem start_value_at (Wd : World K) (W : Array Hid) (gam : E) :
    val Wd (Norm.squaresStart W gam #[]) =
      rd half ^ lPd * (Finset.range 9).sum fun s => rd gam ^ s * val Wd (W.getD s {}).var := by
  unfold Norm.squaresStart
  rw [Came.val_smulE, rd_pow, Came.val_sumTo]
  show _ * (Finset.range 1).sum _ = _
  rw [Finset.sum_range_one, Came.val_sumTo]
  have e : ∀ s, val Wd ((eq (#[] : Point) 0 * gam ^ s) • (W.getD (9 * 0 + s) {}).var) =
      rd gam ^ s * val Wd (W.getD s {}).var := by
    intro s
    have h1 : rd (eq (#[] : Point) 0) = 1 := by
      rw [rd_eq]
      simp [wt]
    rw [Came.val_smulE, rd_mul, rd_pow, h1, one_mul, Nat.mul_zero, Nat.zero_add]
  rw [Finset.sum_congr rfl fun s _ => e s]

/-- **THE NORM's FIRST TWO ROUNDS, SENT HONESTLY.** -/
theorem norm_front (c : NCells) (mask : Nat → E) {F : Fork} (hW : WellLaid F) (pV : Point)
    (hz : pV.size = lt) (gam : E) {m : Nat} (hF : Fresh F (9 + m)) :
    ∃ Fa, sendThenBatch 9 9 F [rvOf (shownOf mask F.next 9
          ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0)) [gam]] =
        some ((hidOf F.next (shownOf mask F.next 9
          ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0)), gam), Fa, []) ∧
      WellLaid Fa ∧ Fresh Fa m ∧ Fa.next = F.next + 9 ∧ Fa.ns = F.ns ∧
      (∀ s, s < 9 → rd (hidden Fa mask (F.next + s)) =
        (dataOf c).sumWAt (Blocks.nat (tupK pV)) 0 s) ∧
      (∃ Tt, Fa.publicPart (Norm.squaresStart (hidOf F.next (shownOf mask F.next 9
          ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0))) gam #[]) = some Tt) ∧
      cvAt mask Fa (hidOf F.next (shownOf mask F.next 9
          ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0))) gam = sigS c pV gam := by
  have hl := shownOf_length mask F.next 9 ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0)
  generalize hv : shownOf mask F.next 9 ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0) = v9 at hl ⊢
  obtain ⟨Fa, h1, a1, a2, a3, a4⟩ := sendThenBatch_returns v9 gam 9 (F := F) (m := m)
    (by rw [hl]; exact hF) []
  rw [hl] at h1 a1 a4
  have Wa : WellLaid Fa := Came.wl_sendThenBatch _ _ _ _ _ _ _ hW h1
  obtain ⟨b1, _, _⟩ := batch_spec hW h1
  have hhid : hide v9 F [] = some (hidOf F.next v9, Fa, []) := by
    obtain ⟨G, g0, _⟩ := hide_returns v9 (F := F) (m := m) (by rw [hl]; exact hF) []
    have e := h1
    unfold sendThenBatch at e
    rw [bind_eq (show Hear.round 9 1 F [rvOf v9 [gam]] = some ((v9, [gam]), F, []) from by
      have := round_returns v9 [gam] F []
      rwa [hl] at this)] at e
    dsimp only at e
    rw [bind_eq g0] at e
    have e' : (some ((hidOf F.next v9, gam), G, []) : Option ((Array Hid × E) × Fork × List Fmt.RoundView))
        = some ((hidOf F.next v9, gam), Fa, []) := e
    simp only [Option.some.injEq, Prod.mk.injEq, and_true, true_and] at e'
    rw [← e']
    exact g0
  have tW : ∀ s, s < 9 → rd (hidden Fa mask (F.next + s)) =
      (dataOf c).sumWAt (Blocks.nat (tupK pV)) 0 s := by
    intro s hs
    rw [hide_hidden hW hhid mask (by rw [hl]; exact hs), ← hv, shownOf_getD _ _ _ _ hs]
    ring
  refine ⟨Fa, h1, Wa, a3, a1, a2, tW, ?_, ?_⟩
  · apply publicPart_returns
    unfold Norm.squaresStart
    refine slotsFilled_smul _ (slotsFilled_sumTo _ _ fun i hi => slotsFilled_sumTo _ _ fun s hs =>
      slotsFilled_smul _ ?_)
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst hi0
    rw [Nat.mul_zero, Nat.zero_add, b1 s hs]
    refine slotsFilled_slot ?_ ?_
    · rw [a2]
      have := hF.1
      omega
    · rw [a4, if_pos ⟨by omega, by omega⟩]
  · unfold cvAt
    rw [start_value_at, sigS_eq c pV gam hz]
    refine congrArg (rd half ^ lPd * ·) ?_
    have e1 := D6.Bridge.ext_squares (dataOf c) (Blocks.nat (tupK pV)) (rd gam) 0
    have e2 : Blocks.ext lt (fun t => (Finset.range d).sum fun j =>
        ((Finset.range 5).sum fun l => rd gam ^ l * ((limbZ c t l j : Int) : K)) ^ 2) (ptK pV) =
        Blocks.ext lt (fun t => (Finset.range d).sum fun j =>
        ((Finset.range 5).sum fun l => rd gam ^ l * ((limbZ c t l j : Int) : K)) ^ 2)
          (Blocks.nat (tupK pV)) :=
      ext_congr_pt lt _ fun t ht => (nat_tupK pV ht).symm
    rw [e2]
    refine Eq.trans ?_ e1.symm
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs9 : s < 9 := Finset.mem_range.mp hs
    have e3 : val (worldOf Fa mask) (Aff.slot (F.next + s)) = rd (hidden Fa mask (F.next + s)) :=
      OnBytes.Model.Aff.value_slot _ _ _
    rw [b1 s hs9, e3, tW s hs9]

/-- A run that is the honest run of tq: each move's polynomial is tq of the challenges in front. -/
theorem poly_of_honest (tq : List K → K[X]) (rs : List K) (ms : List (K[X] × K))
    (h : ms = honest tq [] rs) (i : Nat) (m : K[X] × K) (hm : ms[i]? = some m) :
    m.1 = tq ((ms.take i).map (·.2)) := by
  subst h
  have := honest_poly tq rs [] i m hm
  rwa [List.nil_append] at this

/-- **THE SQUARES' LEVEL, SENT HONESTLY**, for all its draws and any two end values. -/
theorem norm_level (c : NCells) (mask : Nat → E) {Fa : Fork} (pV : Point) (W : Array Hid)
    (gam Tt : E) (hT : Fa.publicPart (Norm.squaresStart W gam #[]) = some Tt) {m : Nat}
    (hF : Fresh Fa (ownSlots (callOf 0 (zS pV) 2).all + 2 + m)) (eps down : E)
    (rsE values : List E) (hr : rsE.length = (zS pV).size + 1) (hv : values.length = 2)
    (oke : okE eps = true) (okd : okE down = true) (okr : ∀ x ∈ rsE, okE x = true)
    (okv : ∀ x ∈ values, okE x = true) :
    ∃ (tS : List Fmt.RoundView) (l : List (List E × E)) (muT : K) (S : Sum) (Fb : Fork),
      tS.length = nS pV ∧ Canonical tS ∧
      level (zS pV) (Norm.squaresStart W gam #[]) Fa tS = some (S, Fb, []) ∧
      S.psc = some (heardRec (Norm.squaresStart W gam #[]) Tt ⟨ofK muT, eps, l, values⟩
        (callOf 0 (zS pV) 2) (Fa.next + 0)) ∧ l.map (·.2) = rsE ∧
      Fb.next = Fa.next + 0 + ownSlots (callOf 0 (zS pV) 2).all + 2 ∧ Fb.ns = Fa.ns ∧
      Fresh Fb m ∧ SquaresTrue c mask Fa pV gam Tt tS ∧
      ∀ (Wd : World K) (S0 : E) (kept : Form),
        (Norm.squaresStart W gam #[]).value Reading.gl Wd = sigS c pV gam →
        (∀ i, i < ownSlots (callOf 0 (zS pV) 2).all →
          Wd.slot (Fa.next + 0 + i) = hcoefL mask Fa i) →
        SmS c mask Fa pV gam (rsE.map Reading.gl.val) =
          Reading.gl.val S0 + kept.value Reading.gl Wd →
        (rowForm (heardRec (Norm.squaresStart W gam #[]) Tt ⟨ofK muT, eps, l, values⟩
          (callOf 0 (zS pV) 2) (Fa.next + 0)) S0 kept).value Reading.gl Wd = 0 := by
  obtain ⟨t, l, _, a1, a2, a3, a5, a6, a7, a8⟩ := level_honest (zS pV)
    (Norm.squaresStart W gam #[])
    (F := Fa) (m := m) (by simpa using hF) Tt hT (hcoefL mask Fa) (SmS c mask Fa pV gam)
    (sigS c pV gam)
    (Classical.choose (SHL (zS pV) (SmS c mask Fa pV gam) (sigS c pV gam) (hSS c mask Fa pV gam)
      mask Fa Tt (sigS c pV gam)))
    (tqL (zS pV) (SmS c mask Fa pV gam) (sigS c pV gam) (hSS c mask Fa pV gam) mask Fa Tt
      (sigS c pV gam)
      (Classical.choose (SHL (zS pV) (SmS c mask Fa pV gam) (sigS c pV gam) (hSS c mask Fa pV gam)
        mask Fa Tt (sigS c pV gam))))
    (fun e rs hl => (specL (zS pV) (SmS c mask Fa pV gam) (sigS c pV gam) (hSS c mask Fa pV gam)
      mask Fa Tt (sigS c pV gam)).2.2.2.2.2.2 rfl _ e rs hl)
    eps down rsE values hr hv oke okd okr okv
  obtain ⟨S, Fb, b1, b2, b3, b4, b5⟩ := a7 []
  rw [List.append_nil] at b1
  refine ⟨t ++ [rvOf [] [down]], l, _, S, Fb, ?_, a2, b1, b2, a5, b3, b4, b5, ?_, a8⟩
  · rw [List.length_append, a1]
    rfl
  · intro R hR i m' hm
    have htake : (t ++ [rvOf [] [down]]).take ((zS pV).size + 3) = t := by
      rw [← a1, List.take_left]
    rw [htake] at hR
    have hRR : R = ⟨ofK _, eps, l, values⟩ := Option.some.inj (hR.symm.trans a3)
    subst hRR
    have hp := poly_of_honest _ _ _ a6 i m' hm
    show m'.1 = tqL (zS pV) _ _ _ mask Fa Tt _ (rd (ofK _)) (rd eps) _
    rw [rd_ofK]
    exact hp

/-- **THE PRODUCTS' SUMCHECK, SENT HONESTLY**, for all its draws and any four end values. The
claimed sum is shown with its mask entry. -/
theorem norm_products (c : NCells) (mask : Nat → E) {Fc : Fork} (Wc : WellLaid Fc) (pV : Point)
    (om : E) {m : Nat} (hF : Fresh Fc (1 + (ownSlots (callOf 1 pV 4).all + 4 + m))) (eps : E)
    (rsE values : List E) (hr : rsE.length = pV.size + 1) (hv : values.length = 4)
    (oke : okE eps = true) (okr : ∀ x ∈ rsE, okE x = true) (okv : ∀ x ∈ values, okE x = true) :
    ∃ (tP : List Fmt.RoundView) (l : List (List E × E)) (muT : K) (S : Sum) (G : Fork),
      tP.length = pV.size + 3 ∧ Canonical tP ∧ sumcheck pV 4 Fc tP = some (S, G, []) ∧
      S.psc = some (heardRec
        ((hidOf Fc.next [ofK (sigR c pV om + rd (mask Fc.next))]).getD 0 {}).var
        (tgt (ofK (sigR c pV om + rd (mask Fc.next)))) ⟨ofK muT, eps, l, values⟩ (callOf 1 pV 4)
        (Fc.next + 1)) ∧ l.map (·.2) = rsE ∧
      G.next = Fc.next + 1 + ownSlots (callOf 1 pV 4).all + 4 ∧ G.ns = Fc.ns ∧ Fresh G m ∧
      ProductsTrue c mask Fc pV om tP ∧
      ∀ (Wd : World K) (S0 : E) (kept : Form),
        (((hidOf Fc.next [ofK (sigR c pV om + rd (mask Fc.next))]).getD 0 {}).var).value
          Reading.gl Wd = sigR c pV om →
        (∀ i, i < ownSlots (callOf 1 pV 4).all → Wd.slot (Fc.next + 1 + i) = hcoefG mask Fc i) →
        SmR c mask Fc pV om (rsE.map Reading.gl.val) =
          Reading.gl.val S0 + kept.value Reading.gl Wd →
        (rowForm (heardRec
          ((hidOf Fc.next [ofK (sigR c pV om + rd (mask Fc.next))]).getD 0 {}).var
          (tgt (ofK (sigR c pV om + rd (mask Fc.next)))) ⟨ofK muT, eps, l, values⟩
          (callOf 1 pV 4) (Fc.next + 1)) S0 kept).value Reading.gl Wd = 0 := by
  generalize hc0 : ofK (sigR c pV om + rd (mask Fc.next)) = c0
  have hcv : cvG mask Fc c0 = sigR c pV om := by
    unfold cvG
    rw [← hc0, rd_ofK]
    ring
  obtain ⟨t, l, _, a1, a2, a3, a4, a5, a6, a7, a8⟩ := sumcheck_honest pV (n := 4) (by omega)
    (F := Fc) (m := m) Wc c0 hF (hcoefG mask Fc) (SmR c mask Fc pV om) (sigR c pV om)
    (muG pV 4 (by omega) (SmR c mask Fc pV om) (sigR c pV om) (hSR c mask Fc pV om) mask Fc
      (rd (tgt c0)) (sigR c pV om))
    (tqG pV 4 (by omega) (SmR c mask Fc pV om) (sigR c pV om) (hSR c mask Fc pV om) mask Fc
      (rd (tgt c0)) (sigR c pV om)
      (muG pV 4 (by omega) (SmR c mask Fc pV om) (sigR c pV om) (hSR c mask Fc pV om) mask Fc
        (rd (tgt c0)) (sigR c pV om)))
    (fun e rs hl => (specG pV 4 (by omega) (SmR c mask Fc pV om) (sigR c pV om)
      (hSR c mask Fc pV om) mask Fc (rd (tgt c0)) (sigR c pV om)).2.2.2.2.2.2 rfl _ e rs hl)
    eps rsE values hr hv (by rw [← hc0]; exact okE_ofK _) oke okr okv
  obtain ⟨S, G, b1, b2, b3, b4, b5⟩ := a7 []
  rw [List.append_nil] at b1
  refine ⟨t, l, _, S, G, a1, a2, b1, b2, a5, b3, b4, b5, ?_, a8⟩
  intro R c0' hR hl
  have hRR : R = ⟨ofK _, eps, l, values⟩ := Option.some.inj (hR.symm.trans a3)
  have hcc : c0' = c0 := by
    have := Option.some.inj (hl.symm.trans a4)
    simpa using this
  subst hRR hcc
  refine ⟨hcv, fun i m' hm => ?_⟩
  have hp := poly_of_honest _ _ _ a6 i m' hm
  show m'.1 = tqG pV 4 _ _ _ _ mask Fc (rd (tgt c0')) _ (rd (ofK _)) (rd eps) _
  rw [rd_ofK]
  exact hp

/-- **A BATCHING ROUND, SENT HONESTLY**: n hidden scalars v 0, v 1, .., each shown with its mask
entry; one element drawn. -/
theorem batch_honest (mask : Nat → E) {F : Fork} (hW : WellLaid F) (n rows : Nat) (v : Nat → K)
    (g : E) {m : Nat} (hF : Fresh F (n + m)) :
    ∃ Fa, sendThenBatch n rows F [rvOf (shownOf mask F.next n v) [g]] =
        some ((hidOf F.next (shownOf mask F.next n v), g), Fa, []) ∧
      WellLaid Fa ∧ Fresh Fa m ∧ Fa.next = F.next + n ∧ Fa.ns = F.ns ∧
      ∀ s, s < n → rd (hidden Fa mask (F.next + s)) = v s := by
  have hl := shownOf_length mask F.next n v
  generalize hv : shownOf mask F.next n v = vs at hl ⊢
  obtain ⟨Fa, h1, a1, a2, a3, _⟩ := sendThenBatch_returns vs g rows (F := F) (m := m)
    (by rw [hl]; exact hF) []
  rw [hl] at h1 a1
  have Wa : WellLaid Fa := Came.wl_sendThenBatch _ _ _ _ _ _ _ hW h1
  have hhid : hide vs F [] = some (hidOf F.next vs, Fa, []) := by
    obtain ⟨G, g0, _⟩ := hide_returns vs (F := F) (m := m) (by rw [hl]; exact hF) []
    have e := h1
    unfold sendThenBatch at e
    rw [bind_eq (show Hear.round n 1 F [rvOf vs [g]] = some ((vs, [g]), F, []) from by
      have := round_returns vs [g] F []
      rwa [hl] at this)] at e
    dsimp only at e
    rw [bind_eq g0] at e
    have e' : (some ((hidOf F.next vs, g), G, []) : Option ((Array Hid × E) × Fork × List Fmt.RoundView))
        = some ((hidOf F.next vs, g), Fa, []) := e
    simp only [Option.some.injEq, Prod.mk.injEq, and_true, true_and] at e'
    rw [← e']
    exact g0
  refine ⟨Fa, h1, Wa, a3, a1, a2, fun s hs => ?_⟩
  rw [hide_hidden hW hhid mask (by rw [hl]; exact hs), ← hv, shownOf_getD _ _ _ _ hs]
  ring

theorem canonical_rvOf {s dr : List E} (hs : ∀ x ∈ s, okE x = true) (hd : ∀ x ∈ dr, okE x = true) :
    Canonical [rvOf s dr] := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := List.mem_map.mp hx
    have e' : y.triple = x := by injection e
    rw [← e', E.ofTriple_triple]
    exact hs y hy
  · obtain ⟨y, hy, e⟩ := List.mem_map.mp hx
    rw [← e, E.ofTriple_triple]
    exact hd y hy

theorem canonical_append {a b : List Fmt.RoundView} (ha : Canonical a) (hb : Canonical b) :
    Canonical (a ++ b) := fun r hr =>
  (List.mem_append.mp hr).elim (ha r) (hb r)

/-- **THE NORM's ROUNDS, SENT HONESTLY, FOR ALL DRAWS.** -/
theorem norm_sends (c : NCells) (mask : Nat → E) {F : Fork} (hW : WellLaid F)
    (hH : (dataOf c).Holds) (pts : List E) (hpts : pts.length = lt)
    (gam epsS down om epsP : E) (rsS valS rsP valP : List E)
    (hrS : rsS.length = (zS pts.toArray).size + 1) (hvS : valS.length = 2)
    (hrP : rsP.length = pts.toArray.size + 1) (hvP : valP.length = 4)
    (okp : ∀ x ∈ pts, okE x = true) (okg : okE gam = true) (okeS : okE epsS = true)
    (okd : okE down = true) (oko : okE om = true) (okeP : okE epsP = true)
    (okrS : ∀ x ∈ rsS, okE x = true) (okvS : ∀ x ∈ valS, okE x = true)
    (okrP : ∀ x ∈ rsP, okE x = true) (okvP : ∀ x ∈ valP, okE x = true) {m : Nat}
    (hF : Fresh F (9 + (ownSlots (callOf 0 (zS pts.toArray) 2).all + 2 +
      (7 + (1 + (ownSlots (callOf 1 pts.toArray 4).all + 4 + m)))))) :
    ∃ (rs : List Fmt.RoundView) (H : Norm.Heard) (G : Fork),
      Canonical rs ∧ Norm.hear F rs = some (H, G, []) ∧ NormTruth c mask F rs ∧
      Sound.NoBad (normRuleC c mask F) rs ∧ Fresh G m ∧ H.pV = pts.toArray ∧ H.gam = gam ∧
      H.om = om := by
  have hz : pts.toArray.size = lt := by rw [List.size_toArray, hpts]
  generalize hpV : pts.toArray = pV at *
  have h0 : drawPoint lt F [rvOf [] pts] = some (pV, F, []) := by
    have := drawPoint_returns pts F []
    rwa [hpts, hpV] at this
  obtain ⟨Fa, h1, Wa, fa, _, _, tW, ⟨Tt, hT⟩, hcv⟩ := norm_front c mask hW pV hz gam hF
  generalize hW9 : hidOf F.next (shownOf mask F.next 9
    ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0)) = W9 at h1 hT hcv
  generalize hr1 : rvOf (shownOf mask F.next 9
    ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0)) [gam] = r1 at h1
  obtain ⟨tS, lS, muS, S, Fb, s1, s2, s3, _, _, _, _, fb, sT, _⟩ := norm_level c mask pV W9 gam Tt
    hT fa epsS down rsS valS hrS hvS okeS okd okrS okvS
  have Wb : WellLaid Fb := Came.wl_level _ _ _ _ _ _ _ Wa s3
  obtain ⟨Fc, h4, Wc, fc, _, _, tP⟩ := batch_honest mask Wb 7 7
    ((dataOf c).prodRAt (Blocks.nat (tupK pV)) 0) om fb
  generalize hP7 : hidOf Fb.next (shownOf mask Fb.next 7
    ((dataOf c).prodRAt (Blocks.nat (tupK pV)) 0)) = P7 at h4
  generalize hr2 : rvOf (shownOf mask Fb.next 7
    ((dataOf c).prodRAt (Blocks.nat (tupK pV)) 0)) [om] = r2 at h4
  obtain ⟨tQ, lP, muP, Sp, G, p1, p2, p3, _, _, _, _, fg, pT, _⟩ := norm_products c mask Wc pV om fc
    epsP rsP valP hrP hvP okeP okrP okvP
  have hhear : Norm.hear F ([rvOf [] pts] ++ ([r1] ++ (tS ++ ([r2] ++ (tQ ++ []))))) =
      some ({ pV := pV, W := W9, gam := gam, rhoI := #[], squares := S, P := P7, om := om,
              products := Sp }, G, []) := by
    unfold Norm.hear Norm.hearPoint
    refine (bind_eq (all_rests (Came.consumes_drawPoint lt) h0 _)).trans ?_
    unfold Norm.hearRest
    refine (bind_eq (all_rests (Came.consumes_sendThenBatch 9 9) h1 _)).trans ?_
    dsimp only
    refine (bind_eq (show (if Norm.lNI == 0 then (pure #[] : Hear Point)
      else drawJoin Norm.lNI) Fa _ = some (#[], Fa, _) from rfl)).trans ?_
    refine (bind_eq (all_rests (Came.consumes_level _ _) s3 _)).trans ?_
    refine (bind_eq (all_rests (Came.consumes_sendThenBatch 7 7) h4 _)).trans ?_
    dsimp only
    refine (bind_eq (all_rests (Came.consumes_sumcheck pV 4) p3 _)).trans ?_
    rfl
  have htruth : NormTruth c mask F ([rvOf [] pts] ++ ([r1] ++ (tS ++ ([r2] ++ (tQ ++ []))))) := by
    refine ⟨hH, ?_⟩
    intro r0' r1' r2' tS' tP' left' pV' W' P' gam' om' Tt' Fa' Fb' Fc' G' S' Sp' hrs e0 e1 e3 e4 e5
      eT
    simp only [List.singleton_append, List.cons.injEq] at hrs
    obtain ⟨rfl, rfl, hrs⟩ := hrs
    have x0 := Option.some.inj (h0.symm.trans e0)
    simp only [Prod.mk.injEq, and_true] at x0
    subst x0
    have x1 := Option.some.inj (h1.symm.trans e1)
    simp only [Prod.mk.injEq, and_true] at x1
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := x1
    have lS' : tS'.length = tS.length := by rw [level_length e3, s1]; rfl
    obtain ⟨hS1, hS2⟩ := List.append_inj hrs lS'.symm
    subst hS1
    injection hS2 with hr2' hS3
    subst hr2'
    have x3 := Option.some.inj (s3.symm.trans e3)
    simp only [Prod.mk.injEq, and_true] at x3
    obtain ⟨rfl, rfl⟩ := x3
    have x4 := Option.some.inj (h4.symm.trans e4)
    simp only [Prod.mk.injEq, and_true] at x4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := x4
    have lP' : tP'.length = tQ.length := by
      obtain ⟨_, _, _, _, _, _, a1, _⟩ := sumcheck_spec e5
      rw [a1, p1]
    obtain ⟨hS4, _⟩ := List.append_inj hS3 lP'.symm
    subst hS4
    have xT := Option.some.inj (hT.symm.trans eT)
    subst xT
    exact ⟨tW, tP, hcv, sT, pT⟩
  refine ⟨_, _, G, ?_, hhear, htruth, norm_true c mask F hW hhear htruth, fg, rfl, rfl, rfl⟩
  refine canonical_append (canonical_rvOf (by simp) okp) (canonical_append ?_
    (canonical_append s2 (canonical_append ?_ (canonical_append p2 (by intro r hr; simp at hr)))))
  · rw [← hr1]
    exact canonical_rvOf (shownOf_ok _ _ _ _) (by
      intro x hx
      rw [List.mem_singleton.mp hx]
      exact okg)
  · rw [← hr2]
    exact canonical_rvOf (shownOf_ok _ _ _ _) (by
      intro x hx
      rw [List.mem_singleton.mp hx]
      exact oko)

/-- A fresh ledger of n numbers (Part/MaskedSumMember.lean) is WellLaid and Fresh. -/
theorem fresh_ledger (n : Nat) :
    WellLaid (Part.MaskedSum.freshLedger n) ∧ Fresh (Part.MaskedSum.freshLedger n) n := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, Part.MaskedSum.freshLedger_free n⟩
  · show (Array.replicate n false).size = n
    simp
  · show (Array.replicate n zeroE).size = n
    simp
  · show (Array.replicate n zeroE).size = n
    simp
  · show 0 + n ≤ n
    omega

end VerifiableInference.Desc.Kinds.Head.Law
