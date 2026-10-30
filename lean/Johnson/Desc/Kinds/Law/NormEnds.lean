-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormEnds.lean.
What it does not show. A toy: an honest prover's tape built in Lean,
at the kind's own hearing text, for cells that hold: no file in scope, no stored proof, not what the
prover's program sends. NOT K06_law's MEMBER: the norm's hearing alone: "normed" and the head's own
sumcheck are not here; nor the reads, nor that the norm's 26 forms are worth 0 (
Law/OpenedNorm.lean makes that step from the letters that are paid here). Premises: the cells hold;
the ledger in front is WellLaid and Fresh. No soundness, no probability, nothing on hiding.
WHAT IT IS. Law/NormSends.lean's sender WITH THE HONEST END VALUES, and what the hearing then
leaves, IN THE LETTERS OF THE NORM's LAWS' OWN TABLES.
  endsOf         an end value is shown with beta times its mask entry.
  start_at_truth the squares' start form is worth sigS where the nine hidden sums are the true ones.
  squares_hend, products_hend   the summand at the challenges is the text's own end term on the end
                 values AS SHOWN (the product of two; the part's summand of four).
  norm_levelE, norm_productsE   the two sumchecks with these end values.
  norm_sendsE    FOR EVERY point, batching elements, eps, challenges and LINE's element: rounds rs,
                 canonical, with Norm.hear F rs = some (H, G, []), NormTruth, no bad draw, the draws
                 the given; AND IN EVERY WORLD WHOSE SLOTS ARE THE HIDDEN SCALARS OF A LATER LEDGER:
                 the nine sums and the seven products are the bridge's true extensions at pV; both
                 end values of the squares' level are the table sqTab's extension at its challenges;
                 the products' claimed sum is the batch of the true extensions; its four end values
                 are the extensions of the row's four fields at its challenges; BOTH SUMCHECKS' OWN
                 FORMS, ON THE END VALUES AS SHOWN, ARE WORTH 0.
Here the start form is a form on slots, the ledger stands behind what was laid in front, the target
is not the hidden value, and the world is read off a ledger behind the rounds.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormSends
import Johnson.Desc.Kinds.Law.HeardEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE okE)
open OnBytes.Model (Aff Fork Reading World)
open Polynomial
open Norm (lt ls d lPd T S2)
open Came (val bind_eq Consumes)
open OnBytes.PscRun (Later)
open Part.MaskedSum (rvOf readAll leadScalars movesOf ownSlots rowForm challenges)
open OnBytes.Desc.First.P1 (honest honest_poly mle sumTerms)
open Came (vsG kG cvG tqG muG specG hcoefG tqL specL hcoefL SHL sEndL sEndG vsG_length mle_point)

/-- What an honest prover shows for n end values v 0, v 1, ..: each with beta times its mask
entry. -/
noncomputable def endsOf (mask : Nat → E) (first n : Nat) (v : Nat → K) (β : K) : List E :=
  (List.range n).map fun j => ofK (v j + β * rd (mask (first + j)))

theorem endsOf_length (mask : Nat → E) (first n : Nat) (v : Nat → K) (β : K) :
    (endsOf mask first n v β).length = n := by
  unfold endsOf
  rw [List.length_map, List.length_range]

theorem endsOf_ok (mask : Nat → E) (first n : Nat) (v : Nat → K) (β : K) :
    ∀ x ∈ endsOf mask first n v β, okE x = true := by
  intro x hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
  exact okE_ofK _

theorem endsOf_getD (mask : Nat → E) (first n : Nat) (v : Nat → K) (β : K) {j : Nat}
    (hj : j < n) :
    rd ((endsOf mask first n v β).getD j zeroE) = v j + β * rd (mask (first + j)) := by
  unfold endsOf
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj),
    List.getElem_map, List.getElem_range, rd_ofK]

theorem in_first (A B C : List E) : ∀ x ∈ A, x ∈ A ++ B ++ C := fun x hx =>
  List.mem_append_left _ (List.mem_append_left _ hx)

theorem in_second (A B C : List E) : ∀ x ∈ B, x ∈ A ++ B ++ C := fun x hx =>
  List.mem_append_left _ (List.mem_append_right _ hx)

theorem in_third (A B C : List E) : ∀ x ∈ C, x ∈ A ++ B ++ C := fun x hx =>
  List.mem_append_right _ hx

theorem map_split (rsE : List E) (n : Nat) (hr : rsE.length = n + 1) :
    rsE.map rd = (rsE.take n).map rd ++ [rd (rsE.getLastD zeroE)] := by
  conv_lhs => rw [take_append_last rsE n zeroE hr]
  rw [List.map_append]
  rfl

variable [Sizes] [Policy] [Request] [Token]

/-- The squares' start form is worth the true sum where the nine hidden sums are the true ones. -/
theorem start_at_truth (c : NCells) (pV : Point) (hz : pV.size = lt) (gam : E) (W9 : Array Hid)
    (Wd : World K)
    (h : ∀ s, s < 9 → val Wd (W9.getD s {}).var = (dataOf c).sumWAt (Blocks.nat (tupK pV)) 0 s) :
    val Wd (Norm.squaresStart W9 gam #[]) = sigS c pV gam := by
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
  exact Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.mp hs)]

/-- The squares' summand at the challenges is the product of the two end values as an honest prover
shows them. -/
theorem squares_hend (c : NCells) (mask : Nat → E) (Fa : Fork) (pV : Point) (hz : pV.size = lt)
    (gam : E) (rsE : List E) (hr : rsE.length = (zS pV).size + 1) (sh0 sh1 : E)
    (h0 : rd sh0 = Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd gam))
        (ptK (rsE.take (zS pV).size).toArray) +
      rd (rsE.getLastD zeroE) * rd (mask (sEndL (zS pV) Fa + 0)))
    (h1 : rd sh1 = Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd gam))
        (ptK (rsE.take (zS pV).size).toArray) +
      rd (rsE.getLastD zeroE) * rd (mask (sEndL (zS pV) Fa + 1))) :
    SmS c mask Fa pV gam (rsE.map rd) = rd (sh0 * sh1) := by
  have hzs := zS_size pV hz
  have hlen : ((rsE.take (zS pV).size).map rd).length = lPd + lt := by
    rw [List.length_map, List.length_take, hr, hzs]
    omega
  have hvl : (vsG (zS pV)).length = lPd + lt := by
    unfold vsG
    rw [List.length_map, Array.length_toList, hzs]
  have hm : mle (lPd + lt) (AtS c gam) ((rsE.take (zS pV).size).map rd) =
      Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd gam))
        (ptK (rsE.take (zS pV).size).toArray) := by
    have h := mle_eq_ext ((rsE.take (zS pV).size).map rd) ((dataOf c).sqTab lPd (rd gam))
    rw [hlen] at h
    exact h
  unfold SmS
  rw [map_split rsE _ hr, Part.MaskedSum.product_at (vsG (zS pV)).length _ _ _ _ _ _
    (by rw [hlen, hvl]), rd_mul, h0, h1, hvl, hm]
  simp only [Nat.add_zero]

/-- **THE SQUARES' LEVEL, SENT HONESTLY, WITH THE HONEST END VALUES**: both end values hide the
table's extension at the challenges. In every world whose slots are the hidden scalars behind the
level and in which the start form is worth the true sum: the level's own form, on the end values as
shown, is worth 0, and both end values' variables are worth that extension. -/
theorem norm_levelE (c : NCells) (mask : Nat → E) {Fa : Fork} (Wa : WellLaid Fa) (pV : Point)
    (hz : pV.size = lt) (W : Array Hid) (gam Tt : E)
    (hT : Fa.publicPart (Norm.squaresStart W gam #[]) = some Tt) {m : Nat}
    (hF : Fresh Fa (ownSlots (callOf 0 (zS pV) 2).all + 2 + m)) (eps down : E)
    (rsE : List E) (hr : rsE.length = (zS pV).size + 1)
    (oke : okE eps = true) (okd : okE down = true) (okr : ∀ x ∈ rsE, okE x = true) :
    ∃ (tS : List Fmt.RoundView) (S : Sum) (Fb : Fork),
      Shaped (down :: eps :: rsE) tS (level.rounds (zS pV).size) ∧ tS.length = nS pV ∧
      Canonical tS ∧
      level (zS pV) (Norm.squaresStart W gam #[]) Fa tS = some (S, Fb, []) ∧
      Fb.next = Fa.next + 0 + ownSlots (callOf 0 (zS pV) 2).all + 2 ∧ Fb.ns = Fa.ns ∧
      Fresh Fb m ∧ SquaresTrue c mask Fa pV gam Tt tS ∧
      S.r = (rsE.take (zS pV).size).toArray ∧
      ∀ Wd : World K, val Wd (Norm.squaresStart W gam #[]) = sigS c pV gam →
        (∀ j, Fa.next ≤ j → j < Fb.next → Wd.slot j = rd (hidden Fb mask j)) →
        val Wd (S.left ((S.end_ 0).shown * (S.end_ 1).shown)) = 0 ∧
        ∀ j, j < 2 → val Wd (S.end_ j).var =
          Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd gam)) (ptK S.r) := by
  generalize hvals : endsOf mask (sEndL (zS pV) Fa) 2
    (fun _ => Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd gam))
      (ptK (rsE.take (zS pV).size).toArray)) (rd (rsE.getLastD zeroE)) = values
  have hv : values.length = 2 := by rw [← hvals, endsOf_length]
  have okv : ∀ x ∈ values, okE x = true := by
    rw [← hvals]
    exact endsOf_ok _ _ _ _ _
  obtain ⟨t, l, a0, a1, a2, a3, a5, a6, a7, a8⟩ := level_honest (zS pV)
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
  have htake : (t ++ [rvOf [] [down]]).take ((zS pV).size + 3) = t := by
    rw [← a1, List.take_left]
  obtain ⟨R, T', c1, _, _, c4, c5, c6⟩ := level_ends Wa b1 mask
  rw [htake] at c1
  have hRR : R = ⟨ofK _, eps, l, values⟩ := Option.some.inj (c1.symm.trans a3)
  subst hRR
  have hSr : S.r = (rsE.take (zS pV).size).toArray := by
    rw [c4]
    show ((l.map (·.2)).take ((zS pV).toList.map (Part.MaskedSum.Var.point · 3)).length).toArray = _
    rw [a5, List.length_map, Array.length_toList]
  have hsE : Fa.next + 0 + ownSlots (callOf 0 (zS pV) 2).all = sEndL (zS pV) Fa := by
    rw [Nat.add_zero]
    rfl
  refine ⟨t ++ [rvOf [] [down]], S, Fb, a0, ?_, a2, b1, b3, b4, b5, ?_, hSr, ?_⟩
  · rw [List.length_append, a1]
    rfl
  · intro R hR i m' hm
    rw [htake] at hR
    have hRR : R = ⟨ofK _, eps, l, values⟩ := Option.some.inj (hR.symm.trans a3)
    subst hRR
    have hp := poly_of_honest _ _ _ a6 i m' hm
    show m'.1 = tqL (zS pV) _ _ _ mask Fa Tt _ (rd (ofK _)) (rd eps) _
    rw [rd_ofK]
    exact hp
  · intro Wd hstart hWs
    have hsh : ∀ j, j < 2 → rd (S.end_ j).shown =
        Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd gam))
          (ptK (rsE.take (zS pV).size).toArray) +
        rd (rsE.getLastD zeroE) * rd (mask (sEndL (zS pV) Fa + j)) := by
      intro j hj
      rw [(c6 j hj).1]
      show rd (values.getD j zeroE) = _
      rw [← hvals, endsOf_getD _ _ _ _ _ hj]
    refine ⟨?_, fun j hj => ?_⟩
    · unfold Sum.left
      rw [b2]
      refine a8 Wd _ {} hstart (fun i hi => ?_) ?_
      · show Wd.slot (Fa.next + 0 + i) = _
        rw [hWs _ (by omega) (by rw [b3]; omega), c5 i hi, Nat.add_zero]
        rfl
      · rw [OnBytes.Model.Aff.value_empty, add_zero]
        exact squares_hend c mask Fa pV hz gam rsE hr _ _ (hsh 0 (by omega)) (hsh 1 (by omega))
    · rw [(c6 j hj).1, hSr]
      show OnBytes.Model.Aff.value Reading.gl Wd (Aff.slot _) = _
      rw [OnBytes.Model.Aff.value_slot, hWs _ (by omega) (by rw [b3]; omega), (c6 j hj).2]
      show rd (values.getD j zeroE) - rd ((l.map (·.2)).getLastD zeroE) * _ = _
      rw [a5, ← hvals, endsOf_getD _ _ _ _ _ hj, hsE]
      ring

/-- The products' summand at the challenges is the part's summand on the four end values as an
honest prover shows them. -/
theorem products_hend (c : NCells) (mask : Nat → E) (Fc : Fork) (pV : Point) (hz : pV.size = lt)
    (om : E) (rsE : List E) (hr : rsE.length = pV.size + 1) (sh : Nat → E) (S0 : E)
    (hS0 : rd S0 = sumTerms (tsP (rd om)) fun q => rd (sh q))
    (hsh : ∀ q, q < 4 → rd (sh q) =
      Blocks.ext lt (fieldK c q) (ptK (rsE.take pV.size).toArray) +
        rd (rsE.getLastD zeroE) * rd (mask (sEndG pV 4 Fc + q))) :
    SmR c mask Fc pV om (rsE.map rd) = rd S0 := by
  letI : FinalNorm.In := (cornerN 0 0).normIn
  have hrs : (rsE.take pV.size).toArray.size = lt := by
    rw [List.size_toArray, List.length_take, hr, hz]
    omega
  have hvl : (vsG pV).length = lt := by rw [vsG_length, hz]
  have hx : ((rsE.take pV.size).map rd).length = (vsG pV).length := by
    rw [List.length_map, List.length_take, hr, hvl, hz]
    omega
  have gq : ∀ q, mle lt (AtR c q) ((rsE.take pV.size).map rd) =
      Blocks.ext lt (fieldK c q) (ptK (rsE.take pV.size).toArray) := by
    intro q
    have hm := mle_point (rsE.take pV.size).toArray hrs fun t => fieldK c q t
    rw [sum_eq_ext _ hrs] at hm
    exact hm
  unfold SmR
  rw [hS0, sumTerms_tsP, sumTerms_tsP, map_split rsE _ hr]
  rw [OnBytes.Desc.First.P1.mle_ext1 _ _ _ _ _ hx, OnBytes.Desc.First.P1.mle_ext1 _ _ _ _ _ hx,
    OnBytes.Desc.First.P1.mle_ext1 _ _ _ _ _ hx, OnBytes.Desc.First.P1.mle_ext1 _ _ _ _ _ hx,
    hsh 0 (by omega), hsh 1 (by omega), hsh 2 (by omega), hsh 3 (by omega), hvl, gq 0, gq 1, gq 2,
    gq 3]

/-- **THE PRODUCTS' SUMCHECK, SENT HONESTLY, WITH THE HONEST END VALUES**: end value q hides the
extension of the row's field q at the challenges. -/
theorem norm_productsE (c : NCells) (mask : Nat → E) {Fc : Fork} (Wc : WellLaid Fc) (pV : Point)
    (hz : pV.size = lt) (om : E) {m : Nat}
    (hF : Fresh Fc (1 + (ownSlots (callOf 1 pV 4).all + 4 + m))) (eps : E)
    (rsE : List E) (hr : rsE.length = pV.size + 1)
    (oke : okE eps = true) (okr : ∀ x ∈ rsE, okE x = true) :
    ∃ (tP : List Fmt.RoundView) (S : Sum) (G : Fork),
      Shaped (eps :: rsE) tP (sumcheck.rounds pV.size 4) ∧
      tP.length = pV.size + 3 ∧ Canonical tP ∧ sumcheck pV 4 Fc tP = some (S, G, []) ∧
      G.next = Fc.next + 1 + ownSlots (callOf 1 pV 4).all + 4 ∧ G.ns = Fc.ns ∧ Fresh G m ∧
      ProductsTrue c mask Fc pV om tP ∧ S.r = (rsE.take pV.size).toArray ∧
      ∀ Wd : World K, (∀ j, Fc.next ≤ j → j < G.next → Wd.slot j = rd (hidden G mask j)) →
        val Wd S.claimed.var = sigR c pV om ∧
        val Wd (S.left (sumTo 1 fun i => OnBytes.Desc.First.P6.summand
          (fun n => om ^ (7 * i + n)) fun j => (S.end_ (4 * i + j)).shown)) = 0 ∧
        ∀ q, q < 4 → val Wd (S.end_ q).var = Blocks.ext lt (fieldK c q) (ptK S.r) := by
  generalize hvals : endsOf mask (sEndG pV 4 Fc) 4
    (fun q => Blocks.ext lt (fieldK c q) (ptK (rsE.take pV.size).toArray))
    (rd (rsE.getLastD zeroE)) = values
  have hv : values.length = 4 := by rw [← hvals, endsOf_length]
  have okv : ∀ x ∈ values, okE x = true := by
    rw [← hvals]
    exact endsOf_ok _ _ _ _ _
  generalize hc0 : ofK (sigR c pV om + rd (mask Fc.next)) = c0
  have hcv : cvG mask Fc c0 = sigR c pV om := by
    unfold cvG
    rw [← hc0, rd_ofK]
    ring
  obtain ⟨t, l, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := sumcheck_honest pV (n := 4) (by omega)
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
  have b3' : G.next = Fc.next + 1 + ownSlots (callOf 1 pV 4).all + 4 := b3
  obtain ⟨c0', R, T', c1, c2, _, c4, _, c6, c7, c8, c9⟩ := sumcheck_ends Wc b1 mask
  have hRR : R = ⟨ofK _, eps, l, values⟩ := Option.some.inj (c2.symm.trans a3)
  have hcc : c0' = c0 := by
    have := Option.some.inj (c1.symm.trans a4)
    simpa using this
  subst hRR hcc
  have hSr : S.r = (rsE.take pV.size).toArray := by
    rw [c6]
    show ((l.map (·.2)).take (pV.toList.map (Part.MaskedSum.Var.point · 3)).length).toArray = _
    rw [a5, List.length_map, Array.length_toList]
  have hsE : Fc.next + 1 + ownSlots (callOf 1 pV 4).all = sEndG pV 4 Fc := rfl
  refine ⟨t, S, G, a0, a1, a2, b1, b3', b4, b5, ?_, hSr, ?_⟩
  · intro R c0'' hR hl
    have hRR : R = ⟨ofK _, eps, l, values⟩ := Option.some.inj (hR.symm.trans a3)
    have hcc : c0'' = c0' := by
      have := Option.some.inj (hl.symm.trans a4)
      simpa using this
    subst hRR hcc
    refine ⟨hcv, fun i m' hm => ?_⟩
    have hp := poly_of_honest _ _ _ a6 i m' hm
    show m'.1 = tqG pV 4 _ _ _ _ mask Fc (rd (tgt c0'')) _ (rd (ofK _)) (rd eps) _
    rw [rd_ofK]
    exact hp
  · intro Wd hWs
    have hcl : (((hidOf Fc.next [c0']).getD 0 {}).var).value Reading.gl Wd = sigR c pV om := by
      rw [hidOf_one]
      show OnBytes.Model.Aff.value Reading.gl Wd (Aff.slot (Fc.next + 0)) = _
      rw [OnBytes.Model.Aff.value_slot, Nat.add_zero, hWs _ (le_refl _) (by rw [b3']; omega), c7]
      exact hcv
    have hsh : ∀ q, q < 4 → rd (S.end_ q).shown =
        Blocks.ext lt (fieldK c q) (ptK (rsE.take pV.size).toArray) +
        rd (rsE.getLastD zeroE) * rd (mask (sEndG pV 4 Fc + q)) := by
      intro q hq
      rw [(c9 q hq).1]
      show rd (values.getD q zeroE) = _
      rw [← hvals, endsOf_getD _ _ _ _ _ hq]
    refine ⟨by rw [c4]; exact hcl, ?_, fun q hq => ?_⟩
    · unfold Sum.left
      rw [b2]
      refine a8 Wd _ {} hcl (fun i hi => ?_) ?_
      · show Wd.slot (Fc.next + 1 + i) = _
        rw [hWs _ (by omega) (by rw [b3']; omega), c8 i hi]
        rfl
      · rw [OnBytes.Model.Aff.value_empty, add_zero]
        refine products_hend c mask Fc pV hz om rsE hr (fun q => (S.end_ q).shown) _ ?_ hsh
        rw [rd_sumTo, Finset.sum_range_one]
        have h := rd_summand (fun n => om ^ (7 * 0 + n))
          (fun j => (S.end_ (4 * 0 + j)).shown) (rd om) (fun n _ => by
            show rd (om ^ (7 * 0 + n)) = _
            rw [Nat.mul_zero, Nat.zero_add, rd_pow])
        simpa using h
    · rw [(c9 q hq).1, hSr]
      show OnBytes.Model.Aff.value Reading.gl Wd (Aff.slot _) = _
      rw [OnBytes.Model.Aff.value_slot, hWs _ (by omega) (by rw [b3']; omega), (c9 q hq).2]
      show rd (values.getD q zeroE) - rd ((l.map (·.2)).getLastD zeroE) * _ = _
      rw [a5, ← hvals, endsOf_getD _ _ _ _ _ hq, hsE]
      ring

/-- **THE NORM's ROUNDS, SENT HONESTLY, WITH THE HONEST END VALUES, FOR ALL DRAWS.** What the
hearing leaves is the truth, in every world whose slots are the hidden scalars of a later ledger. -/
theorem norm_sendsE (c : NCells) (mask : Nat → E) {F : Fork} (hW : WellLaid F)
    (hH : (dataOf c).Holds) (pts : List E) (hpts : pts.length = lt)
    (gam epsS down om epsP : E) (rsS rsP : List E)
    (hrS : rsS.length = (zS pts.toArray).size + 1) (hrP : rsP.length = pts.toArray.size + 1)
    (okp : ∀ x ∈ pts, okE x = true) (okg : okE gam = true) (okeS : okE epsS = true)
    (okd : okE down = true) (oko : okE om = true) (okeP : okE epsP = true)
    (okrS : ∀ x ∈ rsS, okE x = true) (okrP : ∀ x ∈ rsP, okE x = true) {m : Nat}
    (hF : Fresh F (9 + (ownSlots (callOf 0 (zS pts.toArray) 2).all + 2 +
      (7 + (1 + (ownSlots (callOf 1 pts.toArray 4).all + 4 + m)))))) :
    ∃ (rs : List Fmt.RoundView) (H : Norm.Heard) (G : Fork),
      Shaped (pts ++ (gam :: down :: epsS :: rsS) ++ (om :: epsP :: rsP)) rs
        (drawPoint.rounds lt ++ (sendThenBatch.rounds 9 9 ++
          (level.rounds (zS pts.toArray).size ++ (sendThenBatch.rounds 7 7 ++
            (sumcheck.rounds pts.toArray.size 4 ++ []))))) ∧
      Canonical rs ∧ Norm.hear F rs = some (H, G, []) ∧ NormTruth c mask F rs ∧
      Sound.NoBad (normRuleC c mask F) rs ∧ Fresh G m ∧ WellLaid G ∧ H.pV = pts.toArray ∧
      H.gam = gam ∧ H.om = om ∧ H.squares.r = (rsS.take (zS pts.toArray).size).toArray ∧
      H.products.r = (rsP.take pts.toArray.size).toArray ∧
      ∀ (G' : Fork) (Wd : World K), Later G G' →
        (∀ j, F.next ≤ j → j < G.next → Wd.slot j = rd (hidden G' mask j)) →
        (∀ s, s < 9 → val Wd (H.W.getD s {}).var = (dataOf c).sumWAt (ptK H.pV) 0 s) ∧
        (∀ n, n < 7 → val Wd (H.P.getD n {}).var = (dataOf c).prodRAt (ptK H.pV) 0 n) ∧
        val Wd (H.squares.left ((H.squares.end_ 0).shown * (H.squares.end_ 1).shown)) = 0 ∧
        (∀ j, j < 2 → val Wd (H.squares.end_ j).var =
          Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd H.gam)) (ptK H.squares.r)) ∧
        val Wd H.products.claimed.var = (Finset.range 7).sum (fun n =>
          rd H.om ^ n * (dataOf c).prodRAt (ptK H.pV) 0 n) ∧
        val Wd (H.products.left (sumTo 1 fun i => OnBytes.Desc.First.P6.summand
          (fun n => H.om ^ (7 * i + n)) fun j => (H.products.end_ (4 * i + j)).shown)) = 0 ∧
        ∀ q, q < 4 → val Wd (H.products.end_ q).var =
          Blocks.ext lt (fieldK c q) (ptK H.products.r) := by
  have hz : pts.toArray.size = lt := by rw [List.size_toArray, hpts]
  generalize hpV : pts.toArray = pV at *
  have h0 : drawPoint lt F [rvOf [] pts] = some (pV, F, []) := by
    have := drawPoint_returns pts F []
    rwa [hpts, hpV] at this
  obtain ⟨Fa, h1, Wa, fa, na, _, tW, ⟨Tt, hT⟩, hcv⟩ := norm_front c mask hW pV hz gam hF
  generalize hW9 : hidOf F.next (shownOf mask F.next 9
    ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0)) = W9 at h1 hT hcv
  generalize hr1 : rvOf (shownOf mask F.next 9
    ((dataOf c).sumWAt (Blocks.nat (tupK pV)) 0)) [gam] = r1 at h1
  obtain ⟨tS, S, Fb, s0, s1, s2, s3, nb, _, fb, sT, sR, sW⟩ := norm_levelE c mask Wa pV hz W9 gam Tt
    hT fa epsS down rsS hrS okeS okd okrS
  have Wb : WellLaid Fb := Came.wl_level _ _ _ _ _ _ _ Wa s3
  obtain ⟨Fc, h4, Wc, fc, nc, _, tP⟩ := batch_honest mask Wb 7 7
    ((dataOf c).prodRAt (Blocks.nat (tupK pV)) 0) om fb
  generalize hP7 : hidOf Fb.next (shownOf mask Fb.next 7
    ((dataOf c).prodRAt (Blocks.nat (tupK pV)) 0)) = P7 at h4
  generalize hr2 : rvOf (shownOf mask Fb.next 7
    ((dataOf c).prodRAt (Blocks.nat (tupK pV)) 0)) [om] = r2 at h4
  obtain ⟨tQ, Sp, G, p0, p1, p2, p3, ng, _, fg, pT, pR, pW⟩ := norm_productsE c mask Wc pV hz om fc
    epsP rsP hrP okeP okrP
  have Wg : WellLaid G := Came.wl_sumcheck _ _ _ _ _ _ _ Wc p3
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
  refine ⟨_, _, G, ?_, ?_, hhear, htruth, norm_true c mask F hW hhear htruth, fg, Wg, rfl, rfl, rfl,
    sR, pR, ?_⟩
  · refine ((shaped_one [] pts ⟨"ZERO", 0, lt, false, 0⟩ rfl hpts).mono (in_first _ _ _)).append
      (Shaped.append ?_ ((s0.mono fun x hx => in_second _ _ _ x (List.mem_cons_of_mem _ hx)).append
        (Shaped.append ?_ ((p0.mono fun x hx => in_third _ _ _ x (List.mem_cons_of_mem _ hx)).append
          (shaped_nil _)))))
    · rw [← hr1]
      exact (shaped_one _ [gam] ⟨"BAT-sigma", 9, 1, false, 9⟩ (shownOf_length _ _ _ _) rfl).mono
        fun x hx => in_second _ _ _ x (by
          rw [List.mem_singleton.mp hx]
          exact List.mem_cons_self ..)
    · rw [← hr2]
      exact (shaped_one _ [om] ⟨"BAT-sigma", 7, 1, false, 7⟩ (shownOf_length _ _ _ _) rfl).mono
        fun x hx => in_third _ _ _ x (by
          rw [List.mem_singleton.mp hx]
          exact List.mem_cons_self ..)
  · refine canonical_append (canonical_rvOf (by simp) okp) (canonical_append ?_
      (canonical_append s2 (canonical_append ?_
        (canonical_append p2 (by intro r hr; simp at hr)))))
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
  · intro G' Wd hL hWs
    have Lab : Later Fa Fb := keeps_level _ _ _ _ _ _ _ s3
    have Lbc : Later Fb Fc := keeps_sendThenBatch _ _ _ _ _ _ _ h4
    have Lcg : Later Fc G := keeps_sumcheck _ _ _ _ _ _ _ p3
    obtain ⟨v1, f1, _⟩ := batch_spec hW h1
    obtain ⟨v4, f4, _⟩ := batch_spec Wb h4
    have fS := filled_rangeL (zS pV) _ Wa s3
    have fP := Came.filled_rangeG pV 4 Wc p3
    have hsL : sEndL (zS pV) Fa + 2 = Fb.next := by
      rw [nb, Nat.add_zero]
      rfl
    have hsG : sEndG pV 4 Fc + 4 = G.next := by
      rw [ng]
      rfl
    have hu : ∀ (v : Nat → K), Blocks.ext lt v (ptK pV) = Blocks.ext lt v (Blocks.nat (tupK pV)) :=
      fun v => ext_congr_pt lt v fun t ht => (nat_tupK pV ht).symm
    have sums : ∀ s, s < 9 → val Wd (W9.getD s {}).var =
        (dataOf c).sumWAt (Blocks.nat (tupK pV)) 0 s := by
      intro s hs
      rw [v1 s hs]
      show OnBytes.Model.Aff.value Reading.gl Wd (Aff.slot _) = _
      rw [OnBytes.Model.Aff.value_slot, hWs _ (by omega) (by omega),
        hidden_later mask (((Lab.trans Lbc).trans Lcg).trans hL) (f1 s hs), tW s hs]
    have prods : ∀ n, n < 7 → val Wd (P7.getD n {}).var =
        (dataOf c).prodRAt (Blocks.nat (tupK pV)) 0 n := by
      intro n hn
      rw [v4 n hn]
      show OnBytes.Model.Aff.value Reading.gl Wd (Aff.slot _) = _
      rw [OnBytes.Model.Aff.value_slot, hWs _ (by omega) (by omega),
        hidden_later mask (Lcg.trans hL) (f4 n hn), tP n hn]
    obtain ⟨q1, q2⟩ := sW Wd (start_at_truth c pV hz gam W9 Wd sums) fun j j1 j2 => by
      rw [hWs j (by omega) (by omega),
        hidden_later mask ((Lbc.trans Lcg).trans hL) (fS j j1 (by omega))]
    obtain ⟨q3, q4, q5⟩ := pW Wd fun j j1 j2 => by
      rw [hWs j (by omega) j2, hidden_later mask hL (fP j j1 (by omega))]
    refine ⟨fun s hs => (sums s hs).trans (hu _).symm, fun n hn => (prods n hn).trans (hu _).symm,
      q1, q2, ?_, q4, q5⟩
    exact q3.trans (sigR_eq c pV om hz)

end VerifiableInference.Desc.Kinds.Head.Law
