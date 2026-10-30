-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormProducts.lean.
WHAT IT DOES NOT SHOW. That the reads are true, that the forms are 0, that the world is the
ledger's, that no bad element was drawn: premises. The squares' level and the point pV: other files.
Nothing on probabilities beyond the lengths of the lists of bad elements.
WHAT IT IS. THE NORM's ROW (Norm.lean), ITS SUMCHECK "products", OVER THE KIND's OWN TEXT: the
cells, the mask entries, the ledger in front, the point pV and the batching element om stand first;
then a rule for bad elements; then: at a hearing of HeadParts.lean's "sumcheck pV 4" that returns,
in a world that holds the hidden scalars, with the sumcheck's own form 0, its four end values tied
to the row's four fields through a true read at the challenges, and no bad draw: THE CLAIMED SUM's
HIDDEN SCALAR IS THE BATCH, UNDER om's POWERS, OF THE EXTENSIONS AT pV OF THE POSITIONS' SEVEN
PRODUCTS. The sumcheck is not proved here: the law of "sumcheck z n" (Law/SumLaw.lean: coreG) at n =
4, with the summand of a sum of products (isSum_terms).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Normed
import Johnson.Desc.Kinds.Law.NormPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Reading World Fork)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits P6.rowProducts)
open OnBytes.Desc.First.P1 (mle tot ext1 IsSum Term sumTerms isSum_terms tot_ext1_terms mle_ext1)
open Part.MaskedSum (Var Call weightsOf twos_wt)
open Norm (lt ls d lPd T S2)
open Came (val vsG sEndG coreG badG badG_length sum_r_size mle_point vsG_length vsG_d)

/-- **The premise hS of the law, for a sum of products of extensions with shown end values**:
MaskedSumProducts.lean's isSum_product, at a list of terms. -/
theorem isSum_termsCall (lead : Nat) (vs : List Var) (n : Nat) (h3 : ∀ v ∈ vs, 3 ≤ v.d)
    (A : Nat → List Bool → K) (m : Nat → K) (ts : List (Term K)) :
    IsSum ((⟨lead, vs, some ⟨2, n⟩⟩ : Call).all.map (Var.wt Reading.gl))
      (fun rs => sumTerms ts fun i => mle (vs.length + 1) (ext1 vs.length (A i) (m i)) rs)
      (tot (weightsOf Reading.gl vs) fun b => sumTerms ts fun i => A i b) := by
  have hall : (⟨lead, vs, some ⟨2, n⟩⟩ : Call).all = vs ++ [Var.point OnBytes.zeroE 3] := rfl
  have h3' : ∀ v ∈ vs ++ [Var.point OnBytes.zeroE 3], 3 ≤ v.d := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact h3 v h
    · rw [List.mem_singleton] at h
      rw [h]
      exact le_refl 3
  have ht := twos_wt Reading.gl 3 (by omega) (vs ++ [Var.point OnBytes.zeroE 3]) h3'
  have hs := isSum_terms _ _ ht (fun i => ext1 vs.length (A i) (m i)) ts
  have hl : ((vs ++ [Var.point OnBytes.zeroE 3]).map (Var.wt Reading.gl)).length =
      vs.length + 1 := by simp
  rw [hl] at hs
  rw [hall]
  refine hs.congr (fun _ => rfl) ?_
  have hw : weightsOf Reading.gl (vs ++ [Var.point OnBytes.zeroE 3]) =
      weightsOf Reading.gl vs ++ [(1, 0)] := by
    unfold weightsOf
    rw [List.map_append]
    show _ ++ [((1 : K) - Reading.gl.val OnBytes.zeroE, Reading.gl.val OnBytes.zeroE)] = _
    rw [Reading.gl.zero, sub_zero]
  have hlen : (weightsOf Reading.gl vs).length = vs.length := by simp [weightsOf]
  rw [hw, ← hlen]
  exact tot_ext1_terms (weightsOf Reading.gl vs) A m ts

/-- The seven terms: product number n of the part's list under the n-th power of om. -/
def tsP (om : K) : List (Term K) :=
  P6.rowProducts.zipIdx.map fun x => (om ^ x.2, x.1.1, x.1.2)

theorem sumTerms_tsP (om : K) (v : Nat → K) :
    sumTerms (tsP om) v = (Finset.range 7).sum fun n =>
      om ^ n * Inst.Model.Ledger.prodsOf (v 0) (v 1) (v 2) (v 3) n := by
  simp [tsP, sumTerms, P6.rowProducts, Inst.Model.Ledger.prodsOf, Finset.sum_range_succ,
    List.zipIdx]
  ring

/-- The part's summand on four elements, read. -/
theorem rd_summand (om : Nat → E) (s : Nat → E) (o : K) (ho : ∀ n, n < 7 → rd (om n) = o ^ n) :
    rd (OnBytes.Desc.First.P6.summand om s) = sumTerms (tsP o) fun q => rd (s q) := by
  have hadd : ∀ a b : E, rd (OnBytes.addE a b) = rd a + rd b := Reading.gl.add
  have hmul : ∀ a b : E, rd (OnBytes.mulE a b) = rd a * rd b := Reading.gl.mul
  have hzero : rd OnBytes.zeroE = 0 := Reading.gl.zero
  rw [sumTerms_tsP]
  simp only [OnBytes.Desc.First.P6.summand, P6.rowProducts, List.zipIdx, List.zipIdx_cons,
    List.zipIdx_nil, List.foldl_cons, List.foldl_nil, hadd, hmul, hzero, Nat.zero_add,
    Finset.sum_range_succ, Finset.sum_range_zero, Inst.Model.Ledger.prodsOf]
  rw [ho 0 (by omega), ho 1 (by omega), ho 2 (by omega), ho 3 (by omega), ho 4 (by omega),
    ho 5 (by omega), ho 6 (by omega)]
  ring

variable [Sizes] [Policy] [Request] [Token]

/-- The row's four fields at position t, in K: a, b, Rlo, Rhi by their places 0 to 3. -/
def fieldK (c : NCells) (q t : Nat) : K :=
  match q with
  | 0 => Inst.Model.Ledger.sa (dK c t)
  | 1 => Inst.Model.Ledger.sb (dK c t)
  | 2 => Inst.Model.Ledger.Rlo (dK c t)
  | _ => Inst.Model.Ledger.Rhi (dK c t)

section Letters
variable (c : NCells) (mask : Nat → E) (F0 : Fork) (pV : Point) (om : E)

def AtR (q : Nat) : List Bool → K := fun b => fieldK c q (idxOf b)

def SmR : List K → K := fun rs =>
  sumTerms (tsP (rd om)) fun q =>
    mle ((vsG pV).length + 1) (ext1 (vsG pV).length (AtR c q) (rd (mask (sEndG pV 4 F0 + q)))) rs

def sigR : K :=
  tot (weightsOf Reading.gl (vsG pV)) fun b => sumTerms (tsP (rd om)) fun q => AtR c q b

theorem hSR : IsSum ((⟨1, vsG pV, some ⟨2, 4⟩⟩ : Call).all.map (Var.wt Reading.gl))
    (SmR c mask F0 pV om) (sigR c pV om) :=
  isSum_termsCall 1 (vsG pV) 4 (fun v hv => by rw [vsG_d _ v hv]) _ _ _

/-- The tables' sum of products, summed at pV: the batch of the products' extensions. -/
theorem sigR_eq (hz : pV.size = lt) : sigR c pV om = (Finset.range 7).sum fun n =>
    rd om ^ n * Blocks.ext lt (fun t => Inst.Model.Ledger.prods (dK c t) n) (ptK pV) := by
  -- a class that two called lemmas carry and do not read
  letI : FinalNorm.In := (cornerN 0 0).normIn
  have hw : weightsOf Reading.gl (vsG pV) = (pV.toList.map rd).map fun x => (1 - x, x) := by
    unfold weightsOf vsG
    simp only [List.map_map]
    rfl
  unfold sigR
  rw [hw, tot_pairs, List.length_map, Array.length_toList, hz]
  have h := mle_point pV hz fun t => sumTerms (tsP (rd om)) fun q => fieldK c q t
  refine Eq.trans h ?_
  simp only [sumTerms_tsP, ← sum_eq_ext pV hz, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun t _ => ?_
  show _ * (_ * Inst.Model.Ledger.prodsOf (Inst.Model.Ledger.sa (dK c t))
    (Inst.Model.Ledger.sb (dK c t)) (Inst.Model.Ledger.Rlo (dK c t))
    (Inst.Model.Ledger.Rhi (dK c t)) n) = _
  unfold Inst.Model.Ledger.prods
  ring

end Letters

/-- **The rule for the bad elements of "products"**, by name: of the cells, the masks, the ledger in
front, pV and om. -/
noncomputable def productsRule (c : NCells) (mask : Nat → E) (F0 : Fork) (pV : Point) (om : E) :
    List Fmt.RoundView → List E :=
  badG pV 4 (by omega) (SmR c mask F0 pV om) (sigR c pV om) (hSR c mask F0 pV om) mask F0

theorem productsRule_length (c : NCells) (mask : Nat → E) (F0 : Fork) (pV : Point) (om : E)
    (h : List Fmt.RoundView) : (productsRule c mask F0 pV om h).length ≤
      ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 :=
  badG_length _ _ _ _ _ _ _ _ h

/-- **THE LAW OF "products".** D' j: the caller's form for digit j of the row through its read at
the sumcheck's challenges. S0: the caller's end term. -/
theorem products_law (c : NCells) (mask : Nat → E) (F0 : Fork) (pV : Point) (om : E)
    (hWL : WellLaid F0) (hz : pV.size = lt)
    {F1 : Fork} {t : List Fmt.RoundView} {S : Sum} (W : World K) (D' : Nat → Form) (S0 : E)
    (hWs : ∀ j, F0.next ≤ j → j < sEndG pV 4 F0 + 4 → W.slot j = rd (hidden F1 mask j))
    (hcan : Canonical t) (hsum : sumcheck pV 4 F0 t = some (S, F1, []))
    (hD : ∀ j, j < NR → val W (D' j) = Blocks.ext lt (fun t => dK c t j) (ptK S.r))
    (hS0 : rd S0 = sumTerms (tsP (rd om)) (fun q => rd (S.end_ q).shown))
    (f1 : val W (S.left S0) = 0)
    (fa : val W ((S.end_ 0).var - (P6.Row.ofDigits D').a) = 0)
    (fb : val W ((S.end_ 1).var - (P6.Row.ofDigits D').b) = 0)
    (fl : val W ((S.end_ 2).var - (P6.Row.ofDigits D').Rlo) = 0)
    (fh : val W ((S.end_ 3).var - (P6.Row.ofDigits D').Rhi) = 0)
    (hnb : NoBad (productsRule c mask F0 pV om) t) :
    val W S.claimed.var = (Finset.range 7).sum fun n =>
      rd om ^ n * Blocks.ext lt (fun t => Inst.Model.Ledger.prods (dK c t) n) (ptK pV) := by
  -- a class that two called lemmas carry and do not read
  letI : FinalNorm.In := (cornerN 0 0).normIn
  have hr : S.r.size = lt := by rw [sum_r_size hsum, hz]
  -- a field of the row through the read is the field's extension at the challenges
  have hdv : ∀ j, j < 99 → OnBytes.Desc.First.P6.dv Reading.gl W D' j =
      Blocks.ext lt (fun t => dK c t j) (ptK S.r) := fun j hj => hD j hj
  have gq : ∀ q, q < 4 → val W (S.end_ q).var = mle lt (AtR c q) (S.r.toList.map rd) := by
    intro q hq
    have hm := mle_point S.r hr fun t => fieldK c q t
    rw [sum_eq_ext S.r hr] at hm
    refine Eq.trans ?_ hm.symm
    have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases hq' with rfl | rfl | rfl | rfl
    · rw [Came.val_sub] at fa
      rw [sub_eq_zero.mp fa]
      show Aff.value Reading.gl W (P6.Row.ofDigits D').a = _
      rw [OnBytes.Desc.First.P6.a_value]
      show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.sa (dK c t)) (ptK S.r)
      rw [Inst.Model.Ledger.ext_sa lt (fun m t => dK c t m) (ptK S.r)]
      unfold Inst.Model.Ledger.sa
      rw [hdv 58 (by omega), hdv 59 (by omega), hdv 60 (by omega), hdv 61 (by omega)]
    · rw [Came.val_sub] at fb
      rw [sub_eq_zero.mp fb]
      show Aff.value Reading.gl W (P6.Row.ofDigits D').b = _
      rw [OnBytes.Desc.First.P6.b_value]
      show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.sb (dK c t)) (ptK S.r)
      rw [Inst.Model.Ledger.ext_sb lt (fun m t => dK c t m) (ptK S.r)]
      unfold Inst.Model.Ledger.sb
      rw [hdv 62 (by omega), hdv 63 (by omega)]
    · rw [Came.val_sub] at fl
      rw [sub_eq_zero.mp fl]
      show Aff.value Reading.gl W (P6.Row.ofDigits D').Rlo = _
      rw [OnBytes.Desc.First.P6.Rlo_value]
      show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.Rlo (dK c t)) (ptK S.r)
      rw [Inst.Model.Ledger.ext_Rlo lt (fun m t => dK c t m) (ptK S.r)]
      unfold Inst.Model.Ledger.Rlo Inst.Model.Ledger.b256
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hdv (80 + l) (by have := Finset.mem_range.mp hl; omega)]
    · rw [Came.val_sub] at fh
      rw [sub_eq_zero.mp fh]
      show Aff.value Reading.gl W (P6.Row.ofDigits D').Rhi = _
      rw [OnBytes.Desc.First.P6.Rhi_value]
      show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.Rhi (dK c t)) (ptK S.r)
      rw [Inst.Model.Ledger.ext_Rhi lt (fun m t => dK c t m) (ptK S.r)]
      unfold Inst.Model.Ledger.Rhi Inst.Model.Ledger.b256
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hdv (83 + l) (by have := Finset.mem_range.mp hl; omega)]
  have hres := coreG pV 4 (by omega) (SmR c mask F0 pV om) (sigR c pV om) (hSR c mask F0 pV om)
    mask F0 hWL W hWs hcan hsum S0 f1 (fun β hβ => by
      unfold SmR
      rw [hS0, sumTerms_tsP, sumTerms_tsP]
      have hx : (S.r.toList.map rd).length = (vsG pV).length := by
        rw [List.length_map, Array.length_toList, hr, vsG_length, hz]
      rw [mle_ext1 _ _ _ _ β hx, mle_ext1 _ _ _ _ β hx, mle_ext1 _ _ _ _ β hx,
        mle_ext1 _ _ _ _ β hx, hβ 0 (by omega), hβ 1 (by omega), hβ 2 (by omega),
        hβ 3 (by omega), vsG_length, hz, ← gq 0 (by omega), ← gq 1 (by omega), ← gq 2 (by omega),
        ← gq 3 (by omega)]
      rfl) hnb
  rw [← sigR_eq c pV om hz]
  exact hres

end VerifiableInference.Desc.Kinds.Head.Law
