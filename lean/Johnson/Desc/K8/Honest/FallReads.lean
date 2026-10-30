-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallReads.lean: WHAT THE TIES AND READS OF THE LIST "K8.equations" LAY ON ONE
ENTRY OF THE VECTOR OF READS. Statements and proofs, for the count of
Johnson/Desc/K8/Honest/FallCount.lean. On the list's own text and plain data alone: no block, no
prover.

  `sumFrom_none`, `sumFrom_pick`, `sumFrom_sub`, `runSum_zero`, `runSum_nil`, `runSum_pick`   sums
      in which at most one term counts
  `entry_off`, `entry_at`   the world `oneAt` at another array; at the place of a vector's entry
  `tieBracket_same`   a tie reads the digits' array and a symbol array alone
  `readBracket_diff`   what a read reads of the vector's array
  **`reads_weight`**   the ties' and reads' sum, taken where the entry of place pos is 1 and all else
      0, and where all is 0, parts by -(chi^(n + first) * the column's sum), for THE read (number q
      of the list) and column c that name pos
  `same1`   what the smallness test's data have in common in front of the list and behind the step
      that lays the powers of chi
  **`k8_cut`**   a yes of "K8.equations", cut: four claims, then the ties and reads; what the adding
      of these does to a ledger's value, in every world
Limits: from a yes of the list alone. Identities at one value of chi.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallAlg
import Johnson.Desc.First.TailClaims.EquationsCover
import Johnson.Desc.First.TailClaims.EquationsAny
import Johnson.Desc.First.TailClaims.EquationsFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port
open OnBytes.Tie.Pv.Tail (PlacesApart)

/-! ## Sums in which at most one term counts -/

section
variable {K : Type} [CommRing K]

theorem sumFrom_none {α : Type} (g : Nat → α → K) : ∀ (l : List α) (s : Nat),
    (∀ j z, l[j]? = some z → g (s + j) z = 0) → sumFrom g s l = 0
  | [], _, _ => rfl
  | x :: l, s, h => by
    simp only [sumFrom]
    rw [show g s x = 0 from h 0 x (by simp), sumFrom_none g l (s + 1) (fun j z hj => by
      have h2 := h (j + 1) z (by simpa using hj)
      rwa [show s + (j + 1) = s + 1 + j by omega] at h2), add_zero]

theorem sumFrom_pick {α : Type} (g : Nat → α → K) : ∀ (l : List α) (s k : Nat) (y : α),
    l[k]? = some y → (∀ j z, l[j]? = some z → j ≠ k → g (s + j) z = 0) →
    sumFrom g s l = g (s + k) y
  | [], _, _, _, hk, _ => by simp at hk
  | x :: l, s, 0, y, hk, h => by
    have e : x = y := by simpa using hk
    subst e
    simp only [sumFrom]
    rw [sumFrom_none g l (s + 1) (fun j z hj => by
      have h2 := h (j + 1) z (by simpa using hj) (by omega)
      rwa [show s + (j + 1) = s + 1 + j by omega] at h2), add_zero]
    rfl
  | x :: l, s, k + 1, y, hk, h => by
    simp only [sumFrom]
    rw [show g s x = 0 from h 0 x (by simp) (by omega), zero_add,
      sumFrom_pick g l (s + 1) k y (by simpa using hk) (fun j z hj hne => by
        have h2 := h (j + 1) z (by simpa using hj) (by omega)
        rwa [show s + (j + 1) = s + 1 + j by omega] at h2),
      show s + 1 + k = s + (k + 1) by omega]

theorem sumFrom_sub {α : Type} (g h : Nat → α → K) : ∀ (l : List α) (s : Nat),
    sumFrom g s l - sumFrom h s l = sumFrom (fun j x => g j x - h j x) s l
  | [], _ => by simp [sumFrom]
  | x :: l, s => by
    simp only [sumFrom]
    rw [← sumFrom_sub g h l (s + 1)]
    ring

theorem runSum_zero : ∀ (n i : Nat), runSum (fun _ => (0 : K)) n i = 0
  | 0, _ => rfl
  | n + 1, i => by
    simp only [runSum]
    rw [runSum_zero n (i + 1), add_zero]

theorem runSum_nil (h : Nat → K) (n : Nat) (hz : ∀ d, d < n → h d = 0) : runSum h n 0 = 0 := by
  rw [runSum_eq_sum]
  exact Finset.sum_eq_zero fun d hd => by
    rw [Nat.zero_add]
    exact hz d (Finset.mem_range.1 hd)

theorem runSum_pick (h : Nat → K) (n c : Nat) (hc : c < n) (hz : ∀ d, d < n → d ≠ c → h d = 0) :
    runSum h n 0 = h c := by
  rw [runSum_eq_sum]
  simp only [Nat.zero_add]
  exact Finset.sum_eq_single c (fun d hd hne => hz d (Finset.mem_range.1 hd) hne)
    (fun hn => absurd (Finset.mem_range.2 hc) hn)

end

/-! ## The two worlds at the smallness test's brackets -/

theorem entry_off (tU r i t' : Nat) (h : t' ≠ tU) (r' i' : Nat) :
    (oneAt tU r i).entry t' r' i' = 0 := by
  simp [oneAt, h]

theorem entry_zero (t' r' i' : Nat) : allZero.entry t' r' i' = 0 := rfl

/-- A vector's entry of place p lies in virtual row p / K at column p % K. -/
theorem entry_at (tU K p pos : Nat) :
    (oneAt tU (pos / K) (pos % K)).entry tU (p / K) (p % K) = if p = pos then 1 else 0 := by
  have e : (p / K = pos / K ∧ p % K = pos % K) ↔ p = pos :=
    ⟨fun h => calc
        p = K * (p / K) + p % K := (Nat.div_add_mod p K).symm
        _ = K * (pos / K) + pos % K := by rw [h.1, h.2]
        _ = pos := Nat.div_add_mod pos K,
      fun h => by rw [h]; exact ⟨rfl, rfl⟩⟩
  simp [oneAt, e]

theorem tieBracket_same (tl : HTailF2) (mu tU r i : Nat) (hZ : tl.ix.ZZ ≠ tU)
    (hg : tl.gtTree.getD mu 0 ≠ tU) :
    tieBracket Reading.gl (oneAt tU r i) tl mu = tieBracket Reading.gl allZero tl mu := by
  unfold tieBracket
  simp only [entry_off tU r i _ hZ, entry_off tU r i _ hg, entry_zero]

theorem readBracket_diff (tl : HTailF2) (F0 : Fork) (x : HFun × Nat) (tU r i : Nat)
    (hZ : tl.ix.ZZ ≠ tU) (hU : tl.ix.U.getD x.1.tree none = some tU) :
    readBracket Reading.gl (oneAt tU r i) tl F0 x - readBracket Reading.gl allZero tl F0 x =
      - runSum (fun d => Reading.gl.val ((tl.gamV.getD x.1.mat #[]).getD d zeroE) *
          (oneAt tU r i).entry tU (posOf tl x.1 x.2 d / colsU F0 tU)
            (posOf tl x.1 x.2 d % colsU F0 tU)) (tl.mats.getD x.1.mat {}).k 0 := by
  unfold readBracket
  simp only [hU, Option.getD_some, entry_off tU r i _ hZ, entry_zero, mul_zero, runSum_zero]
  ring

/-- **What the ties and reads lay on the entry of place pos.** -/
theorem reads_weight (tl : HTailF2) (F0 : Fork) (funs : Array HFun) (tU pos q c : Nat)
    (y : HFun × Nat) (hZ : tl.ix.ZZ ≠ tU) (hg : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tU)
    (hU : ∀ x ∈ readsList tl funs, tl.ix.U.getD x.1.tree none = some tU ∧ x.1.tree = 2)
    (hap : (readsList tl funs).Pairwise (PlacesApart tl))
    (hcol : ∀ x ∈ readsList tl funs, ∀ d d', d < d' → d' < (tl.mats.getD x.1.mat {}).k →
      posOf tl x.1 x.2 d ≠ posOf tl x.1 x.2 d')
    (hq : (readsList tl funs)[q]? = some y) (hc : c < (tl.mats.getD y.1.mat {}).k)
    (hpos : posOf tl y.1 y.2 c = pos) :
    (((List.range tl.NM).map
          (tieTerm Reading.gl (oneAt tU (pos / colsU F0 tU) (pos % colsU F0 tU)) tl F0)).sum +
        sumFrom (readTerm Reading.gl (oneAt tU (pos / colsU F0 tU) (pos % colsU F0 tU)) tl F0) 0
          (readsList tl funs)) -
      (((List.range tl.NM).map (tieTerm Reading.gl allZero tl F0)).sum +
        sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs)) =
      -(Reading.gl.val F0.theta ^ (F0.planClaimsF + (tl.eqFirst.getD tl.NM 0 + q * tl.stepF)) *
        Reading.gl.val ((tl.gamV.getD y.1.mat #[]).getD c zeroE)) := by
  have hmem : y ∈ readsList tl funs := List.mem_of_getElem? hq
  have ht : (List.range tl.NM).map
        (tieTerm Reading.gl (oneAt tU (pos / colsU F0 tU) (pos % colsU F0 tU)) tl F0) =
      (List.range tl.NM).map (tieTerm Reading.gl allZero tl F0) :=
    List.map_congr_left fun mu hmu => by
      unfold tieTerm
      rw [tieBracket_same tl mu tU _ _ hZ (hg mu (List.mem_range.1 hmu))]
  have hval : readTerm Reading.gl (oneAt tU (pos / colsU F0 tU) (pos % colsU F0 tU)) tl F0 (0 + q) y -
      readTerm Reading.gl allZero tl F0 (0 + q) y =
      -(Reading.gl.val F0.theta ^ (F0.planClaimsF + (tl.eqFirst.getD tl.NM 0 + q * tl.stepF)) *
        Reading.gl.val ((tl.gamV.getD y.1.mat #[]).getD c zeroE)) := by
    unfold readTerm
    rw [← mul_sub, readBracket_diff tl F0 y tU _ _ hZ (hU y hmem).1,
      runSum_pick _ _ c hc (fun d hd hne => by
        rw [entry_at, if_neg, mul_zero]
        intro e
        rcases Nat.lt_or_gt_of_ne hne with h1 | h1
        · exact hcol y hmem d c h1 hc (e.trans hpos.symm)
        · exact hcol y hmem c d h1 hd (hpos.trans e.symm)),
      entry_at, hpos, if_pos rfl, Nat.zero_add]
    ring
  have hoff : ∀ j z, (readsList tl funs)[j]? = some z → j ≠ q →
      readTerm Reading.gl (oneAt tU (pos / colsU F0 tU) (pos % colsU F0 tU)) tl F0 (0 + j) z -
        readTerm Reading.gl allZero tl F0 (0 + j) z = 0 := by
    intro j z hj hne
    have hz : z ∈ readsList tl funs := List.mem_of_getElem? hj
    obtain ⟨hjl, hjz⟩ := List.getElem?_eq_some_iff.1 hj
    obtain ⟨hql, hqy⟩ := List.getElem?_eq_some_iff.1 hq
    have hP := List.pairwise_iff_getElem.1 hap
    have hA : PlacesApart tl z y := by
      rcases Nat.lt_or_gt_of_ne hne with h1 | h1
      · have h2 := hP j q hjl hql h1
        rwa [hjz, hqy] at h2
      · have h2 := hP q j hql hjl h1
        rw [hjz, hqy] at h2
        exact h2.symm
    unfold readTerm
    rw [← mul_sub, readBracket_diff tl F0 z tU _ _ hZ (hU z hz).1,
      runSum_nil _ _ (fun d hd => by
        rw [entry_at, if_neg, mul_zero]
        intro e
        exact hA (by rw [(hU z hz).2, (hU y hmem).2]) d hd c hc (e.trans hpos.symm)),
      neg_zero, mul_zero]
  rw [ht, add_sub_add_left_eq_sub, sumFrom_sub,
    sumFrom_pick _ (readsList tl funs) 0 q y hq hoff]
  exact hval

/-! ## A yes of the list, cut -/

/-- What the smallness test's data tl1, behind the step that lays the powers of chi, have in common
with the data tl that were handed in: every function f that does not read the fields that the text
sets. -/
theorem same1 {α : Type} (f : HTailF2 → α) {n₀ : Nat} {tl tl' tl1 : HTailF2} {funs : Array HFun}
    {F₁ F₂ : Fork} {k8 : List Claim} (h : equations n₀ tl funs F₁ = .ok (tl', F₂, k8))
    (etl : tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid })
    (r1 : ∀ (t : HTailF2) (x : Option Nat), f { t with joinObj9 := x } = f t)
    (r2 : ∀ (t : HTailF2) (x : E), f { t with bitFactor9 := x } = f t)
    (r3 : ∀ (t u : HTailF2),
      f { t with
          vt := u.vt, vp := u.vp, eqFirst := u.eqFirst, rowX := u.rowX, loX := u.loX,
          gamX := u.gamX, gamV := u.gamV, foldTakenF := u.foldTakenF } = f t)
    (r4 : ∀ (t : HTailF2) (x y : Array Nat) (z : Nat),
      f { t with tieObj := x, tiesOn := y, nX4Laid := z } = f t) : f tl1 = f tl :=
  ((congrArg f etl).trans (r4 _ _ _ _)).symm.trans (eq_same f h r1 r2 r3 r4)

/-- **A yes of "K8.equations", cut.** The list is four claims and then the ties and reads. tl1: the
data with the powers of chi laid. To add the ties and reads to a ledger that has kept F₁'s batching
element, plan's number and arrays' frame keeps these, counts them, and lets the ledger's value grow,
in every world, by the ties' and reads' terms. -/
theorem k8_cut {n₀ : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F₁ F₂ : Fork} {k8 : List Claim}
    (h : equations n₀ tl funs F₁ = .ok (tl', F₂, k8)) :
    ∃ tl1 : HTailF2, Powered tl1 F₁.theta ∧
      (∀ mu, mu < tl1.NM → tl1.gamV.getD mu #[] = gamAt tl1 mu) ∧
      tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid } ∧
      (k8.take 4).length = 4 ∧ k8.length = 4 + (tl.NM + (readsList tl funs).length) ∧
      ∀ (W : World Cb.Gl.E) (A A' : Fork), Kept F₁ A → addAll A (k8.drop 4) = some A' →
        Kept F₁ A' ∧ A'.nClaim = A.nClaim + (tl.NM + (readsList tl funs).length) ∧
        A'.total Reading.gl W = A.total Reading.gl W +
          (((List.range tl1.NM).map (tieTerm Reading.gl W tl1 F₁)).sum +
            sumFrom (readTerm Reading.gl W tl1 F₁) 0 (readsList tl1 funs)) := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, hcl⟩ := eq_parts h
  obtain ⟨tl1, hW, -, -, etl, -, new, hs', hlen, -⟩ :=
    eqTail_total Reading.gl allZero F₁ before tlb tl' funs n₀ s2 (F₂, arr) k9
  obtain ⟨hP, -, hgam⟩ := eqWeights_spec tlb tl1 n₀ s2 s2 hW
  have os := eq_side h
  have hF : F₂ = s2.1 := congrArg Prod.fst hs'
  have eNM : tl1.NM = tl.NM :=
    same1 (fun t => t.NM) h etl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eL : readsList tl1 funs = readsList tl funs :=
    same1 (fun t => readsList t funs) h etl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  obtain ⟨four, rest, hc4, hl4, hlr⟩ := eq_split Reading.gl allZero h
  have hk8 : k8.length = 4 + (tl.NM + (readsList tl funs).length) := by
    rw [hc4, List.length_append, hl4, hlr]
  have cutOf : ∀ nw : List Claim, (F₂, arr) = (s2.1, s2.2 ++ nw.toArray) →
      nw.length = tl1.NM + (readsList tl1 funs).length → k8.drop 4 = nw := by
    intro nw hs hl
    have harr : arr = s2.2 ++ nw.toArray := congrArg Prod.snd hs
    have hl8 : k8 = s2.2.toList ++ nw := by
      rw [← hcl, harr]
      simp
    have h4 : s2.2.toList.length = 4 := by
      have h5 := congrArg List.length hl8
      rw [List.length_append, hk8, hl, eNM, eL] at h5
      omega
    rw [hl8]
    exact List.drop_left' h4
  refine ⟨tl1, ?_, fun mu hmu => (hgam mu hmu).2, etl, ?_, hk8, ?_⟩
  · rw [← os.theta, hF]
    exact hP
  · rw [List.length_take, hk8]
    omega
  · intro W A A' hk hA
    obtain ⟨tl2, hW2, -, -, -, -, nw, hs2, hl2, hp⟩ :=
      eqTail_total Reading.gl W F₁ before tlb tl' funs n₀ s2 (F₂, arr) k9
    have e12 : tl2 = tl1 := congrArg Prod.fst (Except.ok.inj (hW2.symm.trans hW))
    subst e12
    rw [cutOf nw hs2 hl2] at hA
    have hfr : Fr F₁ s2.1 := by
      unfold Fr
      rw [← hF, os.trees]
    obtain ⟨k1, k2, k3⟩ := hp hfr A A' hk hA
    exact ⟨k1, by rw [k2, eNM, eL], k3⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.reads_weight
#print axioms VerifiableInference.Desc.First.K8.Honest.k8_cut
