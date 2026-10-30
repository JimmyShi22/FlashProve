-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/SmallLawProofs.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE:
proofs of the statements of Honest/K8/SmallLaw.lean but the last: where no combination leaves its
window, every single equation of the ties and reads holds at a table that is made of the cells, and
the digits are in their tables. LEMMAS ON THE HONEST PROVER's ARRAYS; NONE OF THE LIBRARY's GOALS.

  `signOf_trit`      an entry -1, 0 or 1 read by its sign is the entry
  `thAt`, `comb_cast`   a combination, in the field, as a sum over the matrix's columns of the drawn
                      entries, as the library's single equations read them, times the cells
  `pack_same`        the packing of a column does not see how its number of rows is spelled
  `zzCol_lt`         the verifier's two columns for a row of cells lie in the array's columns
  `zzCol_shift`      the verifier's column for a row, counted from another row of the same matrix
  `mem_rowsFrom`     a row of the list of the reads' equations is the equation of a read of the list
  `tieOf_of_tieBy`, `zz_back`, `ties_zero`, `reads_zero`, `digits_in`, **`small_of_honest`**
The limits are those of Honest/K8/SmallLaw.lean.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SmallLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Tie.Pv.Tail.Port
open VerifiableInference.Desc.First.K8 (Par firstColumns TieOf DigitsOf)
open VerifiableInference.Desc.First.K8.Honest

theorem tieOf_of_tieBy : Spec.tieOf_of_tieBy := fun _ _ a h hb => ⟨a, hb, h.1, h.2⟩

/-- An entry -1, 0 or 1 read by its sign is the entry. -/
theorem signOf_trit (x : ℤ) (h : x = -1 ∨ x = 0 ∨ x = 1) :
    signOf (K := Cb.Gl.E) x = (x : Cb.Gl.E) := by
  rcases h with rfl | rfl | rfl <;> simp [signOf]

/-- The place's columns of matrix mu are the state's. -/
theorem ks_getD (tl : HTailF2) (μ : ℕ) (h : μ < tl.mats.size) :
    (parOfTail tl).ks.getD μ 0 = (tl.mats.getD μ {}).k := by
  simp [parOfTail, Array.getElem?_eq_getElem h]

/-- The drawn entry of column c of matrix mu and combination u, as the library's single equations
read it. -/
def thAt (tl : HTailF2) (μ u c : ℕ) : Cb.Gl.E :=
  signOf (K := Cb.Gl.E) (tl.cfF.getD ((tl.cfFirst.getD μ 0 + c) * tl.tau + u) 0)

/-- A combination, in the field. -/
theorem comb_cast (tl : HTailF2) (hD : DrawLaid tl) (a : CellsAt) (μ i u : ℕ) (hμ : μ < tl.NM) :
    ((comb (parOfTail tl) a tl.cfF μ i u : ℤ) : Cb.Gl.E) =
      ∑ c ∈ Finset.range (tl.mats.getD μ {}).k, thAt tl μ u c * ((a μ i c : ℤ) : Cb.Gl.E) := by
  have hs : μ < tl.mats.size := hD.digits.nm ▸ hμ
  have e := foldl_range_add ((parOfTail tl).ks.getD μ 0)
    (fun c => entry (parOfTail tl) tl.cfF μ c u * a μ i c)
  unfold comb
  rw [e, Fin.sum_univ_eq_sum_range (fun c => entry (parOfTail tl) tl.cfF μ c u * a μ i c),
    ks_getD tl μ hs]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold thAt entry
  rw [hD.first, signOf_trit _ (hD.trits _)]
  rfl

/-- The verifier's two columns for a row of cells lie in the array's columns. -/
theorem zzCol_lt (tl : HTailF2) (h : DigitColsFit tl) (μ i : ℕ) (hμ : μ < tl.NM)
    (hi : i < (tl.mats.getD μ {}).m) :
    (tl.zzCol μ 0 0).getD 0 + i < 2 * tl.mz ∧ (tl.zzCol μ 1 0).getD 0 + i < 2 * tl.mz := by
  have hs : μ < tl.mats.size := h.nm ▸ hμ
  have hr := rowAt_at (parOfTail tl).ms μ i (by simpa [parOfTail] using hs)
    (by rw [ms_getD tl μ hs]; exact hi)
  have hlt := rowAt_lt (parOfTail tl) _ μ i hr
  rw [zzCol_low tl h μ i hμ hi, zzCol_high tl h μ i hμ hi, mz_allRows tl h]
  omega

theorem zz_back : Spec.zz_back := by
  intro tl A a hD hZ hl μ hμ u hu i hi
  have hs : μ < tl.mats.size := hD.nm ▸ hμ
  obtain ⟨hc0, hc1⟩ := zzCol_lt tl hD μ i hμ hi
  have hr := rowAt_at (parOfTail tl).ms μ i (by simpa [parOfTail] using hs)
    (by rw [ms_getD tl μ hs]; exact hi)
  have hw := comb_inWindow (parOfTail tl) a tl.cfF hl _ μ i u hr hu
  have e := congrArg (fun x : ℤ => (x : Cb.Gl.E)) (digits_back _ hw)
  have h0 : t2D0 = 10 := rfl
  have h17 : lbz = 17 := rfl
  rw [h0, h17] at e
  push_cast at e
  rw [hZ u hu _ hc0, hZ u hu _ hc1, digitAt_low tl hD a tl.cfF μ u i hμ hu hi,
    digitAt_high tl hD a tl.cfF μ u i hμ hu hi]
  exact e

/-- The packing of a column does not see how its number of rows is spelled. -/
theorem pack_same {R : Type} [CommRing R] {m m' : ℕ} (h : m = m') (rad : ℤ) (f : ℕ → R)
    (i' : ℕ) :
    Alg.pack rad (fun i : Fin m => f i) i' = Alg.pack rad (fun i : Fin m' => f i) i' := by
  subst h
  rfl

theorem ties_zero : Spec.ties_zero := by
  intro tl A a hD hF hT hZ hl r hr
  unfold tieRows at hr
  obtain ⟨mu, hmu, hr⟩ := List.mem_flatMap.1 hr
  have hmu' : mu < tl.NM := List.mem_range.1 hmu
  unfold tieRowsAt at hr
  obtain ⟨i', _, hr⟩ := List.mem_flatMap.1 hr
  obtain ⟨u, _, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hm, hk⟩ := hF mu hmu'
  show Alg.pack ((2 : ℤ) ^ 20)
        (fun i : Fin (tl.shp.getD mu {}).m =>
          A tl.ix.ZZ u ((tl.zzCol mu 0 0).getD 0 + i) +
            (2 : Cb.Gl.E) ^ 10 * A tl.ix.ZZ u ((tl.zzCol mu 1 0).getD 0 + i) - (2 : Cb.Gl.E) ^ 17)
        i' -
      ∑ c : Fin (tl.shp.getD mu {}).k,
        thOf tl mu (tl.shp.getD mu {}).k u c * A (tl.gtTree.getD mu 0) i' c = 0
  have e1 : (fun i : Fin (tl.shp.getD mu {}).m =>
      A tl.ix.ZZ u ((tl.zzCol mu 0 0).getD 0 + i) +
        (2 : Cb.Gl.E) ^ 10 * A tl.ix.ZZ u ((tl.zzCol mu 1 0).getD 0 + i) - (2 : Cb.Gl.E) ^ 17) =
      fun i : Fin (tl.shp.getD mu {}).m => ∑ c ∈ Finset.range (tl.mats.getD mu {}).k,
        thAt tl mu u c * ((a mu i c : ℤ) : Cb.Gl.E) :=
    funext fun i => by
      rw [zz_back tl A a hD.digits hZ hl mu hmu' u u.isLt i (hm ▸ i.isLt),
        comb_cast tl hD a mu i u hmu']
  have e2 : ∑ c : Fin (tl.shp.getD mu {}).k,
      thOf tl mu (tl.shp.getD mu {}).k u c * A (tl.gtTree.getD mu 0) i' c =
      ∑ c ∈ Finset.range (tl.mats.getD mu {}).k,
        thAt tl mu u c * A (tl.gtTree.getD mu 0) i' c := by
    rw [← hk]
    exact Fin.sum_univ_eq_sum_range (fun c => thAt tl mu u c * A (tl.gtTree.getD mu 0) i' c) _
  have hrad : ((radb : ℕ) : ℤ) = (2 : ℤ) ^ 20 := by decide
  rw [e1, e2, Alg.pack_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Alg.pack_mul_left, Alg.pack_intCast,
    hT.1 mu hmu' c (Finset.mem_range.1 hc) i' (hm ▸ i'.isLt), hrad,
    pack_same hm ((2 : ℤ) ^ 20) (fun i => a mu i c) i']

/-- The verifier's column for a row, counted from another row of the same matrix. -/
theorem zzCol_shift (tl : HTailF2) (μ pl i₀ j : ℕ) (hμ : μ < tl.NM) (hp : pl ≤ 1)
    (h : i₀ < (tl.mats.getD μ {}).m) :
    (tl.zzCol μ pl i₀).getD 0 + j = (tl.zzCol μ pl 0).getD 0 + (i₀ + j) := by
  have h0 : 0 < (tl.mats.getD μ {}).m := by omega
  have hb : (decide (μ < tl.NM) && decide (pl ≤ 1) && decide (i₀ < (tl.mats.getD μ {}).m)) =
      true := by
    rw [decide_eq_true hμ, decide_eq_true hp, decide_eq_true h]
    rfl
  have hb0 : (decide (μ < tl.NM) && decide (pl ≤ 1) && decide (0 < (tl.mats.getD μ {}).m)) =
      true := by
    rw [decide_eq_true hμ, decide_eq_true hp, decide_eq_true h0]
    rfl
  unfold HTailF2.zzCol
  rw [if_pos hb, if_pos hb0, Option.getD_some, Option.getD_some]
  omega

/-- A row of the list of the reads' equations is the equation of a read of the list. -/
theorem mem_rowsFrom {K : Type} {tau : ℕ} (e : ℕ → ℕ → ℕ) (g : HFun × ℕ → Fin tau → Gap K) :
    ∀ (l : List (HFun × ℕ)) (q : ℕ) (r : ℕ × Gap K), r ∈ rowsFrom e g q l →
      ∃ x ∈ l, ∃ u, r.2 = g x u
  | [], _, _, h => by simp [rowsFrom] at h
  | x :: l, q, r, h => by
    unfold rowsFrom at h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨u, _, rfl⟩ := List.mem_map.1 h
      exact ⟨x, List.mem_cons_self, u, rfl⟩
    · obtain ⟨y, hy, u, hu⟩ := mem_rowsFrom e g l (q + 1) r h
      exact ⟨y, List.mem_cons_of_mem _ hy, u, hu⟩

theorem reads_zero : Spec.reads_zero := by
  intro tl A a hD h3 hT hZ hl r hr
  obtain ⟨⟨Fn, sg⟩, hx, u, hru⟩ := mem_rowsFrom _ _ _ _ r hr
  obtain ⟨hFn, hmat, _, hsg⟩ := (mem_readsList tl tl.funs Fn sg).1 hx
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hFn
  have hn' : tl.funs[n]? = some Fn := by simpa using hn
  have hlen : Fn.len ≠ 0 := by
    intro h0
    rw [h0, Nat.div_zero] at hsg
    omega
  have hrow : ∀ j, j < Fn.len → sg * Fn.len + j < (tl.mats.getD Fn.mat {}).m := by
    intro j hj
    have h1 : (sg + 1) * Fn.len ≤ (tl.mats.getD Fn.mat {}).m / Fn.len * Fn.len :=
      Nat.mul_le_mul_right _ hsg
    have h2 := Nat.div_mul_le_self (tl.mats.getD Fn.mat {}).m Fn.len
    have h3 : (sg + 1) * Fn.len = sg * Fn.len + Fn.len := by ring
    omega
  have hu3 : uOf tl Fn = u3Of tl := by
    unfold uOf u3Of
    rw [h3 Fn hFn]
  rw [hru]
  show ∑ j : Fin Fn.len, Reading.gl.val (Fn.phi.getD j zeroE) *
        (A tl.ix.ZZ u ((tl.zzCol Fn.mat 0 (sg * Fn.len)).getD 0 + j) +
          (2 : Cb.Gl.E) ^ 10 * A tl.ix.ZZ u ((tl.zzCol Fn.mat 1 (sg * Fn.len)).getD 0 + j) -
          (2 : Cb.Gl.E) ^ 17) -
      ∑ c : Fin (tl.mats.getD Fn.mat {}).k,
        thOf tl Fn.mat (tl.mats.getD Fn.mat {}).k u c * A (uOf tl Fn) 0 (posOf tl Fn sg c) = 0
  have e1 : ∑ j : Fin Fn.len, Reading.gl.val (Fn.phi.getD j zeroE) *
        (A tl.ix.ZZ u ((tl.zzCol Fn.mat 0 (sg * Fn.len)).getD 0 + j) +
          (2 : Cb.Gl.E) ^ 10 * A tl.ix.ZZ u ((tl.zzCol Fn.mat 1 (sg * Fn.len)).getD 0 + j) -
          (2 : Cb.Gl.E) ^ 17) =
      ∑ j ∈ Finset.range Fn.len, ∑ c ∈ Finset.range (tl.mats.getD Fn.mat {}).k,
        Reading.gl.val (Fn.phi.getD j zeroE) *
          (thAt tl Fn.mat u c * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ c ∈ Finset.range (tl.mats.getD Fn.mat {}).k,
      Reading.gl.val (Fn.phi.getD j zeroE) *
        (thAt tl Fn.mat u c * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E))) Fn.len]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h0 : sg * Fn.len < (tl.mats.getD Fn.mat {}).m := by
      have := hrow j j.isLt
      omega
    rw [zzCol_shift tl Fn.mat 0 _ j hmat (Nat.zero_le 1) h0,
      zzCol_shift tl Fn.mat 1 _ j hmat (Nat.le_refl 1) h0,
      zz_back tl A a hD.digits hZ hl Fn.mat hmat u u.isLt _ (hrow j j.isLt),
      comb_cast tl hD a Fn.mat _ u hmat, Finset.mul_sum]
  have e2 : ∑ c : Fin (tl.mats.getD Fn.mat {}).k,
        thOf tl Fn.mat (tl.mats.getD Fn.mat {}).k u c * A (uOf tl Fn) 0 (posOf tl Fn sg c) =
      ∑ c ∈ Finset.range (tl.mats.getD Fn.mat {}).k, ∑ j ∈ Finset.range Fn.len,
        Reading.gl.val (Fn.phi.getD j zeroE) *
          (thAt tl Fn.mat u c * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun c => ∑ j ∈ Finset.range Fn.len,
      Reading.gl.val (Fn.phi.getD j zeroE) *
        (thAt tl Fn.mat u c * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E)))
      (tl.mats.getD Fn.mat {}).k]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hb : (decide (Fn.mat < tl.NM) && (Fn.len != 0)) = true := by
      rw [decide_eq_true hmat, bne_iff_ne.2 hlen]
      rfl
    have hb2 : (decide ((c : ℕ) < (tl.mats.getD Fn.mat {}).k) &&
        decide (sg < (tl.mats.getD Fn.mat {}).m / Fn.len)) = true := by
      rw [decide_eq_true c.isLt, decide_eq_true hsg]
      rfl
    have htab : tl.tabAt Fn c sg =
        some (Fn.start + c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg) := by
      unfold HTailF2.tabAt
      rw [if_pos hb]
      exact if_pos hb2
    have hpos : posOf tl Fn sg c = Fn.start + c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg := by
      unfold posOf
      rw [htab, Option.getD_some]
    rw [hu3, hpos, hT.2 n Fn hn' c sg _ htab, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show thAt tl Fn.mat u c * _ = _
    ring
  rw [e1, e2, Finset.sum_comm, sub_self]

theorem digits_in : Spec.digits_in := by
  intro tl A a hD hZ μ hμ u hu i hi
  obtain ⟨hc0, hc1⟩ := zzCol_lt tl hD μ i hμ hi
  refine ⟨⟨low (comb (parOfTail tl) a tl.cfF μ i u), low_lt _, ?_⟩,
    ⟨high (comb (parOfTail tl) a tl.cfF μ i u), high_lt _, ?_⟩⟩
  · rw [hZ u hu _ hc0, digitAt_low tl hD a tl.cfF μ u i hμ hu hi]
  · rw [hZ u hu _ hc1, digitAt_high tl hD a tl.cfF μ u i hμ hu hi]

/-- **Where no combination leaves its window, both sentences behind the draw hold.** -/
theorem small_of_honest : Spec.small_of_honest := by
  intro tl A a hD hF h3 hT hZ hl
  refine ⟨fun r hr => ?_, digits_in tl A a hD.digits hZ⟩
  unfold rowsTail at hr
  rcases List.mem_append.1 hr with h | h
  · exact ties_zero tl A a hD hF hT hZ hl r h
  · exact reads_zero tl A a hD h3 hT hZ hl r h

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.tieOf_of_tieBy
#print axioms ProofFile.Honest.K8.zz_back
#print axioms ProofFile.Honest.K8.ties_zero
#print axioms ProofFile.Honest.K8.reads_zero
#print axioms ProofFile.Honest.K8.digits_in
#print axioms ProofFile.Honest.K8.small_of_honest
#print axioms ProofFile.Honest.K8.signOf_trit
#print axioms ProofFile.Honest.K8.ks_getD
#print axioms ProofFile.Honest.K8.thAt
#print axioms ProofFile.Honest.K8.comb_cast
#print axioms ProofFile.Honest.K8.zzCol_lt
#print axioms ProofFile.Honest.K8.pack_same
#print axioms ProofFile.Honest.K8.zzCol_shift
#print axioms ProofFile.Honest.K8.mem_rowsFrom
