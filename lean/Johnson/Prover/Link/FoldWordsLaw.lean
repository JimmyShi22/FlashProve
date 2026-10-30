-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldWordsLaw.lean: THE FOLD's PROVER ON WORDS
(Johnson/Prover/Link/FoldWordsOf.lean), READ IN THE FIELD: FIRST PART: what "FOLD epsilon" sends;
and three general lemmas for the rounds. By the library's readings of the format's arithmetic
(OnBytes/Slice/SimBasic.lean, SimFold.lean) and its sumcheck (Cb/Ld/); of this folder it imports
FoldWordsOf.lean alone. On the format's triples of words (Fmt.M1.E), read by toE.

Main names (namespace Johnson.Prover.Link).
  coefNamed, coefU, coefNamed_hIx, coefNamed_hCst   the 2 k + 1 coefficients, read in the field,
      under the library's names (hIx, hCst, Cb/Ld/LdSumPack.lean).
  toE_hidePoly   the library's word polynomial at a point reads as the field's hU.
  cube_sum   a sum over the library's list of the cube's points is the field's hSumAll.
  toE_sigma, sigma_reads   WHAT "FOLD epsilon" SENDS READS AS THE FIELD's hMu, at every k and w.
  coeffs_read   the library's three coefficients from the values at 0, 1 and -1: the constant and
      the quadratic one are the polynomial's own.
  roundPart, ReadsTo   round number i's three coefficients; the words read as a point's first
      coordinates.
  roundPoly_reads   where a function on words reads as a summand, its sum over the later variables
      reads as the summand's round polynomial (HRounds, Cb/Ld/LdHide.lean). General in the summand.
  toE_dot_fold   two tables of 2^n rows of l entries, folded at a point and paired.

By calls: hSumAll_U, plain_psi (Cb/Ld/LdHideProofs.lean); sVars_ok, plain_sum (Cb/Ld/LdSumRun.lean);
toE_tailFoldl (SimFold.lean); toE_dot_of_le, vec_foldLow, size_foldLow, sum_range_cube, eqW_rowNo
(SimBasic.lean); gl_two_ne_zero (Cb/Pv/Head/NormGl.lean); Leaves.sum_flatMap
(OnBytes/Slice/BlkLeavesRows.lean); the field's readings of the format's operations
(OnBytes/Slice/Field.lean, FieldInv.lean).

Limits. Readings of words alone: nothing on a protocol. The rounds themselves:
Johnson/Prover/Link/FoldWordsShows.lean. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.FoldWordsOf
import OnBytes.Slice.SimFold
import Cb.Ld.LdSumRun
import Cb.Pv.Head.NormGl
import OnBytes.Slice.BlkLeavesRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open Fmt Fmt.M1 Fmt.M1.FoldOwn
open OnBytes.Slice Cb

/-! ## 1 The coefficients by their names -/

/-- Coefficients a l t (l, t from 0) and a constant, under the library's names. -/
def coefNamed : (k : ℕ) → (ℕ → ℕ → GE) → GE → HIdx (sVars GE 2 k) → GE
  | 0, _, c, _ => c
  | _ + 1, a, _, .inl t => a 0 t.val
  | k + 1, a, c, .inr i => coefNamed k (fun l => a (l + 1)) c i

theorem coefNamed_hIx : ∀ (k : ℕ) (a : ℕ → ℕ → GE) (c : GE) (l : Fin k) (p : Fin 2),
    coefNamed k a c (hIx GE 2 k l p) = a l.val p.val
  | 0, _, _, l, _ => l.elim0
  | k + 1, a, c, l, p => by
      refine Fin.cases ?_ (fun l' => ?_) l
      · rfl
      · exact coefNamed_hIx k (fun l => a (l + 1)) c l' p

theorem coefNamed_hCst : ∀ (k : ℕ) (a : ℕ → ℕ → GE) (c : GE), coefNamed k a c (hCst GE 2 k) = c
  | 0, _, _ => rfl
  | k + 1, a, c => coefNamed_hCst k (fun l => a (l + 1)) c

/-- The library's record of coefficients, read in the field, under the library's names. -/
def coefU (k : ℕ) (U : Hide) : HIdx (sVars GE 2 k) → GE :=
  coefNamed k (fun l t => toE (U.w (l + 1) (t + 1))) (toE U.w0)

/-! ## 2 Sums that are built up from the left -/

theorem toE_foldl_add {α : Type} (F : α → E) : ∀ (l : List α) (a : E),
    toE (l.foldl (fun s p => Fld.two.addE s (F p)) a) = toE a + (l.map fun p => toE (F p)).sum
  | [], a => by simp
  | p :: l, a => by
      rw [List.foldl_cons, toE_foldl_add F l, toE_addE, List.map_cons, List.sum_cons, add_assoc]

theorem sPt_ptK : ∀ (k : ℕ) (z : ℕ → GE) (l : Fin k), sPt 2 k (ptK k z) l = z l.val
  | 0, _, l => l.elim0
  | k + 1, z, l => by
      refine Fin.cases ?_ (fun l' => ?_) l
      · rfl
      · exact sPt_ptK k (fun t => z (t + 1)) l'

theorem ptK_cons (k : ℕ) (a : E) (p : List E) :
    ptK (k + 1) (lst (a :: p)) = (toE a, ptK k (lst p)) := rfl

/-! ## 3 The polynomial at a point -/

/-- The record with its first variable's two coefficients taken off. -/
def Hide.tl (U : Hide) : Hide := ⟨fun l t => U.w (l + 1) t, U.w0⟩

theorem coefU_inr (k : ℕ) (U : Hide) (i : HIdx (sVars GE 2 k)) :
    coefU (k + 1) U (.inr i) = coefU k (Hide.tl U) i := rfl

/-- The terms of the polynomial, as a sum over the variables' numbers. -/
theorem toE_hidePoly_sum (k : ℕ) (U : Hide) (xs : List E) :
    toE (hidePoly .two k U xs) = toE U.w0 + ((List.range k).map fun i =>
      (toE (U.w (i + 1) 1) * lst xs i + toE (U.w (i + 1) 2) * (lst xs i * lst xs i)) *
        toE (tailProd .two (xs.take k) (i + 1))).sum := by
  unfold hidePoly
  rw [toE_foldl_add]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  simp only [toE_mulE, toE_addE]
  rfl

theorem tailProd_cons (a : E) (l : List E) (i : ℕ) :
    tailProd .two (a :: l) (i + 1) = tailProd .two l i := rfl

theorem toE_tailProd_zero (l : List E) : toE (tailProd .two l 0) = (l.map toE).prod := by
  unfold tailProd
  rw [List.drop_zero, toE_tailFoldl, toE_oneE, one_mul]

theorem hPsi_ptK : ∀ (k : ℕ) (xs : List E), xs.length = k →
    hPsi (sVars GE 2 k) (ptK k (lst xs)) = (xs.map toE).prod
  | 0, [], _ => rfl
  | k + 1, a :: xs, h => by
      have ih := hPsi_ptK k xs (Nat.succ.inj h)
      show hev (HVar.plain GE 2).psi (toE a) * hPsi (sVars GE 2 k) (ptK k (lst xs)) = _
      rw [ih, plain_psi GE 2 (toE a) (by decide), List.map_cons, List.prod_cons]

/-- **The library's word polynomial at a point reads as the field's.** -/
theorem toE_hidePoly : ∀ (k : ℕ) (U : Hide) (xs : List E), xs.length = k →
    toE (hidePoly .two k U xs) = hU (sVars GE 2 k) (coefU k U) (ptK k (lst xs))
  | 0, U, [], _ => by
      rw [toE_hidePoly_sum]
      simp
      rfl
  | k + 1, U, a :: xs, h => by
      have hx : xs.length = k := Nat.succ.inj h
      have ih := toE_hidePoly k (Hide.tl U) xs hx
      rw [toE_hidePoly_sum] at ih ⊢
      show _ = hPsi (sVars GE 2 k) (ptK k (lst xs)) •
          hev (Fin.cons 0 fun t => coefU (k + 1) U (.inl t) : Fin 3 → GE) (toE a) +
        hU (sVars GE 2 k) (fun i => coefU (k + 1) U (.inr i)) (ptK k (lst xs))
      rw [show (fun i => coefU (k + 1) U (.inr i)) = coefU k (Hide.tl U) from rfl, ← ih,
        hPsi_ptK k xs hx, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      have e1 : (a :: xs).take (k + 1) = a :: xs.take k := rfl
      have e2 : xs.take k = xs := by rw [← hx]; exact List.take_length
      rw [e1, tailProd_cons, e2, toE_tailProd_zero]
      have e3 : hev (Fin.cons 0 fun t => coefU (k + 1) U (.inl t) : Fin 3 → GE) (toE a) =
          toE (U.w 1 1) * toE a + toE (U.w 1 2) * (toE a * toE a) := by
        unfold hev
        rw [Fin.sum_univ_three]
        simp only [smul_eq_mul]
        show toE a ^ 0 * 0 + toE a ^ 1 * toE (U.w 1 1) + toE a ^ 2 * toE (U.w 1 2) = _
        ring
      rw [e3, smul_eq_mul]
      have e4 : ((List.range k).map ((fun i =>
          (toE (U.w (i + 1) 1) * lst (a :: xs) i + toE (U.w (i + 1) 2) *
            (lst (a :: xs) i * lst (a :: xs) i)) * toE (tailProd .two (a :: xs) (i + 1))) ∘
            Nat.succ)).sum =
          ((List.range k).map fun i =>
            (toE ((Hide.tl U).w (i + 1) 1) * lst xs i + toE ((Hide.tl U).w (i + 1) 2) *
              (lst xs i * lst xs i)) * toE (tailProd .two xs (i + 1))).sum := rfl
      rw [e4]
      show toE U.w0 + ((toE (U.w 1 1) * toE a + toE (U.w 1 2) * (toE a * toE a)) *
        (xs.map toE).prod + _) = _
      show _ = _ + (toE U.w0 + _)
      ring

/-! ## 4 The sum over the cube -/

theorem length_cube : ∀ (n : ℕ) (p : List E), p ∈ cube n → p.length = n
  | 0, p, h => by
      rw [show cube 0 = [[]] from rfl, List.mem_singleton] at h
      rw [h]; rfl
  | n + 1, p, h => by
      rw [show cube (n + 1) = (cube n).flatMap fun p => [Fld.zeroE :: p, Fld.oneE :: p] from rfl,
        List.mem_flatMap] at h
      obtain ⟨q, hq, hp⟩ := h
      have := length_cube n q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [this]

/-- **A sum over the library's list of the cube's points is the field's sum over all variables.** -/
theorem cube_sum : ∀ (n : ℕ) (G : HPt (sVars GE 2 n) → GE),
    ((cube n).map fun p => G (ptK n (lst p))).sum = hSumAll (sVars GE 2 n) G
  | 0, G => by
      show G (ptK 0 (lst [])) + 0 = G ()
      rw [add_zero]
      rfl
  | n + 1, G => by
      show _ = (HVar.plain GE 2).sum fun x => hSumAll (sVars GE 2 n) fun xs => G (x, xs)
      rw [plain_sum, ← cube_sum n, ← cube_sum n, ← List.sum_map_add]
      rw [show cube (n + 1) = (cube n).flatMap fun p => [Fld.zeroE :: p, Fld.oneE :: p] from rfl,
        List.map_flatMap, Leaves.sum_flatMap]
      refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
      show G (ptK (n + 1) (lst (Fld.zeroE :: p))) + (G (ptK (n + 1) (lst (Fld.oneE :: p))) + 0) = _
      rw [ptK_cons, ptK_cons, toE_zeroE, toE_oneE, add_zero]

/-! ## 5 "FOLD epsilon" -/

/-- The library's one scalar reads as the field's. -/
theorem toE_sigma (T : Trial) :
    toE (T.sigma .two) = hMu (sVars GE 2 T.k) (coefU T.k T.U) := by
  unfold Trial.sigma
  rw [toE_foldl_add, toE_zeroE, zero_add]
  have h := hSumAll_U (sVars GE 2 T.k) (sVars_ok 2 (by decide) T.k) (0 : GE) (coefU T.k T.U)
  simp only [smul_zero, zero_add] at h
  rw [← h, ← cube_sum]
  exact congrArg List.sum (List.map_congr_left fun p hp =>
    toE_hidePoly T.k T.U p (length_cube T.k p hp))

/-- **L1: WHAT "FOLD epsilon" SENDS READS AS THE FIELD's hMu**, at the 2 k + 1 words under the
library's names. -/
theorem sigma_reads (k : ℕ) (w : Fin (2 * k + 1) → E) :
    toE (foldSigmaW k w) = hMu (sVars GE 2 k) (coefU k (uOfBook k w)) :=
  toE_sigma (trialW k 0 #[] #[] #[] #[] w Fld.zeroE)

/-! ## 6 A round's three coefficients, from three values -/

theorem hev3 (c : Fin 3 → GE) (x : GE) : hev c x = c 0 + x * c 1 + x ^ 2 * c 2 := by
  unfold hev
  rw [Fin.sum_univ_three]
  simp

/-- **The library's three coefficients from the values at 0, 1 and -1**: the constant and the
quadratic one read as the polynomial's own. -/
theorem coeffs_read (c : Fin 3 → GE) (v0 v1 vm : E) (h0 : toE v0 = hev c (0 : GE))
    (h1 : toE v1 = hev c (1 : GE)) (hm : toE vm = hev c (-1 : GE)) :
    toE (coeffs .two v0 v1 vm).1 = c 0 ∧ toE (coeffs .two v0 v1 vm).2.2 = c 2 := by
  rw [hev3] at h0 h1 hm
  have h2 : (1 + 1 : GE) ≠ 0 := by
    rw [one_add_one_eq_two]
    exact Cb.Pv.Head.gl_two_ne_zero
  constructor
  · show toE v0 = c 0
    rw [h0]
    ring
  · show toE (Fld.two.subE (Fld.two.mulE (Fld.two.invE (Fld.two.addE Fld.oneE Fld.oneE))
      (Fld.two.addE v1 vm)) v0) = c 2
    rw [toE_subE, toE_mulE, toE_invE, toE_addE, toE_addE, toE_oneE, h0, h1, hm]
    field_simp
    ring

/-! ## 7 The rounds of any summand, read round by round -/

/-- Round number i's three coefficients. -/
def roundPart : (k : ℕ) → (RIdx (sVars GE 2 k) → GE) → ℕ → Fin 3 → GE
  | 0, _, _, _ => 0
  | _ + 1, q, 0, t => q (.inl t)
  | k + 1, q, i + 1, t => roundPart k (fun j => q (.inr j)) i t

/-- The words read as the point's first coordinates. -/
def ReadsTo : (k : ℕ) → List E → HPt (sVars GE 2 k) → Prop
  | _, [], _ => True
  | 0, _ :: _, _ => False
  | k + 1, g :: gs, γ => toE g = γ.1 ∧ ReadsTo k gs γ.2

/-- **Where a function on words reads as a summand, its sum over the later variables, the earlier
ones at the sampled words, reads as the summand's round polynomial.** General in the summand. -/
theorem roundPoly_reads : ∀ (k : ℕ) (f : HPt (sVars GE 2 k) → GE) (q : RIdx (sVars GE 2 k) → GE)
    (γ : HPt (sVars GE 2 k)), HRounds (sVars GE 2 k) f q γ → ∀ (F : List E → E),
    (∀ xs, xs.length = k → toE (F xs) = f (ptK k (lst xs))) → ∀ (gs : List E) (X : E),
    gs.length < k → ReadsTo k gs γ →
    toE ((cube (k - gs.length - 1)).foldl (fun s p => Fld.two.addE s (F (gs ++ X :: p)))
      Fld.zeroE) = hev (roundPart k q gs.length) (toE X)
  | 0, _, _, _, _, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, f, q, γ, H, F, hF, [], X, _, _ => by
      show toE ((cube k).foldl (fun s p => Fld.two.addE s (F (X :: p))) Fld.zeroE) =
        hev (fun t => q (.inl t)) (toE X)
      rw [H.1 (toE X), toE_foldl_add, toE_zeroE, zero_add, ← cube_sum]
      refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
      rw [hF (X :: p) (by rw [List.length_cons, length_cube k p hp]), ptK_cons]
  | k + 1, f, q, γ, H, F, hF, g :: gs, X, hl, hr => by
      have ih := roundPoly_reads k (fun xs => f (γ.1, xs)) (fun j => q (.inr j)) γ.2 H.2
        (fun xs => F (g :: xs))
        (fun xs hx => by rw [hF (g :: xs) (by rw [List.length_cons, hx]), ptK_cons, hr.1])
        gs X (Nat.lt_of_succ_lt_succ hl) hr.2
      have e : k + 1 - (g :: gs).length - 1 = k - gs.length - 1 := by
        rw [List.length_cons]
        omega
      rw [e]
      exact ih

/-! ## 8 A folded inner product -/

theorem size_foldLow_of (n l : ℕ) (g : List E) (hg : g.length = n) (T : Array E)
    (hT : T.size = 2 ^ n * l) : (foldLow .two g T).size = l := by
  rw [size_foldLow, hg, hT, Nat.add_sub_assoc Nat.one_le_two_pow,
    Nat.mul_add_div (Nat.two_pow_pos n), Nat.div_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos n)
      Nat.one_pos), Nat.add_zero]

/-- **Two tables of 2^n rows of l entries, folded at a point and paired.** -/
theorem toE_dot_fold (n l : ℕ) (g : List E) (hg : g.length = n) (c m : Array E)
    (hc : c.size = 2 ^ n * l) :
    toE (dot .two (foldLow .two g c) (foldLow .two g m)) =
      ∑ p : Fin l, (∑ β : Fin n → Bool, vec c (Sz.rowNo β + 2 ^ n * p.val) *
          Alg.eqk (fun t : Fin n => lst g t.val) β) *
        ∑ β : Fin n → Bool, Alg.eqk (fun t : Fin n => lst g t.val) β *
          vec m (Sz.rowNo β + 2 ^ n * p.val) := by
  rw [toE_dot_of_le _ _ l (by rw [size_foldLow_of n l g hg c hc]; exact Nat.min_le_left _ _),
    Finset.sum_range]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vec_foldLow, vec_foldLow, hg, sum_range_cube, sum_range_cube]
  congr 1
  · exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo, mul_comm]
  · exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.coefNamed_hIx
#print axioms Johnson.Prover.Link.coefNamed_hCst
#print axioms Johnson.Prover.Link.toE_foldl_add
#print axioms Johnson.Prover.Link.sPt_ptK
#print axioms Johnson.Prover.Link.ptK_cons
#print axioms Johnson.Prover.Link.coefU_inr
#print axioms Johnson.Prover.Link.toE_hidePoly_sum
#print axioms Johnson.Prover.Link.tailProd_cons
#print axioms Johnson.Prover.Link.toE_tailProd_zero
#print axioms Johnson.Prover.Link.hPsi_ptK
#print axioms Johnson.Prover.Link.toE_hidePoly
#print axioms Johnson.Prover.Link.length_cube
#print axioms Johnson.Prover.Link.cube_sum
#print axioms Johnson.Prover.Link.toE_sigma
#print axioms Johnson.Prover.Link.sigma_reads
#print axioms Johnson.Prover.Link.hev3
#print axioms Johnson.Prover.Link.coeffs_read
#print axioms Johnson.Prover.Link.roundPoly_reads
#print axioms Johnson.Prover.Link.size_foldLow_of
#print axioms Johnson.Prover.Link.toE_dot_fold
