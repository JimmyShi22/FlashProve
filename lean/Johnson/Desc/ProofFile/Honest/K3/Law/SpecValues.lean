-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecValues.lean: the honest side of the kind "lookup" (K3).
What the specification's true sums, end values and summands come to in the verifier's terms.
Theorems.

Terms. Honest/K3/GLOSSARY.md ("job, summand", "level", "specification", "tie").

What is shown, by the file's sections.
  1. `endTerm_tie0`, `endTerm_tie`, `endTerm_level`, `endTerm_bits`: the verifier's end terms on
     shown end values, read, are the jobs' summands at these values.
  2. `orderOk_of_perm`, `byBit_behind`, `byVar_down`: points.
  3. `line_key`, `line_tab`: the line between a level's two true end values is the extension of the
     level below at the point behind the level.
  4. `key_top`, `tab_root`, `G_one`, `Pc_top`: the ends of the two trees.
  5. `leaves_fin`: the leaves' summand at a point.
`endTerm_level` speaks of the product of the two shown values, which is the level's end term by
definition.

Hypotheses that remain. `h`, `ho`, `hE`: an order is a permutation, or the default order. `hc`,
`hz`, `hx`: a list or a point is long enough, or has its length. `ha`: (in `endTerm_tie0`) a reads
as the data's public factor. `h`: (in `G_one`) the plane's bits are all 0.

Users. This file is imported by Honest/K3/Law/FaceOk.lean and Honest/K3/Law/SpecCourse.lean.

Limits. Facts on the specification's terms and on the verifier's end terms. No course is read here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecStage
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecStages
import Johnson.HonestTrace.LookRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE oneE addE subE mulE)
open OnBytes.Model (orderDefault)
open OnBytes.Slice (readE readE_add readE_sub readE_mul readE_zero readE_one)
open OnBytes.HonestTrace.Look (Job Data pj ext tieJob keyJob tabJob leavesJob bitsJob)
open VerifiableInference.Desc.First.ProdV (layBack orderOk)

variable {P : Type}

/-! ## 1 The verifier's end terms -/

theorem endTerm_tie0 (D : Data P KE) (a : E) (ha : up a = D.a) (v : List E) :
    rd (endTerm a (.tie 0) v) = (tieJob D 0).S0 (ups v) := by
  show readE (subE (v.getD 0 zeroE)
    (mulE a (mulE (mulE (v.getD 1 zeroE) (v.getD 1 zeroE)) (v.getD 2 zeroE)))) =
    (if (0 : Nat) = 0 then (ups v).getD 0 0 - D.a * ((ups v).getD 1 0 ^ 2 * (ups v).getD 2 0)
      else (ups v).getD 0 0 ^ 2 * (ups v).getD 1 0)
  rw [if_pos rfl, readE_sub, readE_mul, readE_mul, readE_mul, ← ha, ← up_getD, ← up_getD, ← up_getD]
  ring

theorem endTerm_tie (D : Data P KE) (a : E) (s : Nat) (v : List E) :
    rd (endTerm a (.tie (s + 1)) v) = (tieJob D (s + 1)).S0 (ups v) := by
  show readE (mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)) =
    (if s + 1 = 0 then (ups v).getD 0 0 - D.a * ((ups v).getD 1 0 ^ 2 * (ups v).getD 2 0)
      else (ups v).getD 0 0 ^ 2 * (ups v).getD 1 0)
  rw [if_neg (Nat.succ_ne_zero s), readE_mul, readE_mul, ← up_getD, ← up_getD]
  ring

/-- At a level of either tree. -/
theorem endTerm_level (m : Nat) (A B : Nat → KE) (o : List Nat) (z : List KE) (v : List E) :
    up (mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) = (pj m 0 A B o z).S0 (ups v) := by
  show readE _ = 0 + (ups v).getD 0 0 * (ups v).getD 1 0
  rw [readE_mul, ← up_getD, ← up_getD, zero_add]

theorem endTerm_bits (D : Data P KE) (a : E) (z : List KE) (v : List E) :
    rd (endTerm a .bits v) = (bitsJob D z).S0 (ups v) := by
  show readE (subE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 0 zeroE)) =
    (ups v).getD 0 0 * ((ups v).getD 0 0 - 1)
  rw [readE_sub, readE_mul, ← up_getD]
  ring

/-! ## 2 Points -/

/-- An order that lists the numbers below m, each once, passes the verifier's test. -/
theorem orderOk_of_perm {m : Nat} {o : List Nat} (h : o.Perm (List.range m)) :
    orderOk m o = true := by
  unfold orderOk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_range]
  refine ⟨⟨by rw [h.length_eq, List.length_range], fun b hb => List.mem_range.1 (h.mem_iff.1 hb)⟩,
    fun b hb => ?_⟩
  rw [h.count_eq, List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 hb)]

/-- **The point behind a level, translated.** -/
theorem byBit_behind (m : Nat) (o : List Nat) (cs : List E) (xi : E) (ho : o.Perm (List.range m))
    (hc : m ≤ cs.length) : byBit (behind m o cs xi) = TwV.byVar o (ups cs) ++ [up xi] := by
  unfold behind
  rw [byBit_stepDown, byBit_layBack m o cs (orderOk_of_perm ho) hc]

/-- By the order that counts down, challenges by round are the point reversed. -/
theorem byVar_down (xs : List KE) : TwV.byVar (orderDefault xs.length) xs = xs.reverse := by
  unfold TwV.byVar orderDefault
  apply List.ext_getElem
  · simp
  · intro c h1 h2
    have hc : c < xs.length := by simpa using h1
    have hn : (List.range xs.length).reverse.Nodup := List.nodup_reverse.2 List.nodup_range
    have hi : xs.length - 1 - c < (List.range xs.length).reverse.length := by simp; omega
    have e : (List.range xs.length).reverse[xs.length - 1 - c]'hi = c := by
      rw [List.getElem_reverse, List.getElem_range]
      simp
      omega
    have e2 : (List.range xs.length).reverse.idxOf c = xs.length - 1 - c := by
      conv_lhs => rw [← e]
      exact hn.idxOf_getElem _ hi
    rw [List.getElem_map, List.getElem_range, e2, List.getElem_reverse,
      List.getD_eq_getElem _ _ (by omega)]

/-! ## 3 The line between a level's two true end values -/

theorem line_key (D : Data P KE) (m : Nat) (z xs : List KE) (rho : KE)
    (ho : (D.N.oK m).Perm (List.range m)) :
    (1 - rho) * ((keyJob D m z).ends xs).getD 0 0 + rho * ((keyJob D m z).ends xs).getD 1 0 =
      ext (m + 1) (D.kLvl (m + 1)) (TwV.byVar (D.N.oK m) xs ++ [rho]) :=
  OnBytes.HonestTrace.Look.ext_line m (D.kLvl (m + 1)) _ rho
    (by rw [OnBytes.HonestTrace.Look.byVar_length, ho.length_eq, List.length_range])

theorem line_tab (D : Data P KE) (l : Nat) (z xs : List KE) (rho : KE)
    (ho : (D.N.oT l).Perm (List.range (D.N.w + l))) :
    (1 - rho) * ((tabJob D l z).ends xs).getD 0 0 + rho * ((tabJob D l z).ends xs).getD 1 0 =
      ext (D.N.w + l + 1) (D.tLvl (l + 1)) (TwV.byVar (D.N.oT l) xs ++ [rho]) :=
  OnBytes.HonestTrace.Look.ext_line (D.N.w + l) (D.tLvl (l + 1)) _ rho
    (by rw [OnBytes.HonestTrace.Look.byVar_length, ho.length_eq, List.length_range])

/-! ## 4 The ends of the two trees -/

/-- The key tree's lowest level, extended at a point of v coordinates, is alpha less the keys'
extension there. -/
theorem key_top (D : Data P KE) (z : List KE) (hz : z.length = D.v) :
    ext D.v (D.kLvl D.v) z = D.al - ext D.v D.key z := by
  have h1 := _root_.Fo.eqN_total z
  rw [hz] at h1
  unfold ext
  have e : ∀ X, D.kLvl D.v X = D.al - D.key X := by
    intro X
    unfold Data.kLvl
    rw [Blocks.lvl_top]
    rfl
  rw [Finset.sum_congr rfl fun X _ => show TwV.eqN z X * D.kLvl D.v X =
    TwV.eqN z X * D.al - TwV.eqN z X * D.key X by rw [e]; ring,
    Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]

/-- The table side's highest level, extended: the planes' roots under the equality weights. -/
theorem tab_root (D : Data P KE) (z : List KE) :
    ext D.N.w (D.tLvl 0) z = ∑ j ∈ Finset.range (2 ^ D.N.w), TwV.eqN z j * D.G j :=
  Finset.sum_congr rfl fun j hj => by
    rw [OnBytes.HonestTrace.Look.tLvl_root D (Finset.mem_range.1 hj)]

/-- A plane whose bits are all 0 has the root 1. -/
theorem G_one (D : Data P KE) (j : Nat) (h : ∀ u, D.bits u j = 0) : D.G j = 1 := by
  show ∏ u ∈ Finset.range (2 ^ D.N.d), (1 + D.bits u j * (D.al - 1 - D.N.tab u)) = 1
  refine Finset.prod_eq_one fun u _ => ?_
  rw [h u, zero_mul, add_zero]

/-- The chain of the tie ends at the last plane's root. -/
theorem Pc_top (D : Data P KE) : D.Pc (D.N.n + 1) = D.G (D.N.n + 1) := by
  unfold Data.Pc
  rw [Nat.sub_self]
  rfl

/-! ## 5 The leaves' summand at a point -/

/-- The leaves' summand at the point of its challenges: 1 plus the planes' bits there times
alpha - 1 - the table's row there. -/
theorem leaves_fin (D : Data P KE) (z xs : List KE) (hx : xs.length = D.N.w + D.N.d)
    (hE : D.N.oE = orderDefault (D.N.w + D.N.d)) :
    (leavesJob D z).fin xs = 1 + ext (D.N.w + D.N.d) D.bitAt xs.reverse *
      ((List.range (2 ^ D.N.d)).map fun r =>
        TwV.eqN (xs.reverse.drop D.N.w) r * (D.al - 1 - D.N.tab r)).sum := by
  show 1 + ext (D.N.w + D.N.d) D.bitAt (TwV.byVar D.N.oE xs) *
    ext (D.N.w + D.N.d) D.rowAt (TwV.byVar D.N.oE xs) = _
  rw [hE, ← hx, byVar_down, hx]
  congr 2
  exact OnBytes.HonestTrace.Look.ext_rows D.N.w D.N.d (fun r => D.al - 1 - D.N.tab r) xs.reverse
    (by rw [List.length_reverse, hx])

#print axioms ProofFile.Honest.K3.Law.Spec.endTerm_tie0
#print axioms ProofFile.Honest.K3.Law.Spec.endTerm_tie
#print axioms ProofFile.Honest.K3.Law.Spec.endTerm_level
#print axioms ProofFile.Honest.K3.Law.Spec.endTerm_bits
#print axioms ProofFile.Honest.K3.Law.Spec.orderOk_of_perm
#print axioms ProofFile.Honest.K3.Law.Spec.byBit_behind
#print axioms ProofFile.Honest.K3.Law.Spec.byVar_down
#print axioms ProofFile.Honest.K3.Law.Spec.line_key
#print axioms ProofFile.Honest.K3.Law.Spec.line_tab
#print axioms ProofFile.Honest.K3.Law.Spec.key_top
#print axioms ProofFile.Honest.K3.Law.Spec.tab_root
#print axioms ProofFile.Honest.K3.Law.Spec.G_one
#print axioms ProofFile.Honest.K3.Law.Spec.Pc_top
#print axioms ProofFile.Honest.K3.Law.Spec.leaves_fin

end ProofFile.Honest.K3.Law.Spec
