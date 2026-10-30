-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByAns.lean: proof of `Spec.ans_eq` (RunBySpec.lean). After a
code switch the verifier samples a point and a factor, and the prover answers, in the round named
"CS", with one field element: a linear form of the new oracle message's entries.

Two definitions compute that answer. `stagesBy` (RunBy.lean) works on words: `lhs` of `sampleRow` at
the new stage's two tables. `aAns` (Johnson/Desc/K12/Honest/Stages.lean) works over the field: the
sum `sampleAt` (Fold.lean beside it).

  `ansBy_eq`     the proof of `Spec.ans_eq`: the first result is the second, encoded as three words
                 below the prime (`ofE`)
  `toE_orOneW`   `orOneW` (RunBy.lean: 1 in the place of a triple that decodes to 0) decodes to
                 `orOne` (Fold.lean: 1 in the place of 0)

By what. Both sides are triples of words below the prime, so it is enough that they decode to the
same field element (`eq_ofE`, RunByTab.lean). `sampleAt_ranges` and `toE_lhs_sampleRow` bring the
two sides to the same two sums over the tables' indices.

Limits.
- The verifier's state fixes how many sampled elements make up the point. If that count is not
  `next.na`, the number of coordinates that `sampleRow` is given, both sides read 0 for a missing
  coordinate and ignore a surplus one.
- If the sampled factor decodes to 0, both sides use 1 in its place.
- Two definitions give the same words. Nothing follows on what a verifier decides.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunByTab
import Johnson.Desc.K12.Law.ClaimSays
import OnBytes.Slice.SimSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open OnBytes.Slice (GE Sg ofE toE vec lst eqW idxOf readE readP toE_addE toE_zeroE toE_oneE toE_inj
  okE_zeroE readE_zero readE_ofTriple lst_nil eqW_congr toE_dot_of_le vec_sampleRow_c
  vec_sampleRow_d size_sampleRow_c size_sampleRow_d)
open Johnson.Prover.Link (PS μOf)
open Fmt.M1 (Stage sampleRow lg)
open Fmt.M1.Own (PSt tabOf lhs)
open H2K.Pub (sgOf stN_eq)

/-! ## 1 What single values decode to -/

/-- `orOneW` decodes to `orOne` of the decoded element. -/
theorem toE_orOneW (b : Fmt.M1.E) : toE (orOneW b) = orOne (toE b) := by
  unfold orOneW orOne
  by_cases h : toE b = 0
  · have e : Fld.two.addE b Fld.zeroE = Fld.zeroE :=
      toE_inj _ _ (OnBytes.Slice.okE_addE _ _) okE_zeroE
        (by rw [toE_addE, toE_zeroE, h, add_zero])
    rw [if_pos e, if_pos h, toE_oneE]
  · have e : ¬ Fld.two.addE b Fld.zeroE = Fld.zeroE := fun c => h (by
      have c' := congrArg toE c
      rwa [toE_addE, toE_zeroE, add_zero] at c')
    rw [if_neg e, if_neg h]

/-- An entry of a list of triples, converted by `E.ofTriple` and decoded by `readE`, is the entry
decoded by `toE`; both give 0 beyond the list's end. -/
theorem readE_getD_ofTriple : ∀ (l : List Fmt.M1.E) (i : ℕ),
    readE ((l.map OnBytes.E.ofTriple).getD i OnBytes.zeroE) = lst l i
  | [], i => readE_zero.trans (lst_nil i).symm
  | a :: _, 0 => readE_ofTriple a
  | _ :: l, i + 1 => readE_getD_ofTriple l i

section
variable {s : Stage} {last : Bool} {P : PS} {p : PSt}

theorem Tab.vec_main_lt (T : Tab s last P p) (i : ℕ) (hi : i < 2 ^ s.k * s.C.l) :
    vec (tabOf p.M s.C.l) i = P.tabM i := by
  have e := T.vec_main (i % 2 ^ s.k) (i / 2 ^ s.k) (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.div_lt_of_lt_mul hi)
  rwa [Nat.mod_add_div] at e

theorem Tab.vec_mask_lt (T : Tab s last P p) (i : ℕ) (hi : i < 2 ^ s.h * s.Z.l) :
    vec (tabOf p.W s.Z.l) i = P.tabZ i := by
  have e := T.vec_mask (i % 2 ^ s.h) (i / 2 ^ s.h) (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.div_lt_of_lt_mul hi)
  rwa [Nat.mod_add_div] at e

end

/-! ## 2 The two sides as the same two sums -/

/-- `sampleAt` as two sums over the indices of the two tables. eC, eZ: the two message lengths are
2 ^ eC and 2 ^ eZ. -/
theorem sampleAt_ranges (s : Sg) (eC eZ : ℕ) (hC : 2 ^ eC = s.C.l) (hZ : 2 ^ eZ = s.Z.l)
    (z : ℕ → GE) (β : GE) (P : PS) :
    sampleAt s (fun t => z t.val) β (μOf s P) =
      (∑ i ∈ Finset.range (2 ^ (s.h + s.g + eC)), eqW s.st.na z i * P.tabM i) +
        ∑ i ∈ Finset.range (2 ^ (s.h + eZ)),
          (if i + 1 = 2 ^ s.h * s.Z.l then β else eqW s.st.na z (2 ^ (s.st.na - 1) + i)) *
            P.tabZ i := by
  rw [H2K.ClaimSays.sum_table (s.h + s.g) eC s.C.l hC, H2K.ClaimSays.sum_table s.h eZ s.Z.l hZ]
  unfold sampleAt
  refine (Fintype.sum_sum_type _).trans (congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun x _ => ?_) (Finset.sum_congr rfl fun x _ => ?_))
  · show (if isPad s (Sum.inl x) = true then β else eqW s.st.na z (idxOf x)) * P.tabM (idxOf x) =
      eqW s.st.na z (idxOf x) * P.tabM (idxOf x)
    exact congrArg (· * P.tabM (idxOf x)) (if_neg Bool.false_ne_true)
  · show (if (idxOf x + 1 == 2 ^ s.h * s.Z.l) = true then β
        else eqW s.st.na z (2 ^ (s.st.na - 1) + idxOf x)) * P.tabZ (idxOf x) =
      (if idxOf x + 1 = 2 ^ s.h * s.Z.l then β
        else eqW s.st.na z (2 ^ (s.st.na - 1) + idxOf x)) * P.tabZ (idxOf x)
    simp only [beq_iff_eq]

/-- `lhs` of `sampleRow` at the two tables of words decodes to the two sums of `sampleAt_ranges`.
z: a point of `n.na` coordinates. b: the factor. -/
theorem toE_lhs_sampleRow (n : Stage) (last : Bool) (Q : PS) (q : PSt)
    (hC : 2 ^ lg n.C.l = n.C.l) (hZ : 2 ^ lg n.Z.l = n.Z.l) (T : Tab n last Q q)
    (z : List Fmt.M1.E) (hz : z.length = n.na) (b y : Fmt.M1.E) :
    toE (lhs .two (sampleRow .two n.Am n.Az z b y) (tabOf q.M n.C.l) (tabOf q.W n.Z.l)) =
      (∑ i ∈ Finset.range (2 ^ n.Am), eqW n.na (lst z) i * Q.tabM i) +
        ∑ i ∈ Finset.range (2 ^ n.Az),
          (if i + 1 = 2 ^ n.h * n.Z.l then toE b else eqW n.na (lst z) (2 ^ (n.na - 1) + i)) *
            Q.tabZ i := by
  have hna : n.na = max n.Am n.Az + 1 := rfl
  have hAm : n.Am ≤ z.length := by omega
  have hAz : n.Az ≤ z.length := by omega
  have eM : 2 ^ n.Am = 2 ^ n.k * n.C.l := by
    show 2 ^ (n.k + lg n.C.l) = _
    rw [pow_add, hC]
  have eZ : 2 ^ n.Az = 2 ^ n.h * n.Z.l := by
    show 2 ^ (n.h + lg n.Z.l) = _
    rw [pow_add, hZ]
  have hc := size_sampleRow_c .two n.Am n.Az z b y hAm
  have hd := size_sampleRow_d .two n.Am n.Az z b y hAz
  unfold lhs
  rw [toE_addE, toE_dot_of_le _ _ (2 ^ n.Am) (Nat.le_trans (Nat.min_le_left _ _) (le_of_eq hc)),
    toE_dot_of_le _ _ (2 ^ n.Az) (Nat.le_trans (Nat.min_le_left _ _) (le_of_eq hd))]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_)
    (Finset.sum_congr rfl fun i hi => ?_)
  · have hi' : i < 2 ^ n.Am := Finset.mem_range.1 hi
    rw [vec_sampleRow_c _ _ _ _ _ _ hAm, if_pos hi', T.vec_main_lt i (lt_of_lt_of_eq hi' eM)]
    rfl
  · have hi' : i < 2 ^ n.h * n.Z.l := lt_of_lt_of_eq (Finset.mem_range.1 hi) eZ
    rw [vec_sampleRow_d _ _ _ _ _ _ hAz, T.vec_mask_lt i hi', eZ]
    by_cases h1 : i + 1 = 2 ^ n.h * n.Z.l
    · have h2 : ¬ i + 1 < 2 ^ n.h * n.Z.l := fun c => Nat.ne_of_lt c h1
      rw [if_neg h2, if_pos h1, if_pos h1]
    · have h2 : i + 1 < 2 ^ n.h * n.Z.l := Nat.lt_of_le_of_ne hi' h1
      rw [if_pos h2, if_neg h1]
      rfl

/-! ## 3 The equation -/

/-- The equation for a stage given as `Sg`. n: the same stage as a `Stage`. els: the sampled
elements. bits: how many of them make up the point. -/
theorem ans_core (s : Sg) (n : Stage) (e : s.st = n) (last : Bool) (Q : PS) (q : PSt)
    (hC : pow2B n.C.l = true) (hZ : pow2B n.Z.l = true) (T : Tab n last Q q)
    (els : List Fmt.M1.E) (bits : ℕ) :
    lhs .two
        (sampleRow .two n.Am n.Az
          ((List.range n.na).map fun i => (els.take bits).getD i Fld.zeroE)
          (orOneW (els.getD bits Fld.zeroE)) Fld.zeroE)
        (tabOf q.M n.C.l) (tabOf q.W n.Z.l) =
      ofE (sampleAt s (readP _ ((els.map OnBytes.E.ofTriple).take bits))
        (orOne (readE ((els.map OnBytes.E.ofTriple).getD bits OnBytes.zeroE))) (μOf s Q)) := by
  subst e
  have hC' : 2 ^ lg s.C.l = s.C.l := (beq_iff_eq.1 hC).symm
  have hZ' : 2 ^ lg s.Z.l = s.Z.l := (beq_iff_eq.1 hZ).symm
  refine eq_ofE (OnBytes.Slice.okE_addE _ _) ?_
  have hlen : ((List.range s.st.na).map fun i => (els.take bits).getD i Fld.zeroE).length =
      s.st.na := by rw [List.length_map, List.length_range]
  have hW : ∀ i, eqW s.st.na
      (lst ((List.range s.st.na).map fun i => (els.take bits).getD i Fld.zeroE)) i =
        eqW s.st.na (lst (els.take bits)) i :=
    fun i => eqW_congr _ _ _ i fun t ht => lst_range _ _ t ht
  have hz : readP s.st.na ((els.map OnBytes.E.ofTriple).take bits) =
      fun t => lst (els.take bits) t.val := by
    funext t
    rw [← List.map_take]
    exact readE_getD_ofTriple _ _
  have hb : readE ((els.map OnBytes.E.ofTriple).getD bits OnBytes.zeroE) =
      toE (els.getD bits Fld.zeroE) := readE_getD_ofTriple _ _
  rw [hz, hb, ← toE_orOneW]
  refine (toE_lhs_sampleRow s.st last Q q hC' hZ' T _ hlen _ _).trans ?_
  simp only [hW]
  exact (sampleAt_ranges s (lg s.C.l) (lg s.Z.l) hC' hZ' (lst (els.take bits)) _ Q).symm

theorem ansBy_eq : Spec.ans_eq := by
  intro p j cur next last o D t₁ Q q hc hn hC hZ T
  unfold aAns
  simp only [sg_k hc, sg_k hn]
  exact ans_core (sgOf next) next (stN_eq hn) last Q q hC hZ T _ _

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.toE_orOneW
#print axioms ProofFile.Honest.K12.Light.readE_getD_ofTriple
#print axioms ProofFile.Honest.K12.Light.Tab.vec_main_lt
#print axioms ProofFile.Honest.K12.Light.Tab.vec_mask_lt
#print axioms ProofFile.Honest.K12.Light.sampleAt_ranges
#print axioms ProofFile.Honest.K12.Light.toE_lhs_sampleRow
#print axioms ProofFile.Honest.K12.Light.ans_core
#print axioms ProofFile.Honest.K12.Light.ansBy_eq
