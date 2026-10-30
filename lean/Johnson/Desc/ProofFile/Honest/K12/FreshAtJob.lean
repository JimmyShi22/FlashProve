-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FreshAtJob.lean: at the job of the shared chain's test on G_u
(`jobAtU`, JobShared.lean), the first fresh table that "send o_u" builds and the fresh table of the
test's first state are the same table, entry by entry, if the two are built from the same values.

  `SameFresh s cs C`   the hypothesis "the same values", on numbers: the sender's value number n
                 decodes to `C.hide n` for n below 2 k + 1, and its value number
                 2 k + 1 + b * Z.r + q decodes to `C.tails b q` for b below 2 ^ h and q below Z.r
  `fresh_atU`    under `freshFitsU A p` (FitShared.lean), 2 k + 1 ≤ h + Z.l at the first stage, and
                 `SameFresh`: entry j of mask row b of the sender's message, decoded, is entry
                 `fM b j` of the test's first state, for b below 2 ^ h and j below Z.l; and entry q
                 of that row's tail, decoded, is `fT b q`, for q below Z.r
  `fresh_atU_words`   the same as equations of words: the sender's entry is the test's entry,
                 encoded, if the words of the sender's values are below the prime
  `sameFresh_of`   `SameFresh` from one list of values: `C.hide n` for n below `dueFresh s`, where
                 `C.tails` is `tailsIn s C.hide`, as it is at `restCoins` (Parts.lean)
  `freshRow_packedN`   an entry of `freshRow` (Fmt/M1Fold.lean), decoded, is the entry of `packedN`
                 (Johnson/Prover/Link/BodyPack.lean) at the decoded coefficients

By what. `freshCoef_atU`, `freshTail_atU`, `freshTest_atU` and `freshTails_atU` (FitSharedLaw.lean)
say what each side builds. `fresh_packed` and `vec_freshRows` (Johnson/Prover/Link/FoldPairs.lean)
say that the two packings put a coefficient at the same place where the rows have room.

Limits.
- On places and numbers alone. That the values are the same is the hypothesis `SameFresh`: whether
  the parts of sender and test are given the same values is up to the book, and nothing here shows
  it.
- The condition 2 k + 1 ≤ h + Z.l is a clause of `StagesOk` (RunBy.lean) and none of `freshFitsU`.
- Within the table alone: rows below 2 ^ h, entries below Z.l, tail entries below Z.r.
- Nothing on how a value is sampled. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitSharedLaw
import Johnson.Desc.ProofFile.Honest.K12.RunByNext
import Johnson.Desc.ProofFile.Honest.K12.RunByTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE Sg toE ofE readE readE_ofTriple vec Sz rowNo_testBit)
open Johnson.Prover.Link (packedN coefU coefNamed vec_freshRows fresh_packed)
open Fmt.M1 (Stage)
open Fmt.M1.FoldOwn (Hide freshRow)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K14 (SendPub jobU laid)
open H2K.Pub (sgOf)

/-! ## 1 The two packings, entry by entry -/

theorem freshRow_packed (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l) (U : Hide) (b j : ℕ)
    (hb : b < 2 ^ s.h) (hj : j < s.Z.l) :
    toE ((freshRow .two (s.h + s.g) s.h U b).getD j Fmt.Fld.zeroE) =
      packedN s (coefU (s.h + s.g) U) b j := by
  unfold packedN
  rw [dif_pos ⟨hl, hj⟩, ← fresh_packed s hl U]
  show _ = vec _ (Sz.rowNo (fun t : Fin s.h => b.testBit t.val) + 2 ^ s.h * j)
  rw [rowNo_testBit, Nat.mod_eq_of_lt hb, vec_freshRows _ _ _ _ _ _ hb hj]

/-- An entry of `freshRow`, decoded, is the entry of `packedN` at the decoded coefficients. -/
theorem freshRow_packedN (s : Stage) (hk : s.h ≤ s.k) (hroom : 2 * s.k + 1 ≤ s.h + s.Z.l)
    (U : Hide) (b j : ℕ) (hb : b < 2 ^ s.h) (hj : j < s.Z.l) :
    toE ((freshRow .two s.k s.h U b).getD j Fmt.Fld.zeroE) =
      packedN (sgOf s) (coefU ((sgOf s).h + (sgOf s).g) U) b j := by
  have hl : (sgOf s).h + 2 * (sgOf s).g + 1 ≤ (sgOf s).Z.l := by
    show s.h + 2 * (s.k - s.h) + 1 ≤ s.Z.l
    omega
  have e := congrArg (fun k => toE ((freshRow .two k s.h U b).getD j Fmt.Fld.zeroE)) (sg_k hk).symm
  exact e.trans (freshRow_packed (sgOf s) hl U b j hb hj)

/-! ## 2 The coefficients -/

theorem coefAt_lt (k l t : ℕ) (hl : l < k) (ht : t < 2) : coefAt k (l + 1) (t + 1) < 2 * k + 1 := by
  unfold coefAt
  split <;> omega

/-- The sender's record of coefficients, decoded, is `byName` at the values that they decode to. K:
the number of variables in the type; it equals k. -/
theorem coefU_byName (K k : ℕ) (hK : K = k) (cs : ℕ → OnBytes.E) (c : ℕ → GE)
    (h : ∀ n < 2 * k + 1, readE (cs n) = c n) :
    coefU K ⟨fun l t => (cs (coefAt k l t)).triple, (cs (2 * (k - 1))).triple⟩ =
      byName K (fun l t => c (coefAt k l t)) (c (2 * (k - 1))) := by
  subst hK
  funext i
  rw [byName_apply]
  have h0 : toE (cs (2 * (K - 1))).triple = c (2 * (K - 1)) := h _ (by omega)
  show coefNamed K (fun l t => toE (cs (coefAt K (l + 1) (t + 1))).triple)
    (toE (cs (2 * (K - 1))).triple) i = _
  rw [h0]
  exact coefNamed_congr K _ _ _ i fun l t hl ht => h _ (coefAt_lt K l t hl ht)

/-! ## 3 "The same values" -/

/-- The sender's values cs and the test's values C are the same, number by number, within the
counts of a fresh table of stage s. -/
def SameFresh (s : Stage) (cs : ℕ → OnBytes.E) (C : TestCoins) : Prop :=
  (∀ n < 2 * s.k + 1, readE (cs n) = C.hide n) ∧
    ∀ b < 2 ^ s.h, ∀ q < s.Z.r, readE (cs (2 * s.k + 1 + b * s.Z.r + q)) = C.tails b q

theorem sameFresh_of (s : Stage) (cs : ℕ → OnBytes.E) (C : TestCoins)
    (h : ∀ n < dueFresh s, readE (cs n) = C.hide n) (ht : C.tails = tailsIn s C.hide) :
    SameFresh s cs C := by
  refine ⟨fun n hn => h n ?_, fun b hb q hq => ?_⟩
  · unfold dueFresh
    omega
  · rw [ht]
    refine h _ ?_
    have h1 : (b + 1) * s.Z.r ≤ 2 ^ s.h * s.Z.r := Nat.mul_le_mul_right _ hb
    have h2 : (b + 1) * s.Z.r = b * s.Z.r + s.Z.r := Nat.succ_mul b s.Z.r
    unfold dueFresh
    omega

/-! ## 4 At the job -/

theorem fresh_atU {W X : Type} (A : SendPub) (p : P12) (h : freshFitsU A p = true)
    (hroom : 2 * (stage₀ p).k + 1 ≤ (stage₀ p).h + (stage₀ p).Z.l) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) (C : TestCoins) (v cs : ℕ → OnBytes.E)
    (same : SameFresh (stage₀ p) cs C) :
    (∀ b < 2 ^ (stage₀ p).h, ∀ j < (stage₀ p).Z.l,
      readE ((laid (jobU A).Q.codes (shapeAt (jobU A) 1) v cs ((jobU A).sort 1)).mask b j) =
        ((jobAtU A p door weights rand u?).toRun.toTest.first w fr C).fM b j) ∧
    ∀ b < 2 ^ (stage₀ p).h, ∀ q < (stage₀ p).Z.r,
      readE ((laid (jobU A).Q.codes (shapeAt (jobU A) 1) v cs ((jobU A).sort 1)).maskTail b q) =
        ((jobAtU A p door weights rand u?).toRun.toTest.first w fr C).fT b q := by
  have hk : (stage₀ p).h ≤ (stage₀ p).k := (freshFitsU_says A p h).2.2.2.2.2
  refine ⟨fun b hb j hj => ?_, fun b hb q hq => ?_⟩
  · rw [freshCoef_atU A p h, readE_ofTriple, freshTest_atU A p h,
      freshRow_packedN (stage₀ p) hk hroom _ b j hb hj,
      coefU_byName _ (stage₀ p).k (sg_k hk) cs C.hide same.1]
  · rw [freshTail_atU A p h, freshTails_atU]
    exact same.2 b hb q hq

/-- The same as equations of words. -/
theorem fresh_atU_words {W X : Type} (A : SendPub) (p : P12) (h : freshFitsU A p = true)
    (hroom : 2 * (stage₀ p).k + 1 ≤ (stage₀ p).h + (stage₀ p).Z.l) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) (C : TestCoins) (v cs : ℕ → OnBytes.E)
    (same : SameFresh (stage₀ p) cs C) (hok : ∀ n, Fmt.Fld.two.okE (cs n).triple = true) :
    (∀ b < 2 ^ (stage₀ p).h, ∀ j < (stage₀ p).Z.l,
      (laid (jobU A).Q.codes (shapeAt (jobU A) 1) v cs ((jobU A).sort 1)).mask b j =
        OnBytes.E.ofTriple
          (ofE (((jobAtU A p door weights rand u?).toRun.toTest.first w fr C).fM b j))) ∧
    ∀ b < 2 ^ (stage₀ p).h, ∀ q < (stage₀ p).Z.r,
      (laid (jobU A).Q.codes (shapeAt (jobU A) 1) v cs ((jobU A).sort 1)).maskTail b q =
        OnBytes.E.ofTriple
          (ofE (((jobAtU A p door weights rand u?).toRun.toTest.first w fr C).fT b q)) := by
  have H := fresh_atU A p h hroom door weights rand u? w fr C v cs same
  refine ⟨fun b hb j hj => ?_, fun b hb q hq => ?_⟩
  · have e := H.1 b hb j hj
    rw [freshCoef_atU A p h, readE_ofTriple] at e
    rw [freshCoef_atU A p h]
    exact congrArg OnBytes.E.ofTriple
      (eq_ofE (nx_ok_getD _ (nx_ok_freshRow _ (fun _ _ => hok _) (hok _) _ _ _) _) e)
  · have e := H.2 b hb q hq
    rw [freshTail_atU A p h] at e ⊢
    exact (OnBytes.E.ofTriple_triple _).symm.trans
      (congrArg OnBytes.E.ofTriple (eq_ofE (hok _) e))

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.freshRow_packed
#print axioms ProofFile.Honest.K12.Light.freshRow_packedN
#print axioms ProofFile.Honest.K12.Light.coefAt_lt
#print axioms ProofFile.Honest.K12.Light.coefU_byName
#print axioms ProofFile.Honest.K12.Light.sameFresh_of
#print axioms ProofFile.Honest.K12.Light.fresh_atU
#print axioms ProofFile.Honest.K12.Light.fresh_atU_words
#print axioms ProofFile.Honest.K12.Light.SameFresh
