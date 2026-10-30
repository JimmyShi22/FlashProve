-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByTies.lean: proof of `Spec.ties_of` (RunBySpecTop.lean). The
prover's random values (`TestCoins`) are indexed in two ways: `sortedOf` (RunOf.lean) groups them by
use, as words, for `runBy`; `coinsOf` (Coins.lean) gives them as field elements to `testAll`. If the
stages pass `okFrom` (RunBy.lean), each value of the first is the matching value of the second,
encoded (`CoinTies`, `HideTie`, RunBySpec.lean).

  `tiesBy_of`    the proof of `Spec.ties_of`
  `numbered`     the 2 k + 1 coefficients of a hiding polynomial, encoded, under the numbers that
                 `hideOf` (Fmt/M1Own.lean) asks for. It repeats the formula of `sortedOf`'s field
                 `hide`; `hide_sorted` proves that the two are equal

By what. Both indexings are unfolded at each of the seven clauses of `CoinTie`. For the hiding
polynomial, `coefU_numbered` shows that `numbered` decodes to `hideAt` (Coins.lean).

Limits.
- The theorem compares two ways to index the same random values. It says nothing on how a value is
  sampled or on how many there are. The equations hold for all row and entry numbers, also beyond a
  stage's counts: there both sides read the next range's values.
- Hypothesis: `okFrom s rest`. Of it the proof uses h ≤ k at each stage that has a fold, and the
  second clause of `switchFitB` at each switch (for the pad alone).
- Nothing on the tails of the first fold's fresh table (`TestCoins.tails`) or on `TestCoins.mem`.
- Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunBySpecTop
import Johnson.Desc.ProofFile.Honest.K12.RunByTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE toE toE_ofE)
open Johnson.Prover.Link (coefNamed coefU okE_ofE)
open Fmt.M1 (Stage)
open H2K.Pub (sgOf)
open Cb (HIdx sVars)

/-! ## 1 Lemmas on `List.drop` -/

theorem getD_of_drop {α : Type} : ∀ (S : List α) (j : ℕ) (a : α) (l : List α) (d : α),
    S.drop j = a :: l → S.getD j d = a
  | [], j, a, l, _, h => by
    rw [List.drop_nil] at h
    cases h
  | x :: S, 0, a, l, _, h => by
    have h' : x :: S = a :: l := h
    cases h'
    rfl
  | _ :: S, j + 1, a, l, d, h => getD_of_drop S j a l d h

theorem drop_succ_of {α : Type} : ∀ (S : List α) (j : ℕ) (a : α) (l : List α),
    S.drop j = a :: l → S.drop (j + 1) = l
  | [], j, a, l, h => by
    rw [List.drop_nil] at h
    cases h
  | x :: S, 0, a, l, h => by
    have h' : x :: S = a :: l := h
    cases h'
    rfl
  | _ :: S, j + 1, a, l, h => drop_succ_of S j a l h

theorem length_of_drop {α : Type} (S : List α) (j : ℕ) (a : α) (l : List α)
    (h : S.drop j = a :: l) : S.length = j + 1 + l.length := by
  have e := congrArg List.length h
  rw [List.length_drop, List.length_cons] at e
  omega

/-- Stage j + 1, counted from 0, is the last of S exactly if no stage follows it. -/
theorem lastB {α : Type} (S : List α) (j : ℕ) (rest : List α)
    (h : S.length = j + 2 + rest.length) : (j + 2 == S.length) = rest.isEmpty := by
  cases rest with
  | nil =>
    have h' : S.length = j + 2 := h
    rw [h']
    exact beq_self_eq_true _
  | cons x r =>
    rw [List.length_cons] at h
    exact beq_eq_false_iff_ne.2 (by omega)

/-! ## 2 What is used of `okFrom` -/

theorem okFrom_cons (s n : Stage) (rest : List Stage) (h : okFrom s (n :: rest) = true) :
    s.h ≤ s.k ∧ 2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ 2 ^ n.h * n.Z.l ∧ okFrom n rest = true := by
  simp only [okFrom, switchFitB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.2.1.1.1.2, h.2⟩

/-! ## 3 The hiding polynomial's coefficients -/

theorem byName_apply : ∀ (k : ℕ) (w : ℕ → ℕ → GE) (w0 : GE) (i : HIdx (sVars GE 2 k)),
    byName k w w0 i = coefNamed k (fun l t => w (l + 1) (t + 1)) w0 i
  | 0, _, _, _ => rfl
  | _ + 1, _, _, .inl _ => rfl
  | k + 1, w, w0, .inr i => byName_apply k (fun l t => w (l + 1) t) w0 i

theorem coefNamed_congr : ∀ (k : ℕ) (a a' : ℕ → ℕ → GE) (c : GE) (i : HIdx (sVars GE 2 k)),
    (∀ l t, l < k → t < 2 → a l t = a' l t) → coefNamed k a c i = coefNamed k a' c i
  | 0, _, _, _, _, _ => rfl
  | k + 1, _, _, _, .inl t, h => h 0 t.val (Nat.succ_pos k) t.isLt
  | k + 1, a, a', c, .inr i, h =>
    coefNamed_congr k (fun l => a (l + 1)) (fun l => a' (l + 1)) c i
      fun l t hl ht => h (l + 1) t (Nat.succ_lt_succ hl) ht

/-- The 2 k + 1 values c, in the hiding polynomial's own order, encoded and renumbered. Number 0 is
the constant; number 2 l + t is the coefficient of variable l (counted from 1) at degree t. -/
def numbered (k : ℕ) (c : ℕ → GE) (n : ℕ) : Fmt.M1.E :=
  if n = 0 then ofE (c (2 * (k - 1)))
  else if (n - 1) / 2 < k then ofE (c (2 * ((n - 1) / 2 - 1) + (n - 2 * ((n - 1) / 2) - 1)))
  else ofE (c (2 * (k - 1) + (n - 2 * ((n - 1) / 2))))

theorem numbered_at (k : ℕ) (c : ℕ → GE) (l t : ℕ) (ht : t < 2) :
    toE (numbered k c (2 * (l + 1) + (t + 1))) =
      c (if l + 1 < k then 2 * (l + 1 - 1) + (t + 1 - 1) else 2 * (k - 1) + (t + 1)) := by
  have hn : ¬ (2 * (l + 1) + (t + 1) = 0) := by omega
  have hd : (2 * (l + 1) + (t + 1) - 1) / 2 = l + 1 := by omega
  unfold numbered
  rw [if_neg hn, hd]
  by_cases h : l + 1 < k
  · rw [if_pos h, if_pos h, toE_ofE]
    exact congrArg c (by omega)
  · rw [if_neg h, if_neg h, toE_ofE]
    exact congrArg c (by omega)

theorem okE_numbered (k : ℕ) (c : ℕ → GE) (n : ℕ) :
    Fmt.Fld.two.okE (numbered k c n) = true := by
  unfold numbered
  split_ifs <;> exact okE_ofE _

theorem coefU_numbered (k : ℕ) (c : ℕ → GE) :
    coefU k ⟨fun l t => numbered k c (2 * l + t), numbered k c 0⟩ = hideAt k c := by
  funext i
  have h0 : toE (numbered k c 0) = c (2 * (k - 1)) := by
    unfold numbered
    rw [if_pos rfl, toE_ofE]
  unfold hideAt
  rw [byName_apply]
  show coefNamed k (fun l t => toE (numbered k c (2 * (l + 1) + (t + 1))))
      (toE (numbered k c 0)) i =
    coefNamed k (fun l t => c (if l + 1 < k then 2 * (l + 1 - 1) + (t + 1 - 1)
      else 2 * (k - 1) + (t + 1))) (c (2 * (k - 1))) i
  rw [h0]
  exact coefNamed_congr k _ _ _ i fun l t _ ht => numbered_at k c l t ht

/-- `(sortedOf S C).hide i` is `numbered k c`. i counts the stages from 1: it means entry i - 1 of
S. k: that stage's number of variables. c: its random values. -/
theorem hide_sorted (S : List Stage) (C : TestCoins) (i n k : ℕ) (c : ℕ → GE)
    (hk : (S.getD (i - 1) default).k = k)
    (hc : ∀ x, (if i = 1 then ofE (C.hide x)
      else ofE (C.rest ((marksAt S (i - 2)).ride + x))) = ofE (c x)) :
    (sortedOf S C).hide i n = numbered k c n := by
  simp only [sortedOf, numbered, hk, hc]

/-- If both read the coefficients c (hH, hW), `HideTie` holds between `sortedOf` and `coinsOf` at
stage i. -/
theorem hideTie_of (S : List Stage) (C : TestCoins) (i : ℕ) (s : Stage) (c : ℕ → GE)
    (hk : s.h ≤ s.k) (hH : ∀ n, (sortedOf S C).hide (i + 1) n = numbered s.k c n)
    (hW : (coinsOf S C.hide C.rest).W (sgOf s) i = hideAt ((sgOf s).h + (sgOf s).g) c) :
    HideTie (sortedOf S C) (coinsOf S C.hide C.rest) i s := by
  unfold HideTie
  refine ⟨?_, fun n => ?_⟩
  · have e : hideBy (sortedOf S C) (i + 1) =
        ⟨fun l t => numbered ((sgOf s).h + (sgOf s).g) c (2 * l + t),
          numbered ((sgOf s).h + (sgOf s).g) c 0⟩ := by
      rw [sg_k hk]
      show (⟨fun l t => (sortedOf S C).hide (i + 1) (2 * l + t),
        (sortedOf S C).hide (i + 1) 0⟩ : Fmt.M1.FoldOwn.Hide) = _
      simp only [hH]
    rw [hW, e, coefU_numbered]
  · rw [hH]
    exact okE_numbered _ _ _

/-! ## 4 `CoinTie` at a switch -/

/-- `CoinTie` holds between `sortedOf` and `coinsOf` at switch j. -/
theorem tie_at (S : List Stage) (C : TestCoins) (j : ℕ) (cur next : Stage) (rest : List Stage)
    (hd : S.drop j = cur :: next :: rest)
    (hfit : 2 * cur.Z.l + cur.C.r + 2 * cur.Z.r + 1 ≤ 2 ^ next.h * next.Z.l)
    (hok : okFrom next rest = true) :
    CoinTie (sortedOf S C) (coinsOf S C.hide C.rest) j cur next rest.isEmpty := by
  have hcur : S.getD j default = cur := getD_of_drop S j cur _ default hd
  have hnext : S.getD (j + 1) default = next :=
    getD_of_drop S (j + 1) next rest default (drop_succ_of S j cur _ hd)
  have hlast : (j + 2 == S.length) = rest.isEmpty := by
    refine lastB S j rest ?_
    rw [length_of_drop S j cur _ hd, List.length_cons]
    omega
  have e1 : j + 2 - 1 = j + 1 := by omega
  have e2 : j + 2 - 2 = j := by omega
  have h21 : ¬ (j + 2 = 1) := by omega
  refine ⟨fun b q => ?_, fun b q => ?_, fun n => ?_, ?_, fun hl b q => ?_, fun hl => ?_,
    fun hl n => ?_⟩
  · simp only [sortedOf, coinsOf, e1, e2]
  · simp only [sortedOf, coinsOf, e1, e2]
  · simp only [sortedOf, coinsOf, e2, hcur, carriedIn, Nat.add_sub_cancel_left]
  · simp only [sortedOf, coinsOf, e1, e2, hcur, hnext, freeRoom, carriedIn]
    refine congrArg (fun x => ofE (C.rest x)) ?_
    generalize 2 ^ next.h * next.Z.l = X at hfit ⊢
    omega
  · rw [hl] at hlast
    simp only [sortedOf, coinsOf, e1, e2, if_neg h21, hlast, Bool.false_eq_true, if_false]
  · cases rest with
    | nil => cases hl
    | cons x r =>
      refine hideTie_of S C (j + 1) next (fun n => C.rest ((marksAt S j).ride + n))
        (okFrom_cons next x r hok).1 (fun n => hide_sorted S C _ n _ _ ?_ fun y => ?_) ?_
      · rw [(by omega : j + 1 + 1 - 1 = j + 1), hnext]
      · rw [if_neg (by omega : ¬ (j + 1 + 1 = 1)), (by omega : j + 1 + 1 - 2 = j)]
      · simp only [coinsOf, if_neg (by omega : ¬ (j + 1 = 0)), Nat.add_sub_cancel]
  · rw [hl] at hlast
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [sortedOf, coinsOf, e1, e2, hlast, if_true]

/-! ## 5 Along the stages -/

theorem ties_from (S : List Stage) (C : TestCoins) : ∀ (rest : List Stage) (j : ℕ) (cur : Stage),
    S.drop j = cur :: rest → okFrom cur rest = true →
    CoinTies (sortedOf S C) (coinsOf S C.hide C.rest) j cur rest
  | [], _, _, _, _ => True.intro
  | next :: rest, j, cur, hd, hok =>
    And.intro
      (tie_at S C j cur next rest hd (okFrom_cons cur next rest hok).2.1
        (okFrom_cons cur next rest hok).2.2)
      (ties_from S C rest (j + 1) next (drop_succ_of S j cur _ hd)
        (okFrom_cons cur next rest hok).2.2)

theorem tiesBy_of : Spec.ties_of := by
  intro s rest C h
  refine ⟨ties_from (s :: rest) C rest 0 s rfl h, fun hr => ?_⟩
  cases rest with
  | nil => exact absurd rfl hr
  | cons n r =>
    refine hideTie_of (s :: n :: r) C 0 s C.hide (okFrom_cons s n r h).1
      (fun x => hide_sorted _ C _ x _ _ rfl fun _ => if_pos rfl) ?_
    simp only [coinsOf, if_true]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.getD_of_drop
#print axioms ProofFile.Honest.K12.Light.drop_succ_of
#print axioms ProofFile.Honest.K12.Light.length_of_drop
#print axioms ProofFile.Honest.K12.Light.lastB
#print axioms ProofFile.Honest.K12.Light.okFrom_cons
#print axioms ProofFile.Honest.K12.Light.byName_apply
#print axioms ProofFile.Honest.K12.Light.coefNamed_congr
#print axioms ProofFile.Honest.K12.Light.numbered_at
#print axioms ProofFile.Honest.K12.Light.okE_numbered
#print axioms ProofFile.Honest.K12.Light.coefU_numbered
#print axioms ProofFile.Honest.K12.Light.hide_sorted
#print axioms ProofFile.Honest.K12.Light.hideTie_of
#print axioms ProofFile.Honest.K12.Light.tie_at
#print axioms ProofFile.Honest.K12.Light.ties_from
#print axioms ProofFile.Honest.K12.Light.tiesBy_of
#print axioms ProofFile.Honest.K12.Light.numbered
