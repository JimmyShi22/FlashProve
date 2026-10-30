-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/ShapeFCaps.lean: what the success of `HTailF2.shapeF` (OnBytes/Model/Tail.lean),
the routine that sets the shapes of a sub-proof's smallness test from a list of matrices, says of
the numbers of that list.

 - `piecesF_mats`: `HTailF2.piecesF`, the routine's last act, keeps the list of matrices and tau.
 - `shapeF_caps`: if `tl.shapeF m txOf f hasU tau` returns tl', then tl'.mats is m; m has fewer than
   256 matrices (the routine's test "plan-link"); each has at most `kcap` columns (its test
   "hid-k-range", in the third loop); and tl'.tau is tl.tau.
 - `foldColumns_le`: so `tl'.foldColumns`, the sum of the matrices' columns, is at most 255 * kcap.
 - `small_cap`: so `tl'.foldColumns * 276 ≤ 2 ^ 45`: the form in which a law on the planner's
   routine `planRng` asks it (its comment says what the two numbers are).

The walk through the routine follows `Fo.shapeF_ix` (OnBytes/Tie/Pv/Lookup/Ends/FoShapeF.lean),
which unfolds the same text; the three small tools in front (`ok_bind'`,
`ok_jp'`, `forIn_keepsE`) are private there and are stated here once more, private again.

Not claimed. That a link's smallness test is made by this routine. That a round's draw fits. Nothing
on soundness. The program does not import this file.


-/
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model

open HTailF2

private theorem ok_bind' {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ok_jp' {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

private theorem forIn_keepsE {α σ : Type} (f : α → σ → Except String (ForInStep σ)) (l0 : List α)
    (I : List α → σ → Prop)
    (step : ∀ pre a rest, l0 = pre ++ a :: rest → ∀ s s', I pre s → f a s = .ok s' →
      ∃ t, s' = .yield t ∧ I (pre ++ [a]) t) :
    ∀ (l pre : List α) (s r : σ), l0 = pre ++ l → I pre s → forIn l s f = .ok r → I l0 r
  | [], pre, s, r, e, hI, h => by
    rw [List.forIn_nil] at h
    have hr : s = r := Except.ok.inj h
    rw [e, List.append_nil, ← hr]
    exact hI
  | a :: l, pre, s, r, e, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := ok_bind' h
    obtain ⟨t, rfl, hI'⟩ := step pre a l e s s' hI hs
    exact forIn_keepsE f l0 I step l (pre ++ [a]) t r (by rw [e]; simp) hI' h

/-- The routine's last act keeps the list of matrices and tau. -/
theorem piecesF_mats {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    tl'.mats = tl.mats ∧ tl'.tau = tl.tau := by
  unfold piecesF at h
  obtain ⟨bz, _, h⟩ := ok_bind' h
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨f9, _, h⟩ := ok_bind' h
  obtain ⟨pub, _, h⟩ := ok_bind' h
  obtain ⟨_, _, h⟩ := ok_bind' h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl⟩

/-- **What the routine's success says of the list of matrices.** -/
theorem shapeF_caps {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.mats = m ∧ m.size < 256 ∧ (∀ mu < m.size, (m.getD mu {}).k ≤ kcap) ∧
      tl'.tau = tl.tau := by
  unfold shapeF at h
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨r1, _, h⟩ := ok_bind' h
  obtain ⟨kTX, pkMat, pxMat⟩ := r1
  obtain ⟨hN, h⟩ := ok_jp' h
  obtain ⟨r2, _, h⟩ := ok_bind' h
  obtain ⟨U, count⟩ := r2
  obtain ⟨r3, h3, h⟩ := ok_bind' h
  obtain ⟨gtTree, mz, nPK, nextF, off, plFor, plOwn⟩ := r3
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨_, h⟩ := ok_jp' h
  obtain ⟨e1, e2⟩ := piecesF_mats h
  refine ⟨e1, Nat.lt_of_not_le hN, ?_, e2⟩
  clear h e1 e2
  -- the third loop: each matrix that it has passed has at most kcap columns
  have K3 := forIn_keepsE _ (List.range m.size)
    (fun pre (_ : MProd (Array Nat) (MProd Nat (MProd Nat (MProd Nat (MProd (Array Nat)
        (MProd (Array PlaceF) (Array PlaceF))))))) =>
      ∀ mu ∈ pre, (m.getD mu {}).k ≤ kcap)
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨gt, mz', nPK', nextF', off', plFor', plOwn'⟩ := s
      dsimp only at hs
      obtain ⟨_, hs⟩ := ok_jp' hs
      obtain ⟨hk, hs⟩ := ok_jp' hs
      have hle : (m.getD a {}).k ≤ kcap :=
        Nat.le_of_not_lt fun hc => hk (by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr hc)
      have keep : ∀ mu ∈ pre ++ [a], (m.getD mu {}).k ≤ kcap := fun mu hmu => by
        rcases List.mem_append.1 hmu with hm | hm
        · exact hI mu hm
        · have : mu = a := by simpa using hm
          rw [this]
          exact hle
      split at hs
      · split at hs
        · exact ⟨_, (Except.ok.inj hs).symm, keep⟩
        · exact ⟨_, (Except.ok.inj hs).symm, keep⟩
      · split at hs
        · split at hs
          · simp only [pure_bind] at hs
            split at hs
            · split at hs
              · cases hs
              · split at hs
                · cases hs
                · exact ⟨_, (Except.ok.inj hs).symm, keep⟩
            · cases hs
          · cases hs
        · cases hs)
    (List.range m.size) [] _ _ rfl (fun _ h => by cases h) h3
  exact fun mu hmu => K3 mu (List.mem_range.2 hmu)

private theorem foldl_le (c : Nat) : ∀ (l : List TMat) (s : Nat), (∀ M ∈ l, M.k ≤ c) →
    l.foldl (fun s M => s + M.k) s ≤ s + l.length * c
  | [], s, _ => by simp
  | M :: l, s, h => by
    have h1 := foldl_le c l (s + M.k) fun N hN => h N (List.mem_cons_of_mem _ hN)
    have h2 := h M (List.mem_cons_self ..)
    rw [List.foldl_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **The sum of the matrices' columns.** -/
theorem foldColumns_le {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') : tl'.foldColumns ≤ 255 * kcap := by
  obtain ⟨e, hN, hk, _⟩ := shapeF_caps h
  unfold foldColumns
  rw [e, ← Array.foldl_toList]
  have hm : ∀ M ∈ m.toList, M.k ≤ kcap := fun M hM => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hM
    have hi' : i < m.size := by simpa using hi
    have := hk i hi'
    simpa [Array.getD, hi'] using this
  have h1 := foldl_le kcap m.toList 0 hm
  have h2 : m.toList.length * kcap ≤ 255 * kcap :=
    Nat.mul_le_mul_right _ (by rw [Array.length_toList]; omega)
  omega

/-- `tl'.foldColumns * 276 ≤ 2 ^ 45`: the form in which the law on `planRng` asks it (`keeps_rng`,
OnBytes/Params/Fit/FitSmall.lean). 276 bounds the combinations of a smallness test where the target
is at most 256 and clog2 of the instances at most 20; 2 ^ 45 is the cap of `Small`
(OnBytes/Params/Fit/FitCalc.lean) on the matrix entries that a round draws. The product is at most
255 * 8191 * 276, below 2 ^ 30. That a round's draw fits is not said here. -/
theorem small_cap {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl.shapeF m txOf f hasU tau = .ok tl') : tl'.foldColumns * 276 ≤ 2 ^ 45 :=
  Nat.le_trans (Nat.mul_le_mul_right _ (foldColumns_le h)) (by decide)

end OnBytes.Model

#print axioms OnBytes.Model.shapeF_caps
#print axioms OnBytes.Model.foldColumns_le
#print axioms OnBytes.Model.small_cap
