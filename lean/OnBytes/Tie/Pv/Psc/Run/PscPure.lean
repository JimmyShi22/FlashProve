-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscPure.lean: laws on the block's Psc.run without a context or a state: its
test and what it hands on as named terms, the length of the walk, and slots in a row.

Psc.run is that of OnBytes/Iop/Psc.lean.

Main names:
  `testsW`, `outW`, `run_eqW`: run's test and what run hands on, as terms of their own; run is
    "if the test holds, then some of that term", by rfl.
  `tests_of_sizes`, `run_of_sizes`: for a sumcheck with end values, fitting sizes make the test
    true, so run gives outW.
  `walk_length`: hidingWalk has hidingEntries coefficients.
  `freshOf`, `freshOf_length`, `freshOf_get`, `freshOf_drop`: n slots in a row of one oracle's mask
    row.
Limits: no value is read: the hypotheses are on sizes alone. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscWhole

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight claimAfter polyAt hidingWalk hidingEntries varsOf masksOf formOK)

/-- The test of Psc.run. -/
def testsW (c : OnBytes.Psc.Claim) (S : OnBytes.Psc.Summand) (fresh : List Slot) (h :
    OnBytes.Psc.Heard) :
    Bool :=
  formOK c S && fresh.length == masksOf c S && h.rounds.length == (varsOf c S).length &&
    h.values.length == S.shown &&
    (S.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).length == 1 + S.kept &&
    (((varsOf c S).zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d)

/-- What Psc.run hands on. -/
def outW (c : OnBytes.Psc.Claim) (S : OnBytes.Psc.Summand) (fresh : List Slot) (h :
    OnBytes.Psc.Heard) :
    OnBytes.Psc.Out :=
  let vars := varsOf c S
  let challenges := h.rounds.map (·.2)
  let point := challenges.take c.vars.length
  let a := S.coeffs point h.values
  let hw := hidingWalk (vars.zip challenges)
  let last := claimAfter vars h.rounds (addE h.mu (mulE h.eps c.target))
  let beta := if S.shown == 0 then none else challenges.getLast?
  { point := point
    rowMasks := fresh.zip hw.1 ++ OnBytes.Psc.scaleForm (mulE h.eps hw.2) c.masks
    rowMaps := (a.drop 1).map fun x => mulE h.eps x
    rowTarget := subE last (mulE h.eps (a.headD zeroE))
    ends := ((fresh.drop hw.1.length).zip h.values).map fun p =>
      ⟨point, [(p.1, beta.getD zeroE)], p.2⟩
    eps := h.eps
    beta := beta }

theorem run_eqW (c : OnBytes.Psc.Claim) (S : OnBytes.Psc.Summand) (fresh : List Slot)
    (h : OnBytes.Psc.Heard) :
    OnBytes.Psc.run c S fresh h = if testsW c S fresh h then some (outW c S fresh h) else none :=
        rfl

/-- Fitting sizes make run's test true: a sumcheck with end values. No value is read. -/
theorem tests_of_sizes (ws : List Weight) (m : MaskForm) (τ : E) (S : OnBytes.Psc.Summand)
    (fresh : List Slot) (mu eps beta : E) (rs : List (List E × E)) (sentY v : List E)
    (len : rs.length = ws.length) (sizes : ∀ x ∈ ws.zip rs, x.2.1.length + 1 = x.1.d)
    (fits : ∀ w ∈ ws, w.fits = true) (hY : sentY.length = S.degree) (hv : v.length = S.shown)
    (d1 : 1 ≤ S.degree) (n1 : 1 ≤ S.shown) (hf : fresh.length = masksOf ⟨ws, m, τ⟩ S)
    (ha : (S.coeffs (rs.map (·.2)) v).length = 1 + S.kept) :
    testsW ⟨ws, m, τ⟩ S fresh (heardOf mu eps rs sentY beta v) = true := by
  have hs0 : (S.shown == 0) = false := by
    cases hh : S.shown with
    | zero => omega
    | succ k => rfl
  have hd0 : (S.degree == 0) = false := by
    cases hh : S.degree with
    | zero => omega
    | succ k => rfl
  have hvars : varsOf ⟨ws, m, τ⟩ S = ws ++ [Weight.atZero (S.degree + 1)] := by
    simp [varsOf, hs0]
  have htake : ((rs ++ [(sentY, beta)]).map (·.2)).take ws.length = rs.map (·.2) := by
    rw [List.map_append, List.take_append_of_le_length (by simp [len]),
        List.take_of_length_le (by simp [len])]
  unfold testsW
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, heardOf, hvars, htake]
  refine ⟨⟨⟨⟨⟨?_, hf⟩, by simp [len]⟩, hv⟩, ha⟩, ?_⟩
  · simp only [formOK, hs0, hd0, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq]
    exact ⟨⟨rfl, Or.inl (by omega)⟩, fits⟩
  · intro x hx
    rw [List.zip_append len.symm] at hx
    simp only [List.mem_append, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact sizes x hx
    · show sentY.length + 1 = S.degree + 1
      rw [hY]

theorem run_of_sizes (ws : List Weight) (m : MaskForm) (τ : E) (S : OnBytes.Psc.Summand)
    (fresh : List Slot) (mu eps beta : E) (rs : List (List E × E)) (sentY v : List E)
    (len : rs.length = ws.length) (sizes : ∀ x ∈ ws.zip rs, x.2.1.length + 1 = x.1.d)
    (fits : ∀ w ∈ ws, w.fits = true) (hY : sentY.length = S.degree) (hv : v.length = S.shown)
    (d1 : 1 ≤ S.degree) (n1 : 1 ≤ S.shown) (hf : fresh.length = masksOf ⟨ws, m, τ⟩ S)
    (ha : (S.coeffs (rs.map (·.2)) v).length = 1 + S.kept) :
    OnBytes.Psc.run ⟨ws, m, τ⟩ S fresh (heardOf mu eps rs sentY beta v) =
      some (outW ⟨ws, m, τ⟩ S fresh (heardOf mu eps rs sentY beta v)) := by
  rw [run_eqW, tests_of_sizes ws m τ S fresh mu eps beta rs sentY v len sizes fits hY hv d1 n1 hf
      ha]
  rfl

/-! ## The length of the hiding walk -/

theorem powersLoop_length (x : E) : ∀ (n : Nat) (c : E) (done : List E),
    (OnBytes.Psc.powersLoop x n c done).length = done.length + n
  | 0, _, done => by simp [OnBytes.Psc.powersLoop]
  | n + 1, c, done => by
    simp only [OnBytes.Psc.powersLoop]
    rw [powersLoop_length x n]
    simp only [List.length_cons]
    omega

theorem powers_length (c x : E) (n : Nat) : (OnBytes.Psc.powers c x n).length = n := by
  unfold OnBytes.Psc.powers
  rw [powersLoop_length]
  simp

/-- The hiding walk has as many coefficients as the hiding polynomial has entries. -/
theorem walk_length : ∀ (ws : List Weight) (γ : List E), ws ≠ [] → ws.length = γ.length →
    (∀ w ∈ ws, 1 ≤ w.d) → (hidingWalk (ws.zip γ)).1.length = hidingEntries ws
  | [], _, h, _, _ => absurd rfl h
  | [w], [g], _, _, hd => by
    show (OnBytes.Psc.powers oneE g w.d).length = 1 + ((w.d - 1) + 0)
    have := hd w List.mem_cons_self
    rw [powers_length]
    omega
  | [_], [], _, h, _ => by simp at h
  | [_], _ :: _ :: _, _, h, _ => by simp at h
  | _ :: _ :: _, [], _, h, _ => by simp at h
  | _ :: _ :: _, [_], _, h, _ => by simp at h
  | w :: w' :: ws, g :: g' :: γ, _, h, hd => by
    show (OnBytes.Psc.powers _ g (w.d - 1) ++ (hidingWalk ((w' :: ws).zip (g' :: γ))).1).length =
      1 + ((w.d - 1) + ((w' :: ws).map fun w => w.d - 1).sum)
    rw [List.length_append, powers_length,
      walk_length (w' :: ws) (g' :: γ) (List.cons_ne_nil _ _) (Nat.succ.inj h)
        fun v hv => hd v (List.mem_cons_of_mem _ hv)]
    unfold hidingEntries
    omega

/-! ## The run's own slots, and the end claims -/

/-- n slots in a row of the mask row of oracle orc, from first on. -/
def freshOf (orc first n : Nat) : List Slot := (List.range n).map fun i => ⟨orc, first + i⟩

theorem freshOf_length (orc first n : Nat) : (freshOf orc first n).length = n := by simp [freshOf]

theorem freshOf_get (orc first n i : Nat) (h : i < n) : (freshOf orc first n)[i]? = some ⟨orc,
    first + i⟩ := by
  simp [freshOf, h]

theorem freshOf_drop (orc first n k : Nat) :
    (freshOf orc first n).drop k = freshOf orc (first + k) (n - k) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  by_cases h : k + i < n
  · rw [freshOf_get _ _ _ _ h, freshOf_get _ _ _ _ (by omega), Nat.add_assoc]
  · have h1 : (freshOf orc first n)[k + i]? = none := by
      rw [List.getElem?_eq_none_iff, freshOf_length]; omega
    have h2 : (freshOf orc (first + k) (n - k))[i]? = none := by
      rw [List.getElem?_eq_none_iff, freshOf_length]; omega
    rw [h1, h2]

#print axioms run_of_sizes
#print axioms walk_length
#print axioms freshOf_drop

end OnBytes.Model.Road
