-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchPads.lean: two laws on the program's pure functions that the names of a
code switch lean on: the places of a sample's pad have different indices; and the program's test on
the public sizes of a switch has the same value in front of the sending and behind it.

The program asks `switchTargetCheck` at the statement in front of the sending (`switchVerify`,
OnBytes/Iop/Cs.lean) and makes the frame (`switchFrame`) at the statement behind the sending and the
joins (`switchAdmit`). `fit_of_check` (Johnson/Top/H/SwitchMapsCheck.lean) takes one statement for
both. The test reads of a statement its codes and the shapes of the kept members alone: so it can be
carried from one statement to another that has these in common. Statements and proofs.
Main names:
  `flat_range`: a list made row by row is the list made in one go.
  `padPlaces_nodup`: no two places of a pad have one index.
  `padOf_congr`, `parts_congr`, `check_congr`: the pad of a message, the parts of the rest and the
    test on the public sizes are the same at two statements with the same codes and the same shapes
    at the kept members.
  `fit_of_check₂`: `fit_of_check` with the test at one statement and the frame at another.
Limits: that a sending and the joins leave the codes and the kept members' shapes as they were is a
premise. Nothing on soundness.

-/
import Johnson.Top.H.SwitchMapsCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

/-- A list made row by row, e entries a row, is the list made in one go. -/
theorem flat_range {α : Type} (e : ℕ) (F : ℕ → α) : ∀ a : ℕ,
    ((List.range a).flatMap fun i => (List.range e).map fun t => F (e * i + t)) =
      (List.range (e * a)).map F
  | 0 => by simp
  | a + 1 => by
    rw [List.range_succ, List.flatMap_append, flat_range e F a, Nat.mul_succ, List.range_add,
      List.map_append, List.map_map]
    simp [Function.comp_def]

theorem pad_form_nodup (part : Part) (c0 base e a rb : ℕ) (bs : ℕ → E) :
    (((List.range a).flatMap fun i => (List.range e).map fun t =>
      ({ part := part, index := c0 + (base + e * i + t) * 2 ^ rb, answer := i, basis := bs t } :
        PadPlace)).map (·.index)).Nodup := by
  have key : (((List.range a).flatMap fun i => (List.range e).map fun t =>
      ({ part := part, index := c0 + (base + e * i + t) * 2 ^ rb, answer := i, basis := bs t } :
        PadPlace)).map (·.index)) =
      (List.range a).flatMap fun i => (List.range e).map fun t =>
        (fun m => c0 + (base + m) * 2 ^ rb) (e * i + t) := by
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def, Nat.add_assoc]
  rw [key, flat_range e (fun m => c0 + (base + m) * 2 ^ rb) a]
  refine List.Nodup.map ?_ List.nodup_range
  intro m m' h
  have h1 : (base + m) * 2 ^ rb = (base + m') * 2 ^ rb := Nat.add_left_cancel h
  have h2 := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos rb) h1
  omega

theorem getD_ite_nodup (c : Prop) [Decidable c] (L : List PadPlace)
    (h : (L.map (·.index)).Nodup) :
    (((if c then none else some L : Option (List PadPlace)).getD []).map (·.index)).Nodup := by
  by_cases hc : c
  · rw [if_pos hc]
    exact List.nodup_nil
  · rw [if_neg hc]
    exact h

/-- **No two places of a pad have one index.** -/
theorem padPlaces_nodup (codes : Codes) (s : OracleShape) :
    ((padPlaces codes s).map (·.index)).Nodup := by
  unfold padPlaces Send.pad
  exact getD_ite_nodup _ _ (pad_form_nodup _ _ _ _ _ _ _)

/-! ## The test in front of the sending and behind it -/

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) : ∀ (l : List α) (b : β),
    (∀ b a, a ∈ l → f b a = g b a) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h b a (List.mem_cons_self ..)]
    exact foldl_congr_mem f g l _ fun b x hx => h b x (List.mem_cons_of_mem _ hx)

section
variable (S S' : Statement) (old : SingleRows) (hc : S'.codes = S.codes)
  (hs : ∀ o, o ∈ (switchKept old).toList →
    (S'.oracles.getD o default).shape = (S.oracles.getD o default).shape)
include hc hs

theorem padOf_congr (o : ℕ) (ho : o ∈ (switchKept old).toList) : padOf S' o = padOf S o := by
  unfold padOf
  rw [hc, hs o ho]

theorem parts_congr : switchParts S' old = switchParts S old := by
  have e : ∀ init : Array ℕ × ℕ,
      (switchKept old).foldl
        (fun (s : Array ℕ × ℕ) o => (s.1.push s.2, s.2 + (padOf S' o).length)) init =
      (switchKept old).foldl
        (fun (s : Array ℕ × ℕ) o => (s.1.push s.2, s.2 + (padOf S o).length)) init := by
    intro init
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    exact foldl_congr_mem _ _ _ _ fun b a ha => by rw [padOf_congr S S' old hc hs a ha]
  unfold switchParts
  simp only [hc, e]

/-- **The test on the public sizes has the same value at both statements.** -/
theorem check_congr (T : SwitchTarget) :
    switchTargetCheck S' old T = switchTargetCheck S old T := by
  have e : ((switchKept old).zip T.kept).all (fun p =>
        let o := (S'.oracles.getD p.1 default).shape
        let n := p.2.shape
        o.maskRows == 0 && n.maskRows == 0 && decide (n.code < S.codes.base.size) &&
          (Send.pad S.codes o).isSome &&
          n.mainRows == o.mainRows && n.mainDeg == o.mainDeg && n.answers == o.answers &&
          (S.codes.base.getD n.code default).ell == (S.codes.base.getD o.code default).ell) =
      ((switchKept old).zip T.kept).all (fun p =>
        let o := (S.oracles.getD p.1 default).shape
        let n := p.2.shape
        o.maskRows == 0 && n.maskRows == 0 && decide (n.code < S.codes.base.size) &&
          (Send.pad S.codes o).isSome &&
          n.mainRows == o.mainRows && n.mainDeg == o.mainDeg && n.answers == o.answers &&
          (S.codes.base.getD n.code default).ell == (S.codes.base.getD o.code default).ell) := by
    rw [Bool.eq_iff_iff, Array.all_eq_true, Array.all_eq_true]
    have hm : ∀ i (hi : i < ((switchKept old).zip T.kept).size),
        (S'.oracles.getD ((switchKept old).zip T.kept)[i].1 default).shape =
          (S.oracles.getD ((switchKept old).zip T.kept)[i].1 default).shape := by
      intro i hi
      have h1 : i < (switchKept old).size := by
        rw [Array.size_zip] at hi
        omega
      rw [Array.getElem_zip]
      exact hs _ (by simp)
    constructor
    · intro h i hi
      have := h i hi
      simp only [hm i hi] at this
      exact this
    · intro h i hi
      simp only [hm i hi]
      exact h i hi
  unfold switchTargetCheck
  simp only [hc, parts_congr S S' old hc hs, e]

end

/-- **`fit_of_check` with the test in front of the sending (S₀) and the frame behind it (S).** -/
theorem fit_of_check₂ (S₀ S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (anew : Array ℕ) (W : SwitchFrame) (hW : switchFrame S old T g anew = some W)
    (hc : switchTargetCheck S₀ old T = true) (hcodes : S.codes = S₀.codes)
    (hshapes : ∀ o, o ∈ (switchKept old).toList →
      (S.oracles.getD o default).shape = (S₀.oracles.getD o default).shape)
    (l : List (OracleShape × ℕ)) (g0 : 0 < l.length) (hg : (l.get ⟨0, g0⟩).1 = T.shape)
    (hk : ∀ i (hi : i < T.kept.size), ∃ h : 1 + i < l.length,
      (l.get ⟨1 + i, h⟩).1 = T.kept[i].shape)
    (s : Sg) (hC : s.C = codeOf W.code) (hZ : s.Z = codeOf W.zk)
    {K : Type} (mem row : K → ℕ) (pl : K → KeptPlace)
    (hpl : ∀ k, W.kept[mem k]? = some (pl k)) (hrow : ∀ k, row k < (pl k).rows)
    (hkr : old.keptRows = (W.kept.map (·.rows)).sum)
    (hcode : ∀ k, W.code.ell ≤
      (S.codes.base.getD (S.oracles.getD (pl k).old default).shape.code default).ell) :
    Fit S.codes l s W mem row pl :=
  fit_of_check S old T g anew W hW ((check_congr S₀ S old hcodes hshapes T).trans hc) l g0 hg hk s
    hC hZ mem row pl hpl hrow hkr hcode

end Johnson.Top.H

#print axioms Johnson.Top.H.padPlaces_nodup
#print axioms Johnson.Top.H.parts_congr
#print axioms Johnson.Top.H.check_congr
#print axioms Johnson.Top.H.fit_of_check₂
