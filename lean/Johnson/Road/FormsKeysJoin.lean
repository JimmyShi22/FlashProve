-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysJoin.lean: what one call's factor in the lookup's join is worth, given what
the forms of its segments are worth.

The verifier gathers the forms of a call's segments, layer by layer, in one form (Env.joinPart in
OnBytes/Model/LayerForms.lean). This file unfolds the folds of that function.

Main definitions: ewJ, whJ (the weights that the join passes to line), padJ.
Main theorem: joinPart_value.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. What the forms of the segments are worth is
a hypothesis here. The program does not import this file.

-/
import Johnson.Road.FormsKeysKit
import OnBytes.Iop.RowLaws

set_option autoImplicit false

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab Seg CallD)
open OnBytes.Model.Layer (Env aff0)

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-! ## Folds -/

/-- A fold of steps that may refuse, on forms: if the step at x adds g x to the value, the fold adds
the sum. -/
theorem foldlM_value {α : Type} (step : Aff → α → Option Aff) (g : α → K) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s s', step s x = some s' → s'.value ρ W = s.value ρ W + g x) →
      ∀ s a, l.foldlM step s = some a → a.value ρ W = s.value ρ W + (l.map g).sum
  | [], _, s, a, h => by
    have hs : s = a := by simpa using h
    subst hs
    simp
  | x :: l, H, s, a, h => by
    rw [List.foldlM_cons] at h
    cases hq : step s x with
    | none => simp [hq] at h
    | some s' =>
      rw [hq] at h
      have h2 : l.foldlM step s' = some a := by simpa using h
      rw [foldlM_value step g l (fun y hy => H y (List.mem_cons_of_mem _ hy)) s' a h2,
        H x List.mem_cons_self s s' hq, List.map_cons, List.sum_cons]
      ring

/-- A fold on elements of the field: if the step at x adds g x to the reading, the fold adds the
sum. -/
theorem foldl_value {α : Type} (G : E → α → E) (g : α → K)
    (H : ∀ s x, ρ.val (G s x) = ρ.val s + g x) :
    ∀ (l : List α) (s : E), ρ.val (l.foldl G s) = ρ.val s + (l.map g).sum
  | [], s => by simp
  | x :: l, s => by
    rw [List.foldl_cons, foldl_value G g H l, H, List.map_cons, List.sum_cons]
    ring

/-- The sum of the negatives is the negative of the sum. -/
theorem list_sum_neg {α : Type} (A : α → K) :
    ∀ l : List α, (l.map fun x => -A x).sum = -(l.map A).sum
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.sum_cons, list_sum_neg A l, List.map_cons, List.sum_cons]
    ring

/-! ## The parts of a call's factor -/

/-- The weights of the entries of segment s in call c, number q, as the join makes them. -/
def ewJ (v : Env) (q : ℕ) (c : CallD) (s : Seg) : Array E :=
  Env.ewFrom (eqTab (v.zj q c.lJ)) s

/-- The weights of the blocks of segment s, as the join makes them: none for a segment that is not a
whole number of blocks, and none for the rows of digits. -/
def whJ (v : Env) (q : ℕ) (c : CallD) (s : Seg) : Array E :=
  if s.n % v.y.S2 == 0 && s.name != "ROW" then
    Env.ewhFrom v.y.S2 (eqTab (v.zj q (c.lJ - v.y.ls))) s
  else #[]

/-- The weight of layer lam at the point of call q. -/
def elJ (v : Env) (q lam : ℕ) : E := (eqTab (v.zl q)).getD lam zeroE

/-- The forms of all segments of a call on all layers, each under the negative of its layer's
weight, as the join gathers them. -/
def linesJ (v : Env) (q : ℕ) (c : CallD) : Option Aff :=
  c.segs.foldlM
    (fun a s =>
      (List.range v.y.Lam).foldlM
        (fun (a : Aff) lam =>
          if s.moe && !v.isMoe lam then some a
          else (v.line s.name lam (ewJ v q c s) (whJ v q c s)).map fun f =>
            a.addMul f (negE (elJ v q lam)))
        a)
    aff0

/-- The weight of the padding's columns, as the join computes it. -/
def padE (v : Env) (q : ℕ) (c : CallD) (weighed : Array Bool) : E :=
  (List.range v.y.Lam).foldl
    (fun p lam =>
      addE p (mulE (elJ v q lam) ((List.range c.J).foldl
        (fun s j =>
          if weighed.getD (lam * c.J + j) true then s
          else addE s ((eqTab (v.zj q c.lJ)).getD j zeroE)) zeroE)))
    zeroE

/-- What joinPart is, in these parts. -/
theorem joinPart_eq (v : Env) (alpha theta : E) (q : ℕ) (c : CallD) (weighed : Array Bool) :
    v.joinPart alpha theta q c weighed = (do
      let lines ← linesJ v q c
      pure (Aff.ofConst (subE (subE alpha (Model.scaleNat theta q))
        (scaleE ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0) (padE v q c weighed))) +
          lines)) := by
  rfl

/-- The weight of the columns of call c that hold padding: for each layer its weight times the sum
of the weights of the columns that are not marked. -/
def padJ (v : Env) (q : ℕ) (c : CallD) (weighed : Array Bool) : K :=
  ((List.range v.y.Lam).map fun lam =>
    ρ.val (elJ v q lam) * ((List.range c.J).map fun j =>
      if weighed.getD (lam * c.J + j) true = true then 0
      else ρ.val ((eqTab (v.zj q c.lJ)).getD j zeroE)).sum).sum

/-- The verifier's weight of the padding's columns reads as padJ. -/
theorem padE_value (v : Env) (q : ℕ) (c : CallD) (weighed : Array Bool) :
    ρ.val (padE v q c weighed) = padJ ρ v q c weighed := by
  unfold padE padJ
  rw [foldl_value ρ _ (fun lam => ρ.val (elJ v q lam) * ((List.range c.J).map fun j =>
      if weighed.getD (lam * c.J + j) true = true then 0
      else ρ.val ((eqTab (v.zj q c.lJ)).getD j zeroE)).sum) _ _ zeroE, ρ.zero, zero_add]
  intro p lam
  rw [ρ.add, ρ.mul, foldl_value ρ _ (fun j =>
      if weighed.getD (lam * c.J + j) true = true then 0
      else ρ.val ((eqTab (v.zj q c.lJ)).getD j zeroE)) _ _ zeroE, ρ.zero, zero_add]
  intro s j
  beta_reduce
  split_ifs
  · rw [add_zero]
  · rw [ρ.add]

/-! ## The factor -/

/-- One call's factor in the lookup's join: alpha - q theta, less the padding key times the weight
of the padding's columns, less the forms of the segments, each layer under its weight. Lv s lam is
what the form of segment s at layer lam of the group is worth. A segment that exists only on layers
with routed experts adds nothing on the other layers. -/
theorem joinPart_value (hρ : Numerals ρ) (v : Env) (alpha theta : E) (q : ℕ) (c : CallD)
    (weighed : Array Bool) (Lv : Seg → ℕ → K)
    (HL : ∀ s ∈ c.segs, ∀ lam f, lam < v.y.Lam → (s.moe && !v.isMoe lam) = false →
      v.line s.name lam (ewJ v q c s) (whJ v q c s) = some f → f.value ρ W = Lv s lam)
    {f : Aff} (h : v.joinPart alpha theta q c weighed = some f) :
    f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
      ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) * padJ ρ v q c weighed -
      (c.segs.map fun s => ((List.range v.y.Lam).map fun lam =>
        if (s.moe && !v.isMoe lam) = true then 0 else ρ.val (elJ v q lam) * Lv s lam).sum).sum := by
  rw [joinPart_eq] at h
  cases h1 : linesJ v q c with
  | none => rw [h1] at h; cases h
  | some lines =>
    rw [h1] at h
    cases h
    have inner : ∀ s ∈ c.segs, ∀ a0 a : Aff,
        (List.range v.y.Lam).foldlM
          (fun (a : Aff) lam =>
            if s.moe && !v.isMoe lam then some a
            else (v.line s.name lam (ewJ v q c s) (whJ v q c s)).map fun f =>
              a.addMul f (negE (elJ v q lam))) a0 = some a →
        a.value ρ W = a0.value ρ W + -((List.range v.y.Lam).map fun lam =>
          if (s.moe && !v.isMoe lam) = true then 0 else ρ.val (elJ v q lam) * Lv s lam).sum := by
      intro s hs a0 a ha
      rw [← list_sum_neg]
      refine foldlM_value ρ W _ _ _ ?_ a0 a ha
      intro lam hlam s0 s' hstep
      by_cases hsk : (s.moe && !v.isMoe lam) = true
      · rw [if_pos hsk] at hstep
        cases hstep
        rw [if_pos hsk, neg_zero, add_zero]
      · rw [if_neg hsk] at hstep
        obtain ⟨g, hg, e⟩ := map_some hstep
        subst e
        rw [Aff.value_addMul, hρ.neg,
          HL s hs lam g (List.mem_range.mp hlam) (Bool.not_eq_true _ ▸ hsk) hg, if_neg hsk]
        ring
    have outer := foldlM_value ρ W _ (fun s => -((List.range v.y.Lam).map fun lam =>
        if (s.moe && !v.isMoe lam) = true then 0 else ρ.val (elJ v q lam) * Lv s lam).sum)
      c.segs inner aff0 lines h1
    rw [Aff.value_add, Aff.value_ofConst, ρ.sub, ρ.sub, hρ.scaleNat, scaleE_val, padE_value, outer,
      aff0_value, list_sum_neg]
    ring

#print axioms joinPart_value

end OnBytes.Road
