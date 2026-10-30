-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedDUnfold.lean.
How the value and the list of a routine's data unfold through a choice, a bind and a loop.

`FixedD` (OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean) holds, for a routine, a value v and a list L of
added claims as data. Its rules build the data of a bind and of a loop from those of the parts. Here
the results are written out.

The list of a bind is the first routine's list, then the second's list at the first's value, and
nothing if the first has no value. So the list of a loop breaks off behind the first pass that has
no value. A closed form holds where every pass has a value, which the lemmas on loops ask. On a run
that returns, the first clause of `FixedD.run` says that the value is there.

 * `ite_v`, `ite_L`: the data of `if p then x else y` are those of x or of y.
 * `bindD_some`: where the first routine's value is a: the list is the two lists one behind the
   other, and the value is the second's at a.
 * `foldlM_vL`: a fold over a list. If at every member a and every state s the pass has the value
   `step s a` and the list `Lf a`: the value is `l.foldl step s` and the list is `l.flatMap Lf`.
   `arrayFoldlM_vL`: the same over an array.
 * `forM_vL`: a loop without a state: if every pass has a value and the list `Lf a`: the list is
   `l.flatMap Lf`.
 * `forIn_vL`: a loop `for a in l` that goes on at every pass: if at every member a and every state
   s the pass has the value `.yield (step a s)` and the list `Lf a`: the value is the fold of step
   and the list is `l.flatMap Lf`.

Limits: those of OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedD

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

section
variable {α β σ : Type} [HasGood α] [HasGood β] [HasGood σ] {t0 : ℕ}

theorem ite_v {p : Prop} [Decidable p] {x y : SubM α} (hx : FixedD t0 x) (hy : FixedD t0 y)
    (k : ℕ → ℕ) : (FixedD.ite (p := p) hx hy).v k = if p then hx.v k else hy.v k := by
  unfold FixedD.ite
  by_cases h : p
  · rw [dif_pos h]
    exact (if_pos h).symm
  · rw [dif_neg h]
    exact (if_neg h).symm

theorem ite_L {p : Prop} [Decidable p] {x y : SubM α} (hx : FixedD t0 x) (hy : FixedD t0 y)
    (k : ℕ → ℕ) : (FixedD.ite (p := p) hx hy).L k = if p then hx.L k else hy.L k := by
  unfold FixedD.ite
  by_cases h : p
  · rw [dif_pos h]
    exact (if_pos h).symm
  · rw [dif_neg h]
    exact (if_neg h).symm

theorem bindD_some {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) {k : ℕ → ℕ} {a : α} (e : hx.v k = some a) :
    (hx.bind hf).v k = (hf a ⟨hx.goodV k a e⟩).v k ∧
    (hx.bind hf).L k = hx.L k ++ (hf a ⟨hx.goodV k a e⟩).L k :=
  ⟨by rw [bind_v, bindV_some hx hf e], by rw [bind_L, bindL_some hx hf e]⟩

theorem foldlM_vL {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedD t0 (f s a)) (k : ℕ → ℕ) (step : σ → α → σ)
    (Lf : α → List Cl) :
    ∀ (l : List α) (s : σ) (hl : Good t0 l) (hs : Good t0 s),
      (∀ a ∈ l, ∀ (s : σ) (gs : Good t0 s) (ga : Good t0 a),
        (hf s a gs ga).v k = some (step s a) ∧ (hf s a gs ga).L k = Lf a) →
      (FixedD.foldlM hf l s hl hs).v k = some (l.foldl step s) ∧
      (FixedD.foldlM hf l s hl hs).L k = l.flatMap Lf
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | a :: l, s, hl, hs, H => by
    obtain ⟨e1, e2⟩ := H a List.mem_cons_self s hs ⟨hl.out a List.mem_cons_self⟩
    obtain ⟨b1, b2⟩ := bindD_some (hf s a hs ⟨hl.out a List.mem_cons_self⟩)
      (fun s' hs' => FixedD.foldlM hf l s'
        ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ hs') e1
    obtain ⟨i1, i2⟩ := foldlM_vL hf k step Lf l (step s a)
      ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩
      ⟨(hf s a hs ⟨hl.out a List.mem_cons_self⟩).goodV k _ e1⟩
      fun b hb => H b (List.mem_cons_of_mem _ hb)
    refine ⟨?_, ?_⟩
    · show ((hf s a hs _).bind _).v k = _
      rw [b1, i1, List.foldl_cons]
    · show ((hf s a hs _).bind _).L k = _
      rw [b2, i2, e2, List.flatMap_cons]

theorem arrayFoldlM_vL {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedD t0 (f s a)) (k : ℕ → ℕ) (step : σ → α → σ)
    (Lf : α → List Cl) (l : Array α) (s : σ) (hl : Good t0 l) (hs : Good t0 s)
    (H : ∀ a ∈ l.toList, ∀ (s : σ) (gs : Good t0 s) (ga : Good t0 a),
      (hf s a gs ga).v k = some (step s a) ∧ (hf s a gs ga).L k = Lf a) :
    (FixedD.arrayFoldlM hf l s hl hs).v k = some (l.toList.foldl step s) ∧
    (FixedD.arrayFoldlM hf l s hl hs).L k = l.toList.flatMap Lf :=
  foldlM_vL hf k step Lf l.toList s ⟨hl.out⟩ hs H

theorem forM_vL {f : α → SubM PUnit} (hf : ∀ a, Good t0 a → FixedD t0 (f a)) (k : ℕ → ℕ)
    (Lf : α → List Cl) :
    ∀ (l : List α) (hl : Good t0 l),
      (∀ a ∈ l, ∀ ga : Good t0 a, (hf a ga).v k = some PUnit.unit ∧ (hf a ga).L k = Lf a) →
      (FixedD.forM hf l hl).v k = some PUnit.unit ∧ (FixedD.forM hf l hl).L k = l.flatMap Lf
  | [], _, _ => ⟨rfl, rfl⟩
  | a :: l, hl, H => by
    obtain ⟨e1, e2⟩ := H a List.mem_cons_self ⟨hl.out a List.mem_cons_self⟩
    obtain ⟨b1, b2⟩ := bindD_some (hf a ⟨hl.out a List.mem_cons_self⟩)
      (fun _ _ => FixedD.forM hf l ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩) e1
    obtain ⟨i1, i2⟩ := forM_vL hf k Lf l ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩
      fun b hb => H b (List.mem_cons_of_mem _ hb)
    refine ⟨?_, ?_⟩
    · show ((hf a _).bind _).v k = _
      rw [b1, i1]
    · show ((hf a _).bind _).L k = _
      rw [b2, i2, e2, List.flatMap_cons]

theorem forIn_vL {f : α → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedD t0 (f a s)) (k : ℕ → ℕ) (step : α → σ → σ)
    (Lf : α → List Cl) :
    ∀ (l : List α) (s : σ) (hl : Good t0 l) (hs : Good t0 s),
      (∀ a ∈ l, ∀ (s : σ) (ga : Good t0 a) (gs : Good t0 s),
        (hf a s ga gs).v k = some (.yield (step a s)) ∧ (hf a s ga gs).L k = Lf a) →
      (FixedD.forIn hf l s hl hs).v k = some (l.foldl (fun s a => step a s) s) ∧
      (FixedD.forIn hf l s hl hs).L k = l.flatMap Lf
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | a :: l, s, hl, hs, H => by
    obtain ⟨e1, e2⟩ := H a List.mem_cons_self s ⟨hl.out a List.mem_cons_self⟩ hs
    obtain ⟨i1, i2⟩ := forIn_vL hf k step Lf l (step a s)
      ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩
      ⟨(hf a s ⟨hl.out a List.mem_cons_self⟩ hs).goodV k _ e1⟩
      fun b hb => H b (List.mem_cons_of_mem _ hb)
    unfold FixedD.forIn
    rw [cast_v, cast_L, bind_v, bind_L, bindV_some _ _ e1, bindL_some _ _ e1, e2,
      List.flatMap_cons, List.foldl_cons]
    exact ⟨i1, congrArg _ i2⟩

end
end Fo
