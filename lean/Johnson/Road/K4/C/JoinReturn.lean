-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/JoinReturn.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the lookup's join: a call's factor in the
join (Env.joinPart, OnBytes/Model/LayerForms.lean) RETURNS where the form of the keys of each of
the call's segments is there at each layer on which the segment exists: nothing else in its text
can refuse. Statements and proofs. General in the sizes.

  `foldlM_there`     a loop in Option returns where each step does, at every value carried.
  **`joinPart_some`**  the factor is there.

Not shown here. That the hypothesis holds at any plan: no example is shown here. Public data alone:
whether a form IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.LineReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env)

variable {v : Env}

/-- A loop in Option returns where each step does, at every value carried. -/
theorem foldlM_there {α σ : Type} {f : σ → α → Option σ} : ∀ (l : List α),
    (∀ x ∈ l, ∀ a, (f a x).isSome = true) → ∀ a, (l.foldlM f a).isSome = true
  | [], _, _ => rfl
  | x :: l, h, a => by
    obtain ⟨b, hb⟩ := some_of (h x List.mem_cons_self a)
    rw [List.foldlM_cons, hb]
    exact foldlM_there l (fun y hy => h y (List.mem_cons_of_mem _ hy)) b

/-- **A CALL's FACTOR IN THE LOOKUP's JOIN IS THERE.** CONDITIONAL: on H: the form of the keys of
each segment, at each layer on which the segment exists, under the weights that the text makes. -/
theorem joinPart_some {alpha theta : E} {q : ℕ} {c : CallD} {weighed : Array Bool}
    (H : ∀ s ∈ c.segs, ∀ lam, lam < v.y.Lam → (s.moe && !v.isMoe lam) = false →
      (v.line s.name lam (Env.ewFrom (eqTab (v.zj q c.lJ)) s)
        (if (s.n % v.y.S2 == 0 && s.name != "ROW") = true then
          Env.ewhFrom v.y.S2 (eqTab (v.zj q (c.lJ - v.y.ls))) s else #[])).isSome = true) :
    (v.joinPart alpha theta q c weighed).isSome = true := by
  unfold Env.joinPart
  dsimp only
  refine bind_there (foldlM_there _ (fun s hs a => foldlM_there _ (fun lam hl a' => ?_) a) _)
    fun _ => rfl
  by_cases hb : (s.moe && !v.isMoe lam) = true
  · rw [if_pos hb]
    rfl
  · rw [if_neg hb, Option.isSome_map]
    exact H s hs lam (List.mem_range.mp hl) (Bool.eq_false_iff.mpr hb)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.foldlM_there
#print axioms OnBytes.Road.K4.C.joinPart_some
