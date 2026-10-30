-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoShapeIota.lean: Forest.shape does not read a call's field iota.

Forest.shape (OnBytes/Model/Forest.lean) makes a lookup's numbers of a list of calls and a cap on a
tree's depth. Two of the four layouts (Attention.shapeHid, Head.layout) run it on their calls, lay
the number iota that it returns into each call, and keep the NEW calls; a check then passes the new
calls to Forest.pad, which runs Forest.shape again. This file shows that the second run returns what
the first returned. (What the layouts do is shown in OnBytes/Tie/Pv/Lookup/Ends/FoMadeLay.lean; that
a check passes the new calls on is by a reading of the checks.)

 - strip, callAsk_strip: a call with 0 in the field iota; the tests on a call do not read the field.
 - bind_of_ok, jp_of_ok: the converses of ok_of_bind and ok_of_jp
   (OnBytes/Tie/Pv/Lookup/Ends/ShapePrem.lean).
 - asks_ok: the loop of the tests on the calls returns where each test does.
 - shape_iota: if c₁ and c₂ are the same lists but for the field iota (c₁.map strip = c₂.map strip)
   and Forest.shape c₁ lid returns f₁, then Forest.shape c₂ lid returns f₁ with the calls c₂.
   By walking the routine's own body twice: what it reads of a call is what callAsk reads (k, fn,
   t0, n, tau, kappa, heavy), n and k.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoShapes
import OnBytes.Tie.Pv.Lookup.Port.FoShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Ends

/-! ### Forest.shape does not read a call's field iota -/

/-- A call with 0 in the field iota. -/
def strip (c : Call) : Call := { c with iota := 0 }

theorem callAsk_strip (c : Call) : Forest.callAsk (strip c) = Forest.callAsk c := rfl

theorem bind_of_ok {α β : Type} {x : Except String α} {f : α → Except String β} {a : α} {y : β}
    (hx : x = .ok a) (hf : f a = .ok y) : (x >>= f) = .ok y := by
  rw [hx]
  exact hf

theorem jp_of_ok {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β} (hc : ¬ c) (h : jp PUnit.unit = .ok y) :
    (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y := by
  rw [if_neg hc]
  exact h

/-- The loop of the tests on the calls returns where each test does. -/
theorem asks_ok : ∀ (l : List Call), (∀ c ∈ l, Forest.callAsk c = .ok ()) →
    (forIn l PUnit.unit fun c _ => do
      Forest.callAsk c
      pure (ForInStep.yield PUnit.unit) : Except String PUnit) = .ok PUnit.unit
  | [], _ => rfl
  | a :: l, h => by
    rw [List.forIn_cons]
    refine bind_of_ok (a := ForInStep.yield PUnit.unit) ?_ ?_
    · exact bind_of_ok (h a List.mem_cons_self) rfl
    · exact asks_ok l fun c hc => h c (List.mem_cons_of_mem _ hc)

/-- **Forest.shape does not read a call's field iota**: at a list of calls that differs from c₁ in
that field alone it returns the same numbers. -/
theorem shape_iota {c₁ c₂ : Array Call} {lid : ℕ} {f₁ : Forest.Shape}
    (hs : c₁.map strip = c₂.map strip) (h₁ : Forest.shape c₁ lid = .ok f₁) :
    Forest.shape c₂ lid = .ok { f₁ with calls := c₂ } := by
  have hn : c₁.map (·.n) = c₂.map (·.n) := by
    have := congrArg (Array.map (·.n)) hs
    simpa [Array.map_map, Function.comp_def, strip] using this
  have hk : c₁.map (·.k) = c₂.map (·.k) := by
    have := congrArg (Array.map (·.k)) hs
    simpa [Array.map_map, Function.comp_def, strip] using this
  have ha : ∀ c ∈ c₂.toList, Forest.callAsk c = .ok () := by
    intro c hc
    have m : strip c ∈ c₁.map strip := by
      rw [hs]
      exact Array.mem_map.mpr ⟨c, Array.mem_toList_iff.mp hc, rfl⟩
    obtain ⟨c', hc', e⟩ := Array.mem_map.mp m
    rw [← callAsk_strip c, ← e, callAsk_strip]
    exact (Cb.Fo.shape_more h₁).2.2.2.2 c' (Array.mem_toList_iff.mpr hc')
  have es : c₂.size = c₁.size := by
    have := congrArg Array.size hn
    simpa using this.symm
  have eD : c₂.foldl (fun m c => min m c.n) lid = c₁.foldl (fun m c => min m c.n) lid := by
    have a : ∀ c : Array Call, c.foldl (fun m c => min m c.n) lid =
        (c.map (·.n)).foldl (fun m x => min m x) lid := fun c => by rw [Array.foldl_map]
    rw [a, a, hn]
  have eK : c₂.foldl (fun m c => max m c.k) 0 = c₁.foldl (fun m c => max m c.k) 0 := by
    have a : ∀ c : Array Call, c.foldl (fun m c => max m c.k) 0 =
        (c.map (·.k)).foldl (fun m x => max m x) 0 := fun c => by rw [Array.foldl_map]
    rw [a, a, hk]
  have eI : ∀ d : ℕ, (c₂.map fun c => c.n - d) = c₁.map fun c => c.n - d := fun d => by
    have a : ∀ c : Array Call, (c.map fun c => c.n - d) = (c.map (·.n)).map (· - d) :=
      fun c => by rw [Array.map_map]; rfl
    rw [a, a, hn]
  unfold Forest.shape at h₁ ⊢
  obtain ⟨_, _, h₁⟩ := ok_of_bind h₁
  obtain ⟨n1, h₁⟩ := ok_of_jp h₁
  obtain ⟨n2, h₁⟩ := ok_of_jp h₁
  obtain ⟨n3, h₁⟩ := ok_of_jp h₁
  obtain ⟨n4, h₁⟩ := ok_of_jp h₁
  obtain ⟨n5, h₁⟩ := ok_of_jp h₁
  obtain ⟨r₁, l₁, h₁⟩ := ok_of_bind h₁
  obtain ⟨n6, h₁⟩ := ok_of_jp h₁
  refine bind_of_ok (a := PUnit.unit) (by rw [← Array.forIn_toList]; exact asks_ok _ ha) ?_
  refine jp_of_ok (by rw [es]; exact n1) ?_
  refine jp_of_ok (by rw [eD]; exact n2) ?_
  refine jp_of_ok (by rw [eD, eI]; exact n3) ?_
  refine jp_of_ok (by rw [eD, eI]; exact n4) ?_
  refine jp_of_ok (by rw [eK, es]; exact n5) ?_
  refine bind_of_ok (a := r₁) (by rw [eD, eI, es]; exact l₁) ?_
  refine jp_of_ok (by rw [eD, eI]; exact n6) ?_
  rw [← Except.ok.inj h₁, eD, eK, eI, es]
  rfl

end Fo
