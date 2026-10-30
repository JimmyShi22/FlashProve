-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Unfolds/PubAsk.lean: Forest.pubAsk returns under a bound on the counts of padding keys.
Statements with their proofs; nothing is evaluated.
  `askB h V`: pubAsk's second and third tests, at a bound V in the place of the counts: a closed
    test.
  `foldl_le` | `loop_ok`: tools.
  `pubAsk_of`: pub.size = h.NT, h.calls.size = h.NC, pub's entries are at most V's place by place,
    and askB h V = true: then Forest.pubAsk h pub = .ok ().

Limits. Nothing on soundness.
-/
import OnBytes.Model.Forest

set_option autoImplicit false

namespace Johnson.Unfolds
open OnBytes OnBytes.Model

/-- pubAsk's tests on the counts, at a bound. -/
def askB (h : Forest.Shape) (V : Nat → Nat) : Bool :=
  ((List.range h.NT).all fun θ => decide (V θ ≤ 2 ^ h.dT)) &&
    (List.range h.NC).all fun c =>
      decide ((List.range (2 ^ h.iota.getD c 0)).foldl
        (fun s b => s + V (h.first.getD c 0 + b)) 0 < 2 ^ (h.dT + h.iota.getD c 0))

theorem foldl_le (f g : Nat → Nat) (hfg : ∀ b, f b ≤ g b) : ∀ (l : List Nat) (s s' : Nat), s ≤ s' →
    l.foldl (fun s b => s + f b) s ≤ l.foldl (fun s b => s + g b) s'
  | [], _, _, h => h
  | a :: l, s, s', h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_le f g hfg l _ _ (Nat.add_le_add h (hfg a))

theorem loop_ok (h : Forest.Shape) (pub : Array Nat) : ∀ (l : List Nat),
    (∀ c ∈ l, (List.range (2 ^ h.iota.getD c 0)).foldl
      (fun s b => s + pub.getD (h.first.getD c 0 + b) 0) 0 < 2 ^ (h.dT + h.iota.getD c 0)) →
    (forIn l PUnit.unit fun c _ => (
      if (List.range (2 ^ h.iota.getD c 0)).foldl
          (fun s b => s + pub.getD (h.first.getD c 0 + b) 0) 0 ≥ 2 ^ (h.dT + h.iota.getD c 0) then
          do
        throw "forest-only-padding"
        pure (ForInStep.yield PUnit.unit)
      else do
        pure PUnit.unit
        pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit))) = .ok PUnit.unit
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.forIn_cons]
    have ha := hl a (List.mem_cons_self ..)
    simp only [ge_iff_le, Nat.not_le.2 ha, if_false]
    exact loop_ok h pub l fun c hc => hl c (List.mem_cons_of_mem _ hc)

/-- **Where the counts lie under a bound that meets the tests, the tests on the counts return.** -/
theorem pubAsk_of (h : Forest.Shape) (pub : Array Nat) (V : Nat → Nat) (h1 : pub.size = h.NT)
    (h2 : h.calls.size = h.NC) (hV : ∀ θ, pub.getD θ 0 ≤ V θ) (hB : askB h V = true) :
    Forest.pubAsk h pub = .ok () := by
  unfold askB at hB
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hB
  obtain ⟨b1, b2⟩ := hB
  have e1 : (pub.size != h.NT || h.calls.size != h.NC) = false := by simp [h1, h2]
  have e2 : (pub.any fun x => decide (x > 2 ^ h.dT)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    rw [Array.any_eq_true] at hh
    obtain ⟨i, hi, hx⟩ := hh
    have e : pub.getD i 0 = pub[i] := by simp [Array.getD, hi]
    have k1 := hV i
    have k2 := b1 i (by omega)
    rw [e] at k1
    have := of_decide_eq_true hx
    omega
  have e3 := loop_ok h pub (List.range h.NC) fun c hc =>
    Nat.lt_of_le_of_lt (foldl_le _ _ (fun b => hV (h.first.getD c 0 + b)) _ 0 0 (Nat.le_refl 0))
      (b2 c (List.mem_range.1 hc))
  unfold Forest.pubAsk
  simp only [e1, e2, Bool.false_eq_true, if_false]
  exact Eq.trans (congrArg (fun z => z >>= fun _ => (pure PUnit.unit : Except String PUnit)) e3) rfl

end Johnson.Unfolds

#print axioms Johnson.Unfolds.foldl_le
#print axioms Johnson.Unfolds.loop_ok
#print axioms Johnson.Unfolds.pubAsk_of
