-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/LayPasses.lean: the two passes of the rule that places the oracle messages of one
prover's message in trees (layTrees, OnBytes/Iop/Ground.lean), under names.

In layTrees the passes are a local function. Here they are definitions, so that a law can be stated
of one step.

Main names.
  layStep: one step of a pass: the oracle message number i is placed.
  layPass: a pass. laidOf: what the two passes leave.
  foldlM_size: a loop in Option whose steps keep the size of the first array keeps it.
  layTrees_size: what layTrees returns has as many trees as the two passes have opened. Its proof
    holds these definitions against layTrees' own text.

What this file does not claim. That layTrees returns. Nothing on the loop that fills the trees but
that it keeps their number.


-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params
open OnBytes

/-- One step of a pass of layTrees: the oracle message number i is placed. -/
def layStep (codes : Codes) (sent : Array OracleNotice) (maskOnly : Bool)
    (s : Array TreeShape × Array Nat × Array Nat) (i : Nat) :
    Array TreeShape × Array Nat × Array Nat :=
  let n := sent.getD i default
  if (n.shape.mainRows == 0) != maskOnly then s
  else
    let logN := (codes.base.getD n.shape.code default).logN
    let fits (t : Nat) : Bool :=
      s.2.1.getD t noId == n.leafClass && (maskOnly || (s.1.getD t {}).logN == logN)
    match (List.range s.1.size).find? fits with
    | some t => (s.1, s.2.1, s.2.2.setIfInBounds i t)
    | none =>
      (s.1.push (if maskOnly then {} else { logN := logN }), s.2.1.push n.leafClass,
        s.2.2.setIfInBounds i s.1.size)

/-- A pass of layTrees. -/
def layPass (codes : Codes) (sent : Array OracleNotice) (maskOnly : Bool)
    (s : Array TreeShape × Array Nat × Array Nat) : Array TreeShape × Array Nat × Array Nat :=
  (List.range sent.size).foldl (layStep codes sent maskOnly) s

/-- What the two passes of layTrees leave. -/
def laidOf (codes : Codes) (sent : Array OracleNotice) :
    Array TreeShape × Array Nat × Array Nat :=
  layPass codes sent true (layPass codes sent false (#[], #[], Array.replicate sent.size 0))

/-- A loop in Option whose steps keep the size of the first array keeps it. -/
theorem foldlM_size {α β γ : Type} (step : Array γ × β → α → Option (Array γ × β))
    (hs : ∀ s a s', step s a = some s' → s'.1.size = s.1.size) :
    ∀ (l : List α) (s s' : Array γ × β), l.foldlM step s = some s' → s'.1.size = s.1.size
  | [], s, s', e => by
    rw [List.foldlM_nil] at e
    rw [← Option.some.inj e]
  | a :: l, s, s', e => by
    rw [List.foldlM_cons] at e
    obtain ⟨t, ht, e2⟩ := Option.bind_eq_some_iff.mp e
    rw [foldlM_size step hs l t s' e2, hs s a t ht]

/-- A step that refuses or returns a value. -/
theorem ite_none_pure {α : Type} {c : Prop} [Decidable c] {x y : α}
    (e : (if c then none else pure x : Option α) = some y) : x = y := by
  by_cases h : c
  · rw [if_pos h] at e
    cases e
  · rw [if_neg h] at e
    exact Option.some.inj e

/-- What layTrees returns has as many trees as the two passes have opened. -/
theorem layTrees_size {codes : Codes} {sent : Array OracleNotice} {T : TreeLay}
    (h : layTrees codes sent = some T) : T.shapes.size = (laidOf codes sent).1.size := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h2⟩ := Option.bind_eq_some_iff.mp h
  have k := foldlM_size _ (fun s i s' e => by
    rw [← ite_none_pure e]
    exact Array.size_modify) _ _ _ hf
  by_cases hc : ((filled.1.map fun t =>
      if t.mainWidth == 0 then { t with logN := t.logNzk } else t).all
        fun t => t.maskWidth == 0 || decide (t.logNzk ≤ t.logN)) = true
  · rw [if_pos hc] at h2
    rw [← Option.some.inj h2]
    show (filled.1.map _).size = _
    rw [Array.size_map]
    exact k
  · rw [if_neg hc] at h2
    cases h2

end OnBytes.Params
