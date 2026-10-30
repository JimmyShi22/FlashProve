-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SendsKeys.lean: THE LIST OF SENDINGS (Johnson.G.sendsOf, Johnson/G/Sends.lean),
WHEREVER IT RETURNS, HAS SEVEN CHAINS, WHICH BEAR, IN ORDER, THE FILES AND NUMBERS ("key", 0 | 1 |
2), ("entry", 0), ("proof", 0 | 1 | 2): by its own text. So just the fifth bears ("proof", 0).
Theorems. No value is evaluated.

  mapM_all2         where mapM returns, member by member the step has returned the value's member
  sends_keys        the seven (file, number) pairs
  first_is_fifth    of a value of seven chains by name the filter at ("proof", 0) leaves the fifth

Limits. Nothing on whether sendsOf returns. No soundness statement.

-/
import Johnson.Top.H0.Opts.RowsShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts

open OnBytes OnBytes.Params
open Johnson.G (Sending ChainSends sendsOf)
open Johnson.G.OfPlan (bind_ok)

theorem mapM_all2 {ε α β : Type} (f : α → Except ε β) : ∀ (l : List α) (r : List β),
    l.mapM f = .ok r → List.Forall₂ (fun a b => f a = .ok b) l r
  | [], r, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    exact .nil
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, h1, h⟩ := bind_ok h
    obtain ⟨r', h2, h⟩ := bind_ok h
    obtain rfl : y :: r' = r := Except.ok.inj h
    exact .cons h1 (mapM_all2 f l r' h2)

/-- **The seven chains' files and numbers.** -/
theorem sends_keys {pol lay KL : ByteArray} {sends : List ChainSends}
    (h : sendsOf pol lay KL = .ok sends) :
    sends.map (fun c => (c.file, c.chain)) =
      [("key", 0), ("key", 1), ("key", 2), ("entry", 0), ("proof", 0), ("proof", 1),
        ("proof", 2)] := by
  unfold sendsOf at h
  obtain ⟨p, -, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨w1, -, h⟩ := bind_ok h
    obtain ⟨w2, -, h⟩ := bind_ok h
    obtain ⟨w3, -, h⟩ := bind_ok h
    obtain ⟨w4, -, h⟩ := bind_ok h
    have hF := mapM_all2 _ _ _ h
    cases hF with
    | cons h0 hF => cases hF with
      | cons h1 hF => cases hF with
        | cons h2 hF => cases hF with
          | cons h3 hF => cases hF with
            | cons h4 hF => cases hF with
              | cons h5 hF => cases hF with
                | cons h6 hF =>
                  cases hF
                  obtain ⟨-, h0⟩ := ite_ok h0
                  obtain ⟨o0, -, h0⟩ := bind_ok h0
                  obtain rfl := Except.ok.inj h0
                  obtain ⟨-, h1⟩ := ite_ok h1
                  obtain ⟨o1, -, h1⟩ := bind_ok h1
                  obtain rfl := Except.ok.inj h1
                  obtain ⟨-, h2⟩ := ite_ok h2
                  obtain ⟨o2, -, h2⟩ := bind_ok h2
                  obtain rfl := Except.ok.inj h2
                  obtain ⟨-, h3⟩ := ite_ok h3
                  obtain ⟨o3, -, h3⟩ := bind_ok h3
                  obtain rfl := Except.ok.inj h3
                  obtain ⟨-, h4⟩ := ite_ok h4
                  obtain ⟨o4, -, h4⟩ := bind_ok h4
                  obtain rfl := Except.ok.inj h4
                  obtain ⟨-, h5⟩ := ite_ok h5
                  obtain ⟨o5, -, h5⟩ := bind_ok h5
                  obtain rfl := Except.ok.inj h5
                  obtain ⟨-, h6⟩ := ite_ok h6
                  obtain ⟨o6, -, h6⟩ := bind_ok h6
                  obtain rfl := Except.ok.inj h6
                  rfl
  · cases h

/-- **Just the fifth chain bears ("proof", 0).** -/
theorem first_is_fifth {pol lay KL : ByteArray} {k0 k1 k2 e p0 p1 p2 : ChainSends}
    (h : sendsOf pol lay KL = .ok [k0, k1, k2, e, p0, p1, p2]) :
    [k0, k1, k2, e, p0, p1, p2].filter (fun c => c.file == "proof" && c.chain == 0) = [p0] := by
  have hk := sends_keys h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hk
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, a6, b6⟩ := hk
  simp [List.filter_cons, a0, a1, a2, a3, a4, a5, a6, b4, b5, b6]

end P1Opts

#print axioms P1Opts.sends_keys
#print axioms P1Opts.first_is_fifth
