-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/K1Ids.lean: the three numbers that the first chain's record hands on behind the
place of W's commitment (W, the own group, the first fold's mask), by name and by position: at the
description's own joined block, with the sending kind's block as W's commitment. Statements with
their proofs.
Main names:
  `outs_length`: the sending lays one message for each shape.
  `sendAtS_full`: where the sending kind's block says yes at the first chain's state: the numbers
    that it hands on are those of the messages that it has just received, in order, and the
    statement's messages are the older ones with as many new ones behind them.
  `sendAtS_idsLast`: so `IdsLast` (Johnson/Desc/K13/Law/Mask.lean) holds behind it.
  `atM4_numbers`: **where the joined block says yes**: W stands as many places from the end of the
    statement's messages as messages were sent; the mask, where masks go ahead, is the last message,
    and else there is none; the own group is the last group.
Used of the sending kind's laws: `decideSend_iff` (Johnson/Desc/K1/Law/Writes3.lean), `map_ok`
(Johnson/Desc/K1/Law/Step.lean).

What is not claimed. That blocks behind this place receive no message and make no group: so that the
three numbers are by position still the same at the chain's end. That the message at the mask's
number is a mask. Where three messages are sent (a split's among them) W stands three places from
the end. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.Mask
import Johnson.Desc.K1.Law.HereAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- The sending lays one message for each shape. -/
theorem outs_length (codes : Codes) (seeds : List (List E × E)) :
    ∀ (l : List OracleShape) (o : ℕ) (ys : List E), (K1.outs codes seeds o l ys).length = l.length
  | [], _, _ => rfl
  | _ :: l, o, ys => congrArg (· + 1) (outs_length codes seeds l (o + 1) _)

/-- **Where the sending kind's block says yes.** -/
theorem sendAtS_full (P' : K1.Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (K1.sendAtS P' : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ a, s.here = .mem a ∧
      s'.here = .mem { a with ids := (Array.range P'.sent.size).map (· + s.st.oracles.size) } ∧
      ∃ new : List OnBytes.Oracle, new.length = P'.sent.size ∧
        s'.st.oracles.toList = s.st.oracles.toList ++ new := by
  unfold K1.sendAtS at h
  dsimp only at h
  split at h
  · rename_i a ha
    split at h
    · obtain ⟨y, hy, rfl⟩ := (K1.map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (K1.map_ok _ _ _).1 hy
      obtain ⟨ids, d'⟩ := x
      obtain ⟨_, rfl, rfl⟩ := (K1.decideSend_iff P' _ _ d' r₁ r₂ ids).1 hx
      refine ⟨a, ha, rfl, _, ?_, rfl⟩
      rw [outs_length]
      simp [K1.shapesOf]
    · cases h
  · cases h

/-- The numbers handed on are those of the statement's last messages, in order. -/
theorem sendAtS_idsLast (P' : K1.Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (K1.sendAtS P' : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ m, s'.here = .mem m ∧ m.ids.size = P'.sent.size ∧ IdsLast m.ids s'.st := by
  obtain ⟨a, _, h2, new, hn, hl⟩ := sendAtS_full P' s s' r₁ r₂ gs h
  have hsz : s'.st.oracles.size = s.st.oracles.size + P'.sent.size := by
    rw [← Array.length_toList, hl, List.length_append, hn, Array.length_toList]
  refine ⟨_, h2, by simp, ?_, fun i hi => ?_⟩
  · simp only [Array.size_map, Array.size_range]
    omega
  · simp only [Array.size_map, Array.size_range] at hi ⊢
    rw [Array.getElem?_map, Array.getElem?_range, if_pos hi, hsz]
    exact congrArg some (by show i + s.st.oracles.size = _; omega)

/-- **Where the joined block at the place of W's commitment says yes**: the three numbers, by
position. -/
theorem atM4_numbers (P : Where) (P' : K1.Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hg : gs.length = (K1.sendAtS P' : Block S Cl).openings)
    (h : (atM4 P (K1.sendAtS P' : Block S Cl)).decide s [r₁, r₂] gs = .ok s') :
    ∃ l, linAt s' = some l ∧ l.w = s'.st.oracles.size - P'.sent.size ∧
      (P.lin.masksAhead = true → l.mask = some (s'.st.oracles.size - 1)) ∧
      (P.lin.masksAhead = false → l.mask = none) ∧ l.own + 1 = s'.st.groups.size := by
  have h' : ((K1.sendAtS P' : Block S Cl).andThen _ (rowsB atS P)).decide s [r₁, r₂] gs = .ok s' :=
    h
  rw [andThen_decide _ _ _ _ _ _ rfl hg] at h'
  obtain ⟨mid, h1, h2⟩ := ebind_ok.1 h'
  obtain ⟨m, hm, hsz, hI⟩ := sendAtS_idsLast P' s mid r₁ r₂ gs h1
  obtain ⟨m₀, l, hm₀, hl, hmask⟩ := rowsB_mask h2
  obtain ⟨l', hl', _, hown⟩ := rowsB_own h2
  rw [hm] at hm₀
  obtain rfl : m = m₀ := by
    injection hm₀
  rw [hl] at hl'
  obtain rfl := Option.some.inj hl'
  obtain ⟨e1, e2, e3⟩ := hmask hI
  exact ⟨l, hl, by rw [e1, hsz], e2, e3, hown⟩

end VerifiableInference.Desc.K13.Law
