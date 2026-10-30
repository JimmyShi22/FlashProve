-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyMaskTakes.lean: which numbers a ledger hands out: take number k of a message's ledger is
takenNo rows k; at one mask row that is k.

  takeMaskP_number     one take
  takeMaskP_shape      a take leaves the message's shape
  takeMasksInto_numbers   n takes: the list of numbers
  takenNo_one          at one mask row, take number k is entry k

Nothing on any property.
-/
import Johnson.Desc.K13.Law.LedgerWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.FirstH
open OnBytes
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP takeMaskL ok)
open VerifiableInference.Desc.K13.Law (LedgerAt nextOf nextAt takenNo_at takeMaskP_within)
open _root_.Desc.Plain (DState)

variable {L : Type}

/-- **Take number k hands out takenNo rows k.** -/
theorem takeMaskP_number {d : DState L} {d' : DState L} {o k n : Nat} {x : OnBytes.Oracle}
    (hx : d.st.oracles[o]? = some x) (h : LedgerAt d.st o k) (ht : takeMaskP d o = some (n, d')) :
    n = takenNo x.shape.maskRows k := by
  obtain ⟨y, l, hy, hl, -, -, hr, hq, -, hnext⟩ := h
  obtain rfl : x = y := Option.some.inj (hx.symm.trans hy)
  unfold takeMaskP at ht
  split at ht
  · have hb : (d.st.oracles[o]?).bind (·.ledger) = some l := by
      rw [hy]
      exact hl
    rw [hb] at ht
    have e := (Prod.mk.inj (Option.some.inj ht)).1
    rw [← e, hr, hq, hnext]
    exact takenNo_at x.shape.maskRows k
  · cases ht

/-- **A take leaves the message's shape.** -/
theorem takeMaskP_shape {d d' : DState L} {o n : Nat} {x : OnBytes.Oracle}
    (hx : d.st.oracles[o]? = some x) (ht : takeMaskP d o = some (n, d')) :
    ∃ y : OnBytes.Oracle, d'.st.oracles[o]? = some y ∧ y.shape = x.shape := by
  unfold takeMaskP at ht
  split at ht
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none =>
      rw [hl] at ht
      cases ht
    | some l =>
      rw [hl] at ht
      have e := (Prod.mk.inj (Option.some.inj ht)).2
      subst e
      refine ⟨{ x with ledger := some { l with
        next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1
        left := l.left - 1 } }, ?_, rfl⟩
      show (d.st.oracles.modify o _)[o]? = _
      rw [Array.getElem?_modify, if_pos rfl, hx]
      rfl
  · cases ht

/-- **n takes hand out these numbers.** -/
theorem takeMasksInto_numbers (o : Nat) : ∀ (n : Nat) (d : DState L) (acc : Array Nat)
    (t : List Nat × DState L) (k : Nat) (x : OnBytes.Oracle), d.st.oracles[o]? = some x →
    LedgerAt d.st o k → takeMasksInto o n d acc = some t →
    t.1 = acc.toList ++ (List.range n).map fun j => takenNo x.shape.maskRows (k + j)
  | 0, d, acc, t, k, x, _, _, ht => by
    have e : some (acc.toList, d) = some t := ht
    rw [← Option.some.inj e]
    simp
  | n + 1, d, acc, t, k, x, hx, h, ht => by
    unfold takeMasksInto at ht
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at ht
      cases ht
    | some q =>
      obtain ⟨i, d'⟩ := q
      rw [hm] at ht
      obtain ⟨y, hy, es⟩ := takeMaskP_shape hx hm
      have hi := takeMaskP_number hx h hm
      have g := takeMasksInto_numbers o n d' (acc.push i) t (k + 1) y hy
        (takeMaskP_within h hm).2.2 ht
      rw [g, es, Array.toList_push, List.append_assoc, List.range_succ_eq_map, List.map_cons,
        List.map_map, hi]
      simp only [Nat.add_zero, List.singleton_append, Function.comp_def]
      refine congrArg (fun l => acc.toList ++ takenNo x.shape.maskRows k :: l)
        (List.map_congr_left fun j _ => ?_)
      rw [show k + 1 + j = k + (j + 1) by omega]

/-- The search at one row stops where it starts. -/
theorem nextRealRow_one (fuel n : Nat) (hf : 0 < fuel) : Blk.nextRealRow 1 0 fuel n = n := by
  cases fuel with
  | zero => cases hf
  | succ fuel =>
    unfold Blk.nextRealRow
    rw [if_pos (by simp [Nat.mod_one])]

/-- **At one mask row take number k is entry k.** -/
theorem takenNo_one : ∀ k, takenNo 1 k = k
  | 0 => nextRealRow_one _ _ (by decide)
  | k + 1 => by
    rw [takenNo, takenNo_one k]
    exact nextRealRow_one _ _ (by decide)

/-- **At one mask row the ledger's next number behind k takes is k.** -/
theorem nextAt_one : ∀ k, nextAt 1 k = k
  | 0 => rfl
  | k + 1 => by
    show takenNo 1 k + 1 = k + 1
    rw [takenNo_one]

end AtPublicFiles.FirstH
