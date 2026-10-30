-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoWalkLed.lean.
The ledger's own places meet the hypotheses of `hide_walk`.

`hide_walk` (FoWalk) speaks of any places that follow `slotCoef` and `slotConst`. This file states
that the places of the running function of a lookup do: for every sumcheck of every lookup
(`hide_walk_led`), and so at each sumcheck of a sub-proof's lookup, with its first slot
(`walk_tie`, `walk_key`, `walk_tab`, `walk_end`, `walk_bit`).
Premises: the sumcheck has at least one round; there are as many challenges as rounds; a step or
level is one that is played (j < 31, l < v, l < d).

Limits: places alone, on plain data. That the verifier's routines take these slots in a run is not
stated here. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoWalk
import OnBytes.Tie.Pv.Lookup.Forest.FoTies

set_option autoImplicit false

namespace Cb.Fo.Walk
open TwV TwNums TwNums.Sizes OnBytes.Model OnBytes.PscTie _root_.Fo

/-! ## The ledger's own places meet `hide_walk`'s hypotheses -/

section Led
variable {K : Type} [CommRing K]

theorem slotCoef_add (dg : List ℕ) (a f r t : ℕ) : slotCoef dg (a + f) r t = a + slotCoef dg f r t
    := by
  unfold slotCoef
  omega

theorem slotConst_add (dg : List ℕ) (a f : ℕ) : slotConst dg (a + f) = a + slotConst dg f := by
  unfold slotConst
  omega

/-- Sumcheck number i of any lookup, its places by the ledger made total, from the lookup's first
slot jLK on: the form of its hiding polynomial reads the slots from jLK + firstOf i on, in the order
of the verifier's walk. -/
theorem hide_walk_led (S : Sizes) (i jLK : ℕ) (pl : Sizes.Ent → ℕ) (c : TwNums.Sc)
    (hc : S.scs.getD i ⟨[], false, 0⟩ = c) (hpl : ∀ e, pl e = S.place i (Sizes.Ent.clamp c e))
    (xs : List K) (hne : c.degs ≠ []) (hl : xs.length = c.degs.length) (μ : Pl → K) :
    valS (hide (ledF jLK pl) c.degs xs) μ =
      sumFrom (fun k x => x * μ (.mask k)) (jLK + S.firstOf i) (walkK (pairs c.degs xs)) := by
  refine hide_walk (ledF jLK pl) μ (fun k => μ (.mask k)) c.degs xs (jLK + S.firstOf i) hne hl
    (fun r t _ ht => ?_) ?_
  · show μ (.mask (jLK + pl (.coef r t))) = μ (.mask (slotCoef c.degs (jLK + S.firstOf i) r t))
    rw [hpl, slotCoef_add, FoLedger.place_eq, hc]
    show μ (.mask (jLK + FoLedger.slotOf c.degs (S.firstOf i)
      (if t < c.degs.getD r 0 then .coef r t else .const))) = _
    rw [if_pos ht]
    rfl
  · show μ (.mask (jLK + pl .const)) = μ (.mask (slotConst c.degs (jLK + S.firstOf i)))
    rw [hpl, slotConst_add, FoLedger.place_eq, hc]
    rfl

variable (h : Forest.Shape) (lm jLK : ℕ) (θ : K) (μ : Pl → K) (xs : List K)

theorem walk_tie (j : ℕ) (hj : j < 31) (hl : xs.length = 1) :
    valS (hide ((numsF h lm jLK θ).ledTie j) [3] xs) μ =
      sumFrom (fun k x => x * μ (.mask k)) (jLK + (FoNums.S h).fTie j) (walkK (pairs [3] xs)) :=
  hide_walk_led (FoNums.S h) ((FoNums.S h).iTie j) jLK _ ((FoNums.S h).scTie j)
    (scs_tie (FoNums.S h) j hj _) (fun _ => if_pos hj) xs (by simp [Sizes.scTie]) hl μ

theorem walk_key (l : ℕ) (hv : l < h.v) (hl : xs.length = l + 1) :
    valS (hide ((numsF h lm jLK θ).ledK l) (List.replicate l 2 ++ [2]) xs) μ =
      sumFrom (fun k x => x * μ (.mask k)) (jLK + (FoNums.S h).fKey l)
        (walkK (pairs (List.replicate l 2 ++ [2]) xs)) :=
  hide_walk_led (FoNums.S h) ((FoNums.S h).iKey l) jLK _ ((FoNums.S h).scKey l)
    (scs_key (FoNums.S h) l hv _) (fun _ => if_pos hv) xs (by simp [Sizes.scKey])
    (by simpa [Sizes.scKey] using hl) μ

theorem walk_tab (l : ℕ) (hd : l < h.d) (hl : xs.length = 5 + l + 1) :
    valS (hide ((numsF h lm jLK θ).ledT l) (List.replicate (5 + l) 2 ++ [2]) xs) μ =
      sumFrom (fun k x => x * μ (.mask k)) (jLK + (FoNums.S h).fTab l)
        (walkK (pairs (List.replicate (5 + l) 2 ++ [2]) xs)) :=
  hide_walk_led (FoNums.S h) ((FoNums.S h).iTab l) jLK _ ((FoNums.S h).scTab l)
    (scs_tab (FoNums.S h) l hd _) (fun _ => if_pos hd) xs (by simp [Sizes.scTab])
    (by
      show xs.length = (List.replicate (5 + l) 2 ++ [2]).length
      simpa using hl) μ

theorem walk_bit (hl : xs.length = 5 + h.d + 1) :
    valS (hide (numsF h lm jLK θ).ledB (List.replicate (5 + h.d) 2 ++ [2]) xs) μ =
      sumFrom (fun k x => x * μ (.mask k)) (jLK + (FoNums.S h).fBit)
        (walkK (pairs (List.replicate (5 + h.d) 2 ++ [2]) xs)) :=
  hide_walk_led (FoNums.S h) (FoNums.S h).iBit jLK _ (FoNums.S h).scBit
    (scs_bit (FoNums.S h) _) (fun _ => rfl) xs (by simp [Sizes.scBit])
    (by
      show xs.length = (List.replicate (5 + h.d) 2 ++ [2]).length
      simpa using hl) μ

theorem walk_end (hl : xs.length = 5 + h.d) :
    valS (hide (numsF h lm jLK θ).ledE (dgE (numsF h lm jLK θ)) xs) μ =
      sumFrom (fun k x => x * μ (.mask k)) (jLK + (FoNums.S h).fEnd)
        (walkK (pairs (dgE (numsF h lm jLK θ)) xs)) := by
  have e : dgE (numsF h lm jLK θ) = (FoNums.S h).scEnd.degs := by
    show (FoNums.ordE h).map _ = ((List.range (5 + h.d)).reverse).map _
    rw [Cb.Fo.ordE_default]
    rfl
  have hlen : (FoNums.S h).scEnd.degs.length = 5 + h.d := by
    show (((List.range (5 + h.d)).reverse).map _).length = _
    simp
  rw [e]
  refine hide_walk_led (FoNums.S h) (FoNums.S h).iEnd jLK (FoNums.S h).pEndC (FoNums.S h).scEnd
    (scs_end (FoNums.S h) _) (fun _ => rfl) xs (fun hn => ?_) (by rw [hlen]; exact hl) μ
  rw [hn] at hlen
  simp at hlen
  omega

end Led


end Cb.Fo.Walk
