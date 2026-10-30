-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoLedAt.lean.
The places of each sumcheck's own masks in a sub-proof's lookup, from its first slot on.

`LedAt L first dg n` says of the places L of one sumcheck: the form of its hiding polynomial reads
the mask row from entry `first` on in the order of the verifier's walk, and the masks of its n shown
values stand right behind. dg: for each round the number of scalars sent.

Main names:
  `ledAt_led`: sumcheck number i of any lookup, its places by the ledger made total. Premise: it
    has at least one round.
  `ledAt_tie`, `ledAt_key`, `ledAt_tab`, `ledAt_end`, `ledAt_bit`: each sumcheck of a sub-proof's
    lookup, at the places that the running function reads (`Fo.numsF`), with its first slot
    jLK + fTie j and so on. A step or level must be one that is played (j < 31, l < v, l < d).

The clause on the shown values speaks of the numbers below n alone: the ledger is made total by
sending a greater number to the last shown value's place.

Limits: places alone. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoWalkLed
import OnBytes.Tie.Pv.Lookup.Forest.FoEnds

set_option autoImplicit false

namespace Fo
open TwV TwNums TwNums.Sizes OnBytes.Model OnBytes.PscTie Cb.Fo.Walk

/-- The places of a sumcheck's own masks, from its first slot on. -/
structure LedAt (L : Led Pl) (first : ℕ) (dg : List ℕ) (n : ℕ) : Prop where
  hide : ∀ (K : Type) [CommRing K] (xs : List K) (mask : ℕ → K), xs.length = dg.length →
    evalL (muOf mask) (TwV.hide L dg xs) =
      sumFrom (fun j x => x * mask j) first (walkK ((dg.zip xs).map fun p => (p.1 + 1, p.2)))
  sh : ∀ a, a < n → L.sh a = .mask (first + 1 + dg.sum + a)

theorem pairs_eq {K : Type} (dg : List ℕ) (xs : List K) :
    pairs dg xs = (dg.zip xs).map fun p => (p.1 + 1, p.2) := by
  unfold pairs
  rw [List.zip_map_left]
  rfl

theorem ledAt_led (S : Sizes) (i jLK : ℕ) (pl : Sizes.Ent → ℕ) (c : TwNums.Sc)
    (hc : S.scs.getD i ⟨[], false, 0⟩ = c) (hpl : ∀ e, pl e = S.place i (Sizes.Ent.clamp c e))
    (hne : c.degs ≠ []) : LedAt (ledF jLK pl) (jLK + S.firstOf i) c.degs c.shown where
  hide := fun K _ xs mask hl =>
    (hide_walk_led S i jLK pl c hc hpl xs hne hl (muOf mask)).trans (by rw [pairs_eq]; rfl)
  sh := fun a ha => by
    show Pl.mask (jLK + pl (.shown a)) = _
    rw [hpl, FoLedger.place_eq, hc]
    show Pl.mask (jLK + FoLedger.slotOf c.degs (S.firstOf i)
      (if c.shown = 0 then .const else .shown (min a (c.shown - 1)))) = _
    rw [if_neg (by omega), Nat.min_eq_left (by omega)]
    show Pl.mask (jLK + (S.firstOf i + 1 + c.degs.sum + a)) = _
    congr 1
    omega

section
variable (h : Forest.Shape) (jLK : ℕ)

theorem ledAt_tie (j : ℕ) (hj : j < 31) : LedAt (ledF jLK ((FoNums.S h).pTieC j))
    (jLK + (FoNums.S h).fTie j) [3] (if j = 0 then 3 else 2) :=
  ledAt_led (FoNums.S h) ((FoNums.S h).iTie j) jLK _ ((FoNums.S h).scTie j)
    (scs_tie (FoNums.S h) j hj _) (fun _ => if_pos hj) (by simp [Sizes.scTie])

theorem ledAt_key (l : ℕ) (hl : l < h.v) : LedAt (ledF jLK ((FoNums.S h).pKeyC l))
    (jLK + (FoNums.S h).fKey l) (List.replicate l 2 ++ [2]) 2 :=
  ledAt_led (FoNums.S h) ((FoNums.S h).iKey l) jLK _ ((FoNums.S h).scKey l)
    (scs_key (FoNums.S h) l hl _) (fun _ => if_pos hl) (by simp [Sizes.scKey])

theorem ledAt_tab (l : ℕ) (hl : l < h.d) : LedAt (ledF jLK ((FoNums.S h).pTabC l))
    (jLK + (FoNums.S h).fTab l) (List.replicate (5 + l) 2 ++ [2]) 2 :=
  ledAt_led (FoNums.S h) ((FoNums.S h).iTab l) jLK _ ((FoNums.S h).scTab l)
    (scs_tab (FoNums.S h) l hl _) (fun _ => if_pos hl) (by simp [Sizes.scTab])

theorem ledAt_bit : LedAt (ledF jLK (FoNums.S h).pBitC)
    (jLK + (FoNums.S h).fBit) (List.replicate (5 + h.d) 2 ++ [2]) 1 :=
  ledAt_led (FoNums.S h) (FoNums.S h).iBit jLK _ (FoNums.S h).scBit
    (scs_bit (FoNums.S h) _) (fun _ => rfl) (by simp [Sizes.scBit])

/-- The leaves' sumcheck shows nothing. Its degrees: 2 in a variable of the rows, 1 in one of the
planes, by round. -/
theorem ledAt_end : LedAt (ledF jLK (FoNums.S h).pEndC)
    (jLK + (FoNums.S h).fEnd) (FoNums.S h).scEnd.degs 0 :=
  ledAt_led (FoNums.S h) (FoNums.S h).iEnd jLK _ (FoNums.S h).scEnd
    (scs_end (FoNums.S h) _) (fun _ => rfl) (fun hn => by
      have hlen : (FoNums.S h).scEnd.degs.length = 5 + h.d := by
        show (((List.range (5 + h.d)).reverse).map _).length = _
        simp
      rw [hn] at hlen
      simp at hlen
      omega)

/-- These are the places that the running function reads. -/
theorem nums_led {K : Type} [CommRing K] (lm : ℕ) (θ : K) :
    (numsF h lm jLK θ).ledTie = (fun j => ledF jLK ((FoNums.S h).pTieC j)) ∧
    (numsF h lm jLK θ).ledK = (fun l => ledF jLK ((FoNums.S h).pKeyC l)) ∧
    (numsF h lm jLK θ).ledT = (fun l => ledF jLK ((FoNums.S h).pTabC l)) ∧
    (numsF h lm jLK θ).ledB = ledF jLK (FoNums.S h).pBitC ∧
    (numsF h lm jLK θ).ledE.pw = (ledF jLK (FoNums.S h).pEndC).pw ∧
    (numsF h lm jLK θ).ledE.c0 = (ledF jLK (FoNums.S h).pEndC).c0 ∧
    dgE (numsF h lm jLK θ) = (FoNums.S h).scEnd.degs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by
    show (FoNums.ordE h).map _ = ((List.range (5 + h.d)).reverse).map _
    rw [Cb.Fo.ordE_default]
    rfl⟩

end
end Fo
