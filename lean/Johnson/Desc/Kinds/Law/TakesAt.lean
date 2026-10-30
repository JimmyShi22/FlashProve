-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TakesAt.lean: THE OUTPUT HEAD's BLOCK TAKES AT MOST 41 + 8 lt + 4 lPd NUMBERS OF THE LEDGER, WRITES ABOVE,
AND HAS NO LATE ROW: from Law/Takes.lean's hear_takes, at the block's decision.
  k6_decide_takes   at any seat whose laying and reading of the ledger fit: where the decision goes on from a
        ledger with a place for each number: Takes (ledger s) (ledger s') (41 + 4 lt + 4 n + 4 lPd) for an
        n ≤ lt: n is the number of coordinates of zt, the last lt of the lookup's point in the record.
  blockAt_takes     the same at the first chain's record.
  blockAt_room      IN THE FORM OF LedgerTakes (read at another text; not imported), at the lens S.fork?
        and t = 41 + 8 lt + 4 lPd, numbers of the plan alone: from room for t and m more it gives back
        room for m. · blockAt_above: in the form of its LedgerWritesAbove.
WHAT IT IS NOT. Nothing on soundness. t IS A CEILING here: that n = lt wherever the decision goes on (the
rounds' count forces it) is not shown. The block's runs of claims: not here (three leave the record but
for the seat's setKeyForms; "join" is the lookup's own run). Room and "writes above" are written out, field
by field: the tie to these names is an anonymous constructor away, and is not made here.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Takes
import Johnson.Desc.Kinds.Law.HeardBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First (S)
open Norm (lt lPd)

/-- The count's ceiling, of the place's parameters. -/
def takesOf (p : Par) : Nat :=
  let _ := p.sizes
  41 + 8 * lt + 4 * lPd

theorem k6_decide_takes {S Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (par : Par)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : ∀ F H w s1 s2, L.setLedger s F = .ok s1 → L.setHeard s1 H = .ok s2 →
      L.ledger (L.setWeightClaim s2 w) = F)
    (hS : Sized (L.ledger s)) (hd : (kind cl L link piece par).decide s rs gs = .ok s') :
    ∃ t, t ≤ takesOf par ∧ Takes (L.ledger s) (L.ledger s') t := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) par L s rs
      = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, hg, hh, e1, e2, rfl⟩ := decideBy_spec hd'
  rw [hfit F H w s1 s2 e1 e2]
  have T := hear_takes hS hh
  obtain ⟨z, y, rfl⟩ := given_form hg
  refine ⟨_, ?_, T⟩
  have hz := last_size z.1 (let _ := par.sizes; lt)
  show (let _ := par.sizes; 41 + 4 * lt + 4 * (z.1.last lt).size + 4 * lPd) ≤ takesOf par
  unfold takesOf
  dsimp only at hz ⊢
  omega

variable (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat)

theorem blockAt_takes (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hS : Sized ((seatAt h iU3).ledger s)) (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ t, t ≤ takesOf (parOf h work) ∧
      Takes ((seatAt h iU3).ledger s) ((seatAt h iU3).ledger s') t :=
  k6_decide_takes (fun _ => ()) (seatAt h iU3) l 4 (parOf h work) s s' rs gs (seatAt_fit h iU3 s)
    hS hd

/-- Behind the block's decision the record holds a ledger. -/
theorem blockAt_fork (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') : s'.fork?.isSome = true := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, _, e1, e2, rfl⟩ := decideBy_spec hd'
  have e1' : s.putFork? F = .ok s1 := e1
  have hs1 := putFork?_ok e1'
  have hsome : s.fork?.isSome = true := by
    unfold S.putFork? at e1'
    split at e1'
    · assumption
    · cases e1'
  obtain ⟨o, o', ho, rfl, _, hq, _⟩ := setHeard_ok h iU3 e2
  show (S.fork? { s1 with here := .head o' }).isSome = true
  subst hs1
  cases hh : s.here with
  | head a =>
    by_cases hop : a.opened = true
    · simp only [S.putFork, hh, hop, if_true] at ho
      simp only [VerifiableInference.Desc.First.Here.head.injEq] at ho
      subst ho
      simp [S.fork?, hq]
    · simp [S.fork?, hh, hop] at hsome
  | lay a => simp [S.putFork, hh] at ho
  | att a => simp [S.putFork, hh] at ho
  | between => simp [S.fork?, hh] at hsome
  | fin a => simp [S.fork?, hh] at hsome
  | mem a => simp [S.fork?, hh] at hsome

/-- **In the form of LedgerTakes**, at the lens S.fork? and the plan's count. -/
theorem blockAt_room (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (F : Fork)
    (m : Nat) (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') (hF : s.fork? = some F)
    (sized : Sized F) (fits : F.next + (takesOf (parOf h work) + m) ≤ F.ns)
    (free : ∀ j, F.next ≤ j → ¬ OnBytes.PscRun.Filled F j) :
    ∃ F', s'.fork? = some F' ∧ Sized F' ∧ F'.next + m ≤ F'.ns ∧
      ∀ j, F'.next ≤ j → ¬ OnBytes.PscRun.Filled F' j := by
  have hl : (seatAt h iU3).ledger s = F := by
    show s.fork?.getD {} = F
    rw [hF]; rfl
  obtain ⟨F', hF'⟩ := Option.isSome_iff_exists.1 (blockAt_fork h iU3 work l s s' rs gs hd)
  have hl' : (seatAt h iU3).ledger s' = F' := by
    show s'.fork?.getD {} = F'
    rw [hF']; rfl
  obtain ⟨t, ht, T⟩ := blockAt_takes h iU3 work l s s' rs gs (by rw [hl]; exact sized) hd
  rw [hl, hl'] at T
  exact ⟨F', hF', T.room ht fits free⟩

/-- **In the form of LedgerWritesAbove.** -/
theorem blockAt_above (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (F : Fork)
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') (hF : s.fork? = some F)
    (sized : Sized F) :
    ∃ F', s'.fork? = some F' ∧ F.next ≤ F'.next ∧
      ∀ j, j < F.next → (OnBytes.PscRun.Filled F' j ↔ OnBytes.PscRun.Filled F j) := by
  have hl : (seatAt h iU3).ledger s = F := by
    show s.fork?.getD {} = F
    rw [hF]; rfl
  obtain ⟨F', hF'⟩ := Option.isSome_iff_exists.1 (blockAt_fork h iU3 work l s s' rs gs hd)
  have hl' : (seatAt h iU3).ledger s' = F' := by
    show s'.fork?.getD {} = F'
    rw [hF']; rfl
  obtain ⟨t, _, T⟩ := blockAt_takes h iU3 work l s s' rs gs (by rw [hl]; exact sized) hd
  rw [hl, hl'] at T
  exact ⟨F', hF', T.writesAbove⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_room
#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_above
