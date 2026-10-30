-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/GrowsAt.lean.
WHAT IT DOES NOT SHOW. No soundness. Nothing on what lies under a slot. It speaks of the kind's own
block (blockAt, blockOf); the seated block (Stored/HeadSeatAt.lean: seatedOf;
Stored/HeadAddsAtS.lean) says yes only where that one does, to the same state: not joined here. That
the two tests hold in front of the block: premises. WORDS. "The verifier's state": the value of type
S that the blocks hand on. "The ledger": its table of hidden scalars at the open link (S.fork?).
LETTERS. No "there is" in the tops.
OBJECT. The output head's block at S, and the table's files' two tests on the verifier's state
(Desc/First/FillKeeper.lean): ledgerB: a ledger is open and its three arrays have as many entries as
it has slots · freeAboveB n: a ledger is open; every slot from its next free number on is free; it
has n slots.
USER. The public items "ledger m" and "freeAbove m" behind the output head's block, in the promise
of the table of joints.
WHAT IT IS. THE OUTPUT HEAD's BLOCK KEEPS THE TWO TESTS: where both say yes in front of a yes of the
block, both say yes behind it, at the same n.
  seatAt_fork       behind the seat's three layings S.fork? is the ledger that was laid.
  k6_decide_grows   the block, at any seat whose laying and reading of the ledger fit: the ledger
                    grows (Law/GrowsHear.lean).
  blockAt_grows     at S.
  sized_iff, free_iff   the two tests in the library's words (OnBytes/Tie/Pv/Psc/: Sized,
                        FreeAbove); the second over freeAboveB_iff.
                        blockAt_freeAbove THE STATEMENT. blockOf_freeAbove the same for blockOf, the
                        block as it rides.
NEAREST RELATIVES: Law/KeepsAt.lean: seatAt_fit (the same ledger, read with a default) ·
blockAt_later · Desc/First/Look/K3CallsKeeps.lean: k3_calls_freeAbove (the like for the lookup on
the calls).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.GrowsHear
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.First.Look.K3CallsKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later Sized FreeAbove)
open VerifiableInference.Desc.First (S ledgerB freeAboveB)

/-- Behind the seat's three layings S.fork? is the ledger that was laid. -/
theorem seatAt_fork (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (H : HeardAll)
    (w : SumOnMatrix) (s1 s2 : S) (e1 : (seatAt h iU3).setLedger s F = .ok s1)
    (e2 : (seatAt h iU3).setHeard s1 H = .ok s2) :
    ((seatAt h iU3).setWeightClaim s2 w).fork? = some F := by
  have e1' : s.putFork? F = .ok s1 := e1
  have hs1 := putFork?_ok e1'
  have hsome : s.fork?.isSome = true := by
    unfold S.putFork? at e1'
    split at e1'
    · assumption
    · cases e1'
  obtain ⟨o, o', ho, rfl, _, hq, hF⟩ := setHeard_ok h iU3 e2
  show S.fork? { s1 with here := .head o' } = some F
  subst hs1
  cases hh : s.here with
  | head a =>
    by_cases hop : a.opened = true
    · simp only [S.putFork, hh, hop, if_true] at ho
      simp only [VerifiableInference.Desc.First.Here.head.injEq] at ho
      subst ho
      simp [S.fork?, hq, hF, hop]
    · simp [S.fork?, hh, hop] at hsome
  | lay a => simp [S.putFork, hh] at ho
  | att a => simp [S.putFork, hh] at ho
  | between => simp [S.fork?, hh] at hsome
  | fin a => simp [S.fork?, hh] at hsome
  | mem a => simp [S.fork?, hh] at hsome

/-- The block, at any seat whose laying and reading of the ledger fit. -/
theorem k6_decide_grows {S Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (par : Par)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : ∀ F H w s1 s2, L.setLedger s F = .ok s1 → L.setHeard s1 H = .ok s2 →
      L.ledger (L.setWeightClaim s2 w) = F)
    (hS : Sized (L.ledger s)) (hd : (kind cl L link piece par).decide s rs gs = .ok s') :
    Grows (L.ledger s) (L.ledger s') := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) par L s rs
      = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, hh, e1, e2, rfl⟩ := decideBy_spec hd'
  rw [hfit F H w s1 s2 e1 e2]
  exact keepsG_hear _ _ _ _ _ hS hh

/-- At S. -/
theorem blockAt_grows (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hS : Sized ((seatAt h iU3).ledger s)) (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    Grows ((seatAt h iU3).ledger s) ((seatAt h iU3).ledger s') :=
  k6_decide_grows (fun _ => ()) (seatAt h iU3) l 4 (parOf h work) s s' rs gs (seatAt_fit h iU3 s) hS
    hd

/-- The table's files' first test, in the library's words. -/
theorem sized_iff {s : S} {F : Fork} (hF : s.fork? = some F) : ledgerB s = true ↔ Sized F := by
  unfold ledgerB Sized
  rw [hF]
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- The table's files' second test, in the library's words. -/
theorem free_iff {s : S} {F : Fork} (n : Nat) (hF : s.fork? = some F) (hS : Sized F) :
    freeAboveB n s = true ↔ FreeAbove F ∧ F.ns = n := by
  have key := VerifiableInference.OnPublicFiles.freeAboveB_iff hF hS
  unfold VerifiableInference.OnPublicFiles.freeAboveB at key
  unfold freeAboveB
  rw [hF] at key ⊢
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at key ⊢
  rw [key]

/-- **THE OUTPUT HEAD's BLOCK KEEPS THE TWO TESTS.** -/
theorem blockAt_freeAbove (h : OnBytes.Model.Head.Shape) (iU3 work l n : Nat) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok t) (hL : ledgerB s = true)
    (hf : freeAboveB n s = true) : ledgerB t = true ∧ freeAboveB n t = true := by
  cases hF : s.fork? with
  | none =>
    unfold ledgerB at hL
    rw [hF] at hL
    cases hL
  | some F =>
    have hS : Sized F := (sized_iff hF).1 hL
    obtain ⟨a, b⟩ := (free_iff n hF hS).1 hf
    have hled : (seatAt h iU3).ledger s = F := by
      show s.fork?.getD {} = F
      rw [hF]
      rfl
    have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
        (seatAt h iU3) s rs = .ok t := hd
    obtain ⟨g, H, G, left, w, s1, s2, _, hh, e1, e2, et⟩ := decideBy_spec hd'
    have hG := seatAt_fork h iU3 s G H w s1 s2 e1 e2
    rw [← et] at hG
    rw [hled] at hh
    obtain ⟨c1, c2, c3⟩ := hear_free hS a hh
    exact ⟨(sized_iff hG).2 c3, (free_iff n hG c3).2 ⟨c1, c2.trans b⟩⟩

/-- The same for `blockOf`, the block as it rides. -/
theorem blockOf_freeAbove (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (n : Nat) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : b.decide s rs gs = .ok t) (hL : ledgerB s = true)
    (hf : freeAboveB n s = true) : ledgerB t = true ∧ freeAboveB n t = true := by
  unfold blockOf at hb
  cases hu : W.H.tl.ix.U.getD 2 none with
  | none => rw [hu] at hb; simp at hb
  | some i =>
    rw [hu] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    exact blockAt_freeAbove _ _ _ _ n s t rs gs hd hL hf

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.seatAt_fork
#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_grows
#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_freeAbove
#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockOf_freeAbove
