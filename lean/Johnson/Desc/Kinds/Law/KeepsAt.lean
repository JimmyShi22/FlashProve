-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeepsAt.lean: LedgerKeeps FOR THE OUTPUT HEAD's BLOCK AT THE FIRST CHAIN's RECORD.
OVER HeadSeatAt.lean and State.lean: the seat's
setLedger is putFork?, which refuses where no sub-proof's engine is there to be written; setHeard
refuses outside the head's link. `seatAt_fit`: so where both return, the seat reads behind the three
layings the ledger that was laid: AT EVERY RECORD. `blockAt_later`, `blockOf_later`: where the block's
decision goes on, the ledger behind is later.
-/
import Johnson.Desc.Kinds.Law.Keeps
import Johnson.Desc.Kinds.Law.HeardAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First (S)

theorem seatAt_fit (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (H : HeardAll)
    (w : SumOnMatrix) (s1 s2 : S) (e1 : (seatAt h iU3).setLedger s F = .ok s1)
    (e2 : (seatAt h iU3).setHeard s1 H = .ok s2) :
    (seatAt h iU3).ledger ((seatAt h iU3).setWeightClaim s2 w) = F := by
  have e1' : s.putFork? F = .ok s1 := e1
  have hs1 := putFork?_ok e1'
  have hsome : s.fork?.isSome = true := by
    unfold S.putFork? at e1'
    split at e1'
    · assumption
    · cases e1'
  obtain ⟨o, o', ho, rfl, _, hq, hF⟩ := setHeard_ok h iU3 e2
  show (S.fork? { s1 with here := .head o' }).getD {} = F
  subst hs1
  cases hh : s.here with
  | head a =>
    by_cases hop : a.opened = true
    · simp only [S.putFork, hh, hop, if_true] at ho
      simp only [VerifiableInference.Desc.First.Here.head.injEq] at ho
      subst ho
      simp [S.fork?, hq, hF]
    · simp [S.fork?, hh, hop] at hsome
  | lay a => simp [S.putFork, hh] at ho
  | att a => simp [S.putFork, hh] at ho
  | between => simp [S.fork?, hh] at hsome
  | fin a => simp [S.fork?, hh] at hsome
  | mem a => simp [S.fork?, hh] at hsome

/-- **LedgerKeeps for K6's block at S.** -/
theorem blockAt_later (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    Later ((seatAt h iU3).ledger s) ((seatAt h iU3).ledger s') :=
  k6_decide_later (fun _ => ()) (seatAt h iU3) l 4 (parOf h work) s s' rs gs (seatAt_fit h iU3 s) hd

/-- The same for `blockOf`, the block as it rides: iU3 is the number that the public record names. -/
theorem blockOf_later (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) :
    ∃ iU3, W.H.tl.ix.U.getD 2 none = some iU3 ∧ ∀ s s' rs gs, b.decide s rs gs = .ok s' →
      Later ((seatAt W.hS iU3).ledger s) ((seatAt W.hS iU3).ledger s') := by
  unfold blockOf at hb
  cases hu : W.H.tl.ix.U.getD 2 none with
  | none => rw [hu] at hb; simp at hb
  | some i =>
    rw [hu] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    exact ⟨i, rfl, fun s s' rs gs hd => blockAt_later _ _ _ _ s s' rs gs hd⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockOf_later
