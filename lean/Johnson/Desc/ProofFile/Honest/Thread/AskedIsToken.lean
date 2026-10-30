-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/AskedIsToken.lean: where the test on the instance says yes, the
reply that the instance asks about is a token of the vocabulary. The test on the instance reads the
reply file's first word and refuses it where it is not below the vocabulary's size.
-/
import Johnson.Desc.ProofFile.Pub
import Johnson.Desc.Reply.ReplyStep
import Johnson.Desc.Kinds.Law.ReplyHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes.Desc.Reply (isToken)

/-- Where the statement's words are read, the reply is the reply file's first word. -/
theorem stFromCall_y {P Q : Array UInt32} {T : Nat} {so : OnBytes.Model.Head.StOwn}
    (h : OnBytes.Model.Head.stFromCall P Q T = .ok so) : so.y = (Q.getD 0 0).toNat := by
  unfold OnBytes.Model.Head.stFromCall at h
  simp only [OnBytes.Model.Head.needed, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl

/-- Where the covered positions are read, the reply is below the vocabulary's size. -/
theorem coveredOf_y {so : OnBytes.Model.Head.StOwn} {T V : Nat} {c : OnBytes.Model.Head.Covered}
    (h : OnBytes.Model.Head.coveredOf so T V = .ok c) : so.y < V := by
  by_cases hy : so.y < V
  · exact hy
  · exfalso
    have e : OnBytes.Model.Head.coveredOf so T V = .error "token-range" := by
      unfold OnBytes.Model.Head.coveredOf
      simp [OnBytes.Model.Head.needed, hy, bind, Except.bind]
    rw [e] at h
    cases h

theorem ok_of_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem ok_of_held {α : Type} {s : String} {y : Except String α} {v : α}
    (h : ProofFile.held s y = .ok v) : y = .ok v := by
  cases y with
  | error e => cases h
  | ok a =>
    have e : (Except.ok a : Except (String × String) α) = .ok v := h
    cases e
    rfl

/-- **Where the test on the instance says yes, the reply file's first word is below the
vocabulary's size.** -/
theorem reply_below_vocabulary {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    (h : ProofFile.okBy o mk Z x = true) :
    ((OnBytes.Model.Verify.words32 x.y).getD 0 0).toNat < Z.p.X.P.h.V := by
  unfold ProofFile.okBy at h
  cases hh : ProofFile.holdBy o mk Z x with
  | error e =>
    rw [hh] at h
    cases h
  | ok g =>
    unfold ProofFile.holdBy at hh
    obtain ⟨_, -, hh⟩ := ok_of_bind hh
    obtain ⟨so, hso, hh⟩ := ok_of_bind hh
    obtain ⟨cov, hcov, -⟩ := ok_of_bind hh
    have hy := coveredOf_y (ok_of_held hcov)
    rwa [stFromCall_y (ok_of_held hso)] at hy

/-- A number below a vocabulary of at most the prime's size is a token, as a field element. -/
theorem isToken_ofNat {V y : Nat} (hy : y < V) (hV : V ≤ OnBytes.pW.toNat) :
    isToken V (OnBytes.Model.ofNat y) = true := by
  have hlt : y < OnBytes.pW.toNat := Nat.lt_of_lt_of_le hy hV
  have h64 : y < 18446744073709551616 := Nat.lt_trans hlt (UInt64.toNat_lt _)
  have e : (Nat.toUInt64 y).toNat = y := by
    simpa using h64
  simp only [isToken, OnBytes.Model.ofNat, OnBytes.Model.fOfNat, OnBytes.ofF, OnBytes.E.mk3,
    Nat.mod_eq_of_lt hlt]
  simp [e, hy]

/-- **Where the test on the instance says yes, the reply that the instance asks about is a token.**
The two premises are on the public part: its head's vocabulary is the scan's, and it is at most the
prime's size. -/
theorem asked_is_token {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    (h : ProofFile.okBy o mk Z x = true) (hV : Z.p.X.hS.V = Z.p.X.P.h.V)
    (hp : Z.p.X.hS.V ≤ OnBytes.pW.toNat) : isToken Z.p.X.hS.V x.asked = true := by
  unfold ProofFile.Inst.asked
  exact isToken_ofNat (hV ▸ reply_below_vocabulary h) hp

/-- **The asked reply is the field's element of its own token's number.** -/
theorem asked_ofNat {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    (h : ProofFile.okBy o mk Z x = true) (hV : Z.p.X.hS.V = Z.p.X.P.h.V)
    (hp : Z.p.X.hS.V ≤ OnBytes.pW.toNat) : OnBytes.Model.ofNat x.asked.c0.toNat = x.asked :=
  VerifiableInference.Desc.Kinds.Head.Law.ofNat_token Z.p.X.hS.V hp x.asked
    (asked_is_token h hV hp)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.asked_ofNat
#print axioms ProofFile.Honest.FirstThread.reply_below_vocabulary
#print axioms ProofFile.Honest.FirstThread.asked_is_token
