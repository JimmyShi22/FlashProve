-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeldAtPlan.lean: code switching: «BEHIND AN ACCEPT OF THE SWITCH's DECISION
THE STATE HOLDS THE OOD SAMPLE OF EVERY MEMBER OF N.index :: N.sent m 0», FROM TWO TESTS WITH CODE
ON THE LIST OF ROUNDS AND FACTS ON THE STATE IN FRONT. A joining of K2C/HeldAtYes.lean and
K2C/SentAtPlan.lean. General in the numbers N. NO SUB-PROTOCOL IMPORTS THIS FILE.
  hall_of_test    the test noticesFitB (K2C/NoticesFit.lean) accepts at «sent» · the front's notices
                  are «sent»: each of the notices but the last counts an answer and has a row
  held_of_tests   sentFitB (K2C/SentFit.lean) and noticesFitB accept · the accept · bookAt N pIn s ·
                  the book in front fits · the fence (K2C/SendsOn.lean) · SeedReads · the test
                  smpHeld accepts in front at N.index: it accepts behind at every member of
                  N.index :: N.sent m 0
LIMITS. NEITHER TEST HAS BEEN EVALUATED AT A LIST OF ROUNDS. Every other premise is a fact on the
state in front, or SeedReads (see K2C/HeldAtYes.lean's head): shown by nobody here. s is the state
at which the decision accepts: at the finish that is the state behind the way in. No way out is
treated. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HeldAtYes
import Johnson.Top.H0.Tw.K2C.SentAtPlan
import Johnson.Top.H0.Tw.K2C.NoticesFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open _root_.Tw.K2 (switchNotices sendByL8)
open VerifiableInference.Desc.Book (BookFits)

theorem hall_of_test {sent notices : Array OracleNotice} (h : noticesFitB sent = true)
    (hn : notices = sent) {n : Nat} (hk : n = notices.size - 1) :
    ∀ i, i < n → ∃ nt, notices[i]? = some nt ∧ nt.shape.answers ≠ 0 ∧
      0 < nt.shape.mainRows + nt.shape.maskRows := by
  subst hn hk
  intro i hi
  have e := List.all_eq_true.1 h i (List.mem_range.2 hi)
  cases hx : notices[i]? with
  | none => simp [hx] at e
  | some nt =>
    rw [hx] at e
    simp only [Option.any_some, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at e
    exact ⟨nt, rfl, e.1, e.2⟩

/-- **From two tests on the list of rounds and facts on the state in front.** -/
theorem held_of_tests {N : Numbers} {m : Nat} {pIn : Option Place} {codes : Codes}
    {sent : Array OracleNotice} (hT : sentFitB N m pIn codes sent = true)
    (hA : noticesFitB sent = true) {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok s') (hb : bookAt N pIn s = true)
    (hB : BookFits s.book) (hS : SeedReads) {n₀ : Nat} (hF : Fence p sent codes n₀ s)
    (hI : smpHeld s.st s.book N.index.1 N.index.2 = true) :
    ∀ q ∈ N.index :: N.sent m 0, smpHeld s'.st s'.book q.1 q.2 = true := by
  obtain ⟨x, lay, f, hl, _, _⟩ := yes_seated h
  exact held_behind h hB hS (frontAt_of f) hl
    (sent_of_test hT hb (hF x f).1 (hF x f).2.1 hl rfl) (hall_of_test hA (hF x f).1 rfl) hI

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.hall_of_test
#print axioms VerifiableInference.Desc.First.K2.held_of_tests
