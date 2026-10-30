-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchEndsVals.lean: THE CODE SWITCH's LAST TWO PLACES ("H:2", "F:1"; kind
K2): THE TESTS ON THE STATE ITSELF OF THE LATER PIECES, BROUGHT TO THE STATE IN FRONT OF THE MEMBER,
AND ONE OF THEM MADE SMALLER. Four general laws; nothing is evaluated.

Why. Each of the two places is several decisions in a row. A table of tests on values is typed at
the state in front of the whole member; two of the pieces' tests stand at a state between.

Main names.
* `headQuietV_behind`: what the quiet step behind the head's switch asks of the state itself
  (`headQuietV`, Johnson/Desc/First/Shape/SwitchEndsReturns.lean) says the same behind the switch as
  in front of it: it reads the reply's seat and the request's words, which the switch leaves.
* `headQuietV_of_covered`: OF ITS THREE CLAUSES THE SECOND GIVES THE OTHER TWO: where the covered
  positions can be made (`S.covered`, Johnson/Desc/First/State.lean), `headQuietV` accepts:
  `S.covered` returns only at a heard reply that is a natural number below the vocabulary's size,
  laid as `ofNat` lays one; and it lays its four arrays with T entries each, behind its own test
  that the request has T + 2 words.
* `headQuietV_eq`: so `headQuietV P s` is the one test "`S.covered` returns at s".
* `finOnesV_behind`: behind the finish's quiet front the switch's one test on values (`finOnesV`,
  Johnson/Desc/First/Shape/SwitchArmsB.lean) is `onesV` (SwitchFrontFits.lean) at the statement and
  the carried rows in front of it: the quiet front adds an empty group and leaves the messages and
  the frame's rows.

Limits. Equations and one implication between tests: that a test accepts at any state is not shown.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.SwitchEndsReturns
import Johnson.Desc.First.Shape.SwitchArmsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2 (P2 HeadPar decideWith finishFrontQ sizedOk)

/-- **Behind the head's switch the quiet step's tests on values say what they say in front.** -/
theorem headQuietV_behind {p : P2} {HP : HeadPar} {s m : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .head)
    (h : decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok m) :
    headQuietV HP m = headQuietV HP s := by
  obtain ⟨r₁, r₂, a, G, w, roots, -, R⟩ := First.K2.head_inv hp h
  rw [R.hOut]
  rfl

/-- **Where the covered positions can be made, all three clauses hold.** -/
theorem headQuietV_of_covered {P : HeadPar} {s : S} {cov : Head.Covered}
    (h : s.covered P.T P.V = .ok cov) : headQuietV P s = true := by
  unfold headQuietV
  rw [h]
  unfold S.covered at h
  cases hy : s.replyTok? with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    unfold S.replyTok? at hy
    obtain ⟨g, hg, hy⟩ := Option.bind_eq_some_iff.1 hy
    split at hy
    · rename_i hgo
      obtain rfl := Option.some.inj hy
      have eg : ofNat g.c0.toNat = g := eq_of_beq hgo
      unfold S.coveredAt at h
      dsimp only at h
      split at h
      · cases h
      · rename_i h1
        split at h
        · cases h
        · rename_i h2
          split at h
          · cases h
          · split at h
            · cases h
            · cases h
              rw [hg]
              have hV : g.c0.toNat < P.V := by simpa using h1
              have hsz : s.req.size = P.T + 2 := by simpa using h2
              have c1 : g.c1 = 0 := by rw [← eg]; rfl
              have c2 : g.c2 = 0 := by rw [← eg]; rfl
              simp [sizedOk, c1, c2, hV, hsz]
    · cases hy

/-- **So the three clauses are one test: the covered positions can be made.** -/
theorem headQuietV_eq (P : HeadPar) (s : S) :
    headQuietV P s = (s.covered P.T P.V).toOption.isSome := by
  cases h : s.covered P.T P.V with
  | ok cov =>
    rw [headQuietV_of_covered h]
    rfl
  | error e =>
    unfold headQuietV
    rw [h, Bool.and_false]
    rfl

/-- **Behind the finish's quiet front the switch's test on values is the one in front.** -/
theorem finOnesV_behind {s m : S} (h : finishFrontQ s = .ok m) :
    finOnesV m = onesV s.st s.check.frame.rows := by
  obtain ⟨G, x, s₁, a, A⟩ := (First.K2.finishFrontQ_iff s m).1 h
  obtain ⟨G', S', g, F⟩ := (_root_.Tw.K2.finishFront_iff _ _ _).1 A.front
  have e : S'.oracles = s.st.oracles := by
    have hN := F.opened
    unfold _root_.Tw.K2.newGroupG at hN
    split at hN
    · rename_i g' d hd
      cases hN
      unfold Ground.newGroupP at hd
      split at hd
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hd)
        rfl
      · cases hd
    · cases hN
  rw [A.out, F.out]
  show onesV S' s.check.frame.rows = _
  unfold onesV
  rw [e]

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.headQuietV_behind
#print axioms VerifiableInference.Desc.First.Shape.headQuietV_of_covered
#print axioms VerifiableInference.Desc.First.Shape.headQuietV_eq
#print axioms VerifiableInference.Desc.First.Shape.finOnesV_behind
