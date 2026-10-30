--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStartThird.lean: THE START OF THE KEY FILE's THIRD CHAIN RETURNS, and what it returns, from
named clauses on the first and the shared chain's last states. The start is a function of the IOP as
written in Lean (below: the description), between two chains: no round, no part of a prover. It
reads nothing of the instance. Statements and proofs, by unfolding. One step of the verifier's:
NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on what a view shows.

What is shown.
  `Start₃ codes S s₁ s₂ l`: ALL THAT THE START ASKS, clause by clause. On public values alone: the
    shape is lawful at the codes; it does not split the row (Dot). On the first chain's last state:
    its claim l is there; a mask's number is named just where the shape sends masks ahead; the three
    numbers (W, the own group, the mask) pass the library's `numbersOk`: shapes, codes, membership
    and flags; its statement's codes are the public ones; it has received as many roots as its book
    has trees. On the shared chain's last state: every group's test has begun and every sampled
    message is in a group (`K14.tested`); its statement's codes are the public ones.
  `thirdFirst s₁ s₂ l`: the state that the start returns: the first chain's statement and book as
    they are; no root received; the three numbers; the two ends at hand; the first own tree's
    number. `thirdFirst_st`, `thirdFirst_listed`: so `Listed` (E2E/KeyListed.lean) passes from the
    first chain's last statement to the third chain's first.
  **`start₃_passes`**: under `Start₃`, at the description `keyFileDescription X N P` and its own codes and
    shape: the start returns `thirdFirst s₁ s₂ l`, at every instance.

No field value is tested: of the claim the row weights are handed on; the shared point is handed on.

Limits.
- `Start₃` restates the start's own tests. That the last states of a run meet it is not shown.
  `K14.tested`: E2E/KeyEnds.lean's `tested_of_end₂`. The library's tests on the first chain's
  book-keeping hold no message's SHAPE and no group's CODE, which `numbersOk` reads.
- A member of `Start₃`, at the full size's shapes and codes: E2E/KeyStartMember.lean.


-/
import E2E.KeyProtocolOverDescription
import E2E.KeyListed
import Johnson.Desc.Key.Desc

set_option autoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Key (FirstState)
open VerifiableInference.Desc.Third (S₃ numbersOk plainArm)

/-- What the start takes of the first chain's last state, at the claim l. -/
def firstOutOf (s₁ : FirstState) (l : LinFirst) : VerifiableInference.Desc.Third.FirstOut :=
  { st := s₁.d.st, book := s₁.d.book, roots := s₁.d.roots
    g := (VerifiableInference.Desc.Key.rowOfLinClaim l.claim).g, w := l.w, own := l.own
    mask := l.mask }

/-- **All that the third chain's start asks.** -/
structure Start₃ (codes : Codes) (S : LinShape) (s₁ : FirstState) (s₂ : _root_.Desc.K14.St)
    (l : LinFirst) : Prop where
  lawful : (codes.lengthsOk && linOk codes S) = true
  arm : plainArm S = true
  claim : s₁.lin = some l
  ahead : l.mask.isSome = S.masksAhead
  numbers : numbersOk S (firstOutOf s₁ l) = true
  codes₁ : s₁.d.st.codes = codes
  roots : s₁.d.roots = s₁.d.book.trees.size
  tested : _root_.Desc.K14.tested s₂ = true
  codes₂ : s₂.st.codes = codes

/-- The state that the start returns. -/
def thirdFirst (s₁ : FirstState) (s₂ : _root_.Desc.K14.St) (l : LinFirst) : S₃ :=
  { st := s₁.d.st, book := s₁.d.book, roots := 0
    loc :=
      { w := l.w, own := l.own, mask := l.mask
        border := some
          { g := (VerifiableInference.Desc.Key.rowOfLinClaim l.claim).g
            shared :=
              { st := s₂.st, book := s₂.book, psi := s₂.loc.psiSh, omega := s₂.loc.oOmega } }
        omega := noId, firstTree := s₁.d.roots + 1 } }

/-- It holds the first chain's last statement as it is: by unfolding. -/
theorem thirdFirst_st (s₁ : FirstState) (s₂ : _root_.Desc.K14.St) (l : LinFirst) :
    (thirdFirst s₁ s₂ l).st = s₁.d.st := rfl

/-- So it has the property that every sub-protocol of the three chains keeps (E2E/KeyListed.lean)
where the first chain's last statement has it. -/
theorem thirdFirst_listed (s₁ : FirstState) (s₂ : _root_.Desc.K14.St) (l : LinFirst)
    (h : Listed s₁.d.st) : Listed (thirdFirst s₁ s₂ l).st := h

/-- **The start returns.** -/
theorem start₃_passes (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) (x : KeyInst) (s₁ : FirstState)
    (s₂ : _root_.Desc.K14.St) (l : LinFirst)
    (h : Start₃ X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape s₁ s₂ l) :
    (keyFileDescription X N P).start₃ x s₁ s₂ = .ok (thirdFirst s₁ s₂ l) := by
  show (do
    let l ← VerifiableInference.Desc.named "the first chain's end names no W" s₁.lin
    let e₂ ← VerifiableInference.Desc.named "the shared chain's end: something is untested"
      (_root_.Desc.K14.ended s₂)
    VerifiableInference.Desc.Third.start₃E X.chains.made.sized.key.codes
      X.chains.made.sized.key.once.shape (VerifiableInference.Desc.Key.firstOf s₁).1
      (VerifiableInference.Desc.Key.firstOf s₁).2.1 (VerifiableInference.Desc.Key.firstOf s₁).2.2.1
      l.w l.own l.mask (VerifiableInference.Desc.Key.firstOf s₁).2.2.2
      (VerifiableInference.Desc.Third.sharedOfEnd e₂) : Except String S₃) = _
  have e1 : _root_.Desc.K14.ended s₂ = some
      { st := s₂.st, book := s₂.book
        lin := { psi := s₂.loc.psiSh, zeta := s₂.loc.zFd, u := s₂.loc.oU, omega := s₂.loc.oOmega,
                 split := s₂.loc.oSp, groupU := s₂.loc.gU, groupOmega := s₂.loc.gOmega,
                 mask := s₂.loc.firstMask } } := by
    unfold _root_.Desc.K14.ended
    simp only [h.tested, if_true]
  have e2 : (VerifiableInference.Desc.Key.firstOf s₁).2.2.2 =
      [VerifiableInference.Desc.Key.rowOfLinClaim l.claim] := by
    unfold VerifiableInference.Desc.Key.firstOf
    simp only [h.claim]
  have e3 : numbersOk X.chains.made.sized.key.once.shape
      { st := s₁.d.st, book := s₁.d.book, roots := s₁.d.roots
        g := (VerifiableInference.Desc.Key.rowOfLinClaim l.claim).g, w := l.w, own := l.own
        mask := l.mask } = true := h.numbers
  have e4 : VerifiableInference.Desc.Third.rootsB s₁.d.roots s₁.d.book = true := by
    unfold VerifiableInference.Desc.Third.rootsB
    rw [h.roots]
    exact beq_self_eq_true _
  rw [h.claim, e1, e2]
  simp only [VerifiableInference.Desc.named, bind, Except.bind,
    VerifiableInference.Desc.Third.start₃E, h.lawful, Bool.not_true, Bool.false_eq_true, if_false,
    VerifiableInference.Desc.Third.firstOutFrom, h.arm, h.ahead, beq_self_eq_true, Bool.and_self,
    if_true, VerifiableInference.Desc.Key.firstOf, e3,
    VerifiableInference.Desc.Third.start₃, VerifiableInference.Desc.Third.sharedOfEnd, h.codes₁,
    h.codes₂, decide_true, e4]
  rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.thirdFirst_st
#print axioms AtPublicFiles.AtFiles.thirdFirst_listed
#print axioms AtPublicFiles.AtFiles.start₃_passes
