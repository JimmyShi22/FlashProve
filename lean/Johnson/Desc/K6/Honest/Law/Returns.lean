-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/Returns.lean.
WHAT IT IS NOT. Every statement is CONDITIONAL. THAT A READY STATE (K6Front) IS EVER REACHED IS NOT
SHOWN HERE, nor that the IOP as written in Lean seats the member in the form K6MemberIs, nor that
any rounds pass the step's tests. K6Front is a definition: nothing is claimed of it. No prover's
text is read. Nothing is said of any value that is heard. What an accept leaves of the state as it
was, beside the ledger, is not said here. Nothing on soundness, on completeness or on hiding.
WHAT IT IS. WHEN THE STEP OF THE SUB-PROTOCOL "THE OUTPUT HEAD's OWN ROUNDS" (K6) ACCEPTS, AND WHAT
THE LEDGER BEHIND IS: from facts on the state's own book-keeping fields and the step's own tests on
the rounds' and the columns' form. The decision compares no sent value. It imports library files,
Kinds/Law/K6YesAtMember.lean and K6GivenOfLeft.lean, and ProofFile/Honest/K6/Hears/OfFit.lean, which
reads the verifier's text alone.
  K6Front W m s   the state in front is ready, with room for m slots more behind the hearing.
  zt_of_points    CONDITIONAL on the test on the points: the end of the lookup's point on the
                  positions has lt coordinates. So no test on the plan is spent below.
  k6_hears        CONDITIONAL: a ready state; rounds that pass the step's test on the rounds: the
                  head's letters are read, the hearing returns on the rounds without the sealed
                  digest and uses them up; the ledger behind is well laid, has m free slots left,
                  as many slots as in front, and its next free number has moved on by
                  41 + 8 lt + 4 lPd.
  member_returns  MAIN. CONDITIONAL: the member's form, with hk (the address is not K7's) and hsm
                  (the guard accepts where the reply is as it was); a ready state; the step's tests:
                  the member's step accepts and takes no column; so does its decision at what the
                  step shows it; the ledger behind is as k6_hears says.
  member_returns' the same WITHOUT hk, which is not needed: at every address. hsm is: this is the
                  way up.
WHO IS MEANT TO PAY. K6Front: K6/Honest/Law/FrontOfItems.lean, from what the table's promise says in
front of the member. The member's form: Kinds/Law/K6WayUpAtSeat.lean. The step's tests: whoever
shows what is played.
CALLED: given_of_parts, Came.given_ok, Came.call_get, blockAt_rounds, hears_of_fit, member_yes,
member_yes', K6MemberIs.rounds.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6YesAtMember
import Johnson.Desc.Kinds.Law.K6GivenOfLeft
import Johnson.Desc.ProofFile.Honest.K6.Hears.OfFit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block OpenedColumn Place KindName Claim noDigest roundsFit)
open VerifiableInference.Desc.First (S)
open OnBytes.Model (Fork)
open Norm (lt lPd)

/-- **THE STATE IN FRONT OF K6's MEMBER IS READY**, with room for m slots more behind the hearing:
no mark of failure; it stands in the head's link, opened, with what the lookup left; its own test on
the request accepts; the lookup's points are laid, a token is heard, and each call's key point has
the coordinates that the head's text asks and ends as the lookup's point does (the three tests under
which the head's letters are read: given_of_parts, Kinds/Law/K6GivenOfLeft.lean); its ledger has its
three arrays at the number of slots; 41 + 8 lt + 4 lPd + m more slots are there, and every slot from
the next on is free. A definition: a premise's form. Nothing is claimed of it. -/
structure K6Front (W : OnBytes.Model.Verify.Public) (m : Nat) (s : S) : Prop where
  clean : s.failed = none
  open_ : HeadOpen s
  start : startOk W s = true
  letters : ∃ (z : Point × (Nat → Point)) (y : Nat),
    (seatAt W.hS (readsOf W)).lookup s = some z ∧
      Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y ∧
      @PointsOk (parOf W.hS (workOf W)).sizes (parOf W.hS (workOf W)).floor z.1 z.2
  laid : WellLaid ((seatAt W.hS (readsOf W)).ledger s)
  room : letI : Sizes := (parOf W.hS (workOf W)).sizes
    Fresh ((seatAt W.hS (readsOf W)).ledger s) (41 + 8 * lt + 4 * lPd + m)

/-- Under the test on the points, the end of the lookup's point on the positions has lt coordinates:
no test on the plan is spent. (Kinds/Law/WeightTwinAt.lean's zt_size_at has the same from the plan's
test.) -/
theorem zt_of_points [Sizes] (floor : Nat) (zx : Point) (zk : Nat → Point)
    (hP : PointsOk floor zx zk) : (zx.last lt).size = lt := by
  obtain ⟨p1, p2⟩ := hP 0 _ (Came.call_get (by decide))
  have h := congrArg Array.size p2
  unfold Point.last at h ⊢
  simp only [Array.size_extract] at h ⊢
  omega

/-- THE HEARING RETURNS AT A READY STATE, on rounds that pass the step's own test. CONDITIONAL. -/
theorem k6_hears (W : OnBytes.Model.Verify.Public) (l : Nat) {m : Nat} {s : S}
    (R : K6Front W m s) (rs : List Fmt.RoundView)
    (hf : roundsFit (blockAt W.hS (readsOf W) (workOf W) l).rounds rs = true) :
    ∃ (g : Given) (H : HeardAll) (G : Fork),
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g ∧
      hear ((seatAt W.hS (readsOf W)).ledger s) (rs.map noDigest) = some (H, G, []) ∧
      WellLaid G ∧ Fresh G m ∧
      (letI : Sizes := (parOf W.hS (workOf W)).sizes
       G.next = ((seatAt W.hS (readsOf W)).ledger s).next + (41 + 8 * lt + 4 * lPd)) ∧
      G.ns = ((seatAt W.hS (readsOf W)).ledger s).ns := by
  obtain ⟨z, y, hz, hy, hP⟩ := R.letters
  obtain ⟨g, hg⟩ := given_of_parts _ _ s z y hz hy hP
  obtain ⟨z', y', hz', _, _, rfl⟩ := Came.given_ok _ _ s g hg
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  letI : Sizes := (parOf W.hS (workOf W)).sizes
  letI : Policy := (parOf W.hS (workOf W)).policy
  letI : Request := (seatAt W.hS (readsOf W)).request s
  letI : Token := ⟨y'⟩
  letI : FinalNorm.In := (fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).norm
  letI : In := (fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).head
  have hzt : (FinalNorm.zt).size = lt := zt_of_points _ _ _ hP
  rw [blockAt_rounds] at hf
  obtain ⟨H, G, hh, w1, w2, w3, w4, _⟩ := ProofFile.Honest.K6.Hears.hears_of_fit
    (parOf W.hS (workOf W)).work R.laid R.room hzt rs hf
  exact ⟨_, H, G, hg, hh, w1, w2, w3, w4⟩

/-- **THE "RETURNS" LAW, AT THE MEMBER AS THE IOP AS WRITTEN IN LEAN SEATS IT.** CONDITIONAL: the
member's form; the state in front is ready; the step's own tests on rounds and columns. No premise
is a routine's return, none speaks of a value that is sent, and no test on the plan is spent. -/
theorem member_returns {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool}
    {a : Place} {b : Block S Claim} (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true)
    (ft : Nat) {m : Nat} {s : S} (R : K6Front W m s) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : b.Fits ft rs cols) :
    ∃ (s' : S) (G : Fork), b.step ft s rs cols = .ok (s', 0) ∧
      b.decide s (rs.map noDigest) (b.shown ft rs cols) = .ok s' ∧
      (seatAt W.hS (readsOf W)).ledger s' = G ∧ WellLaid G ∧ Fresh G m ∧
      (letI : Sizes := (parOf W.hS (workOf W)).sizes
       G.next = ((seatAt W.hS (readsOf W)).ledger s).next + (41 + 8 * lt + 4 * lPd)) ∧
      G.ns = ((seatAt W.hS (readsOf W)).ledger s).ns := by
  obtain ⟨g, H, G, hg, hh, w1, w2, w3, w4⟩ :=
    k6_hears W l R rs (by rw [← M.rounds]; exact hF.1)
  obtain ⟨s', hs, hd, hL⟩ :=
    member_yes M hk hsm ft s rs cols H G hF R.clean R.open_ R.start g hg hh
  exact ⟨s', G, hs, hd, hL, w1, w2, w3, w4⟩

/-- `member_returns` without hk: at every address. CONDITIONAL, as that. -/
theorem member_returns' {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool}
    {a : Place} {b : Block S Claim} (M : K6MemberIs W l same a b)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true)
    (ft : Nat) {m : Nat} {s : S} (R : K6Front W m s) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : b.Fits ft rs cols) :
    ∃ (s' : S) (G : Fork), b.step ft s rs cols = .ok (s', 0) ∧
      b.decide s (rs.map noDigest) (b.shown ft rs cols) = .ok s' ∧
      (seatAt W.hS (readsOf W)).ledger s' = G ∧ WellLaid G ∧ Fresh G m ∧
      (letI : Sizes := (parOf W.hS (workOf W)).sizes
       G.next = ((seatAt W.hS (readsOf W)).ledger s).next + (41 + 8 * lt + 4 * lPd)) ∧
      G.ns = ((seatAt W.hS (readsOf W)).ledger s).ns := by
  obtain ⟨g, H, G, hg, hh, w1, w2, w3, w4⟩ :=
    k6_hears W l R rs (by rw [← M.rounds]; exact hF.1)
  obtain ⟨s', hs, hd, hL⟩ :=
    member_yes' M hsm ft s rs cols H G hF R.clean R.open_ R.start g hg hh
  exact ⟨s', G, hs, hd, hL, w1, w2, w3, w4⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.zt_of_points
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_hears
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_returns
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_returns'
