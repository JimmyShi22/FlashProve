--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/K2Caller/CarryOverShut.lean: the code switch: «carry m» (CarryClosed.lean's
carryAtZ) RIDES OVER «THE SEGMENT IS SHUT» AND OVER A «cleared» THAT LEAVES NO ROW, AT
ALL THREE SORTS OF THE PLACE AT WHICH IT IS SPENT (a link · the head · the finish): rows (a) and
(b), without a row, of the item's span. OUR OWN DEFINITION's LEMMAS.
  carry_of_door  the sentence reads of the state what the way in makes of it, and nothing else
  rest_shut    across the shutting (s.putLink (closed L L.check.frame): First/Batch/Place.lean's
               «K9: the segment is shut») rest IS ONE, OUTRIGHT: putLink writes where the chain
               stands alone; closed turns of the link's copy of the state of the calls the flag
               alone; rest lays that flag down itself
  doorZ_shut · carry_over_shut  so the way in, and the sentence, are one
  rest_left · doorZ_left · carry_over_left  the same across S.leaveLink (what «cleared» does where
               it leaves no row), where a link is open and the live copy's flag is down; at the
               head's sort: where the state does not stand in the head
  shut_facts   behind the shutting these two premises hold
WHY IT MATTERS. With the live copy taken back as it is, the sentence is false just here at the two
items spent at the head and at the finish. With rest the riding over the shutting is an equation.
LIMITS. NOT HERE: a «cleared» that leaves a row (it turns one message's ledger in the statement: the
fronts are alike, not one: carryRow_like) · «laid» (it hands the state on as it
is) · the sub-protocol that enters the head (CarryOverReply.lean) · the ties themselves. That the
sentence can be met is not shown. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.CarryClosed
import Johnson.Desc.First.Batch.Text

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S)
open OnBytes.Model (LinkCtx)

/-- **The sentence reads of the state what the way in makes of it, and nothing else.** -/
theorem carry_of_door {P W : Type} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ) (a b : P × S) (y : Strs)
    (w w' : W) (h : doorZ Z m a.2 = doorZ Z m b.2) :
    carryAtZ Z lay m a y w ↔ carryAtZ Z lay m b y w' := by
  rw [carryAtZ_iff, carryAtZ_iff, h]

/-- **ACROSS «THE SEGMENT IS SHUT» rest IS ONE.** -/
theorem rest_shut {s : S} {L : LinkCtx} (hL : s.link? = some L) :
    rest (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) = rest s := by
  unfold S.link? at hL
  cases hq : s.here with
  | lay a =>
    rw [hq] at hL
    obtain rfl : a.L = L := Option.some.inj hL
    simp only [rest, S.putLink, S.inLink, S.fork?, S.live, S.link?, hq]
    rfl
  | att a =>
    rw [hq] at hL
    obtain rfl : a.L = L := Option.some.inj hL
    simp only [rest, S.putLink, S.inLink, S.fork?, S.live, S.link?, hq]
    rfl
  | head a =>
    rw [hq] at hL
    cases ho : a.opened with
    | false => simp [ho] at hL
    | true =>
      simp only [ho, if_true] at hL
      obtain rfl : a.L = L := Option.some.inj hL
      simp only [rest, S.putLink, S.inLink, S.fork?, S.live, S.link?, hq, ho, if_true]
      rfl
  | between => rw [hq] at hL; cases hL
  | fin a => rw [hq] at hL; cases hL
  | mem a => rw [hq] at hL; cases hL

/-- So is the way in, at every sort of place. -/
theorem doorZ_shut (Z : ProofFile.Pub) (m : ℕ) {s : S} {L : LinkCtx} (hL : s.link? = some L) :
    doorZ Z m (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) = doorZ Z m s := by
  unfold doorZ
  rw [rest_shut hL]
  cases (ProofFile.pAtK2 Z m).stands with
  | link => rfl
  | finish => rfl
  | head =>
    unfold S.link? at hL
    cases hq : s.here with
    | lay a => simp only [S.putLink, hq]
    | att a => simp only [S.putLink, hq]
    | head a =>
      rw [hq] at hL
      cases ho : a.opened with
      | false => simp [ho] at hL
      | true => simp only [S.putLink, hq, ho, if_true]
    | between => rw [hq] at hL; cases hL
    | fin a => rw [hq] at hL; cases hL
    | mem a => rw [hq] at hL; cases hL

/-- **«carry m» SAYS THE SAME IN FRONT OF AND BEHIND «THE SEGMENT IS SHUT»**, wherever it is
spent. -/
theorem carry_over_shut {P W : Type} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ) (z z' : P) {s : S}
    {L : LinkCtx} (hL : s.link? = some L) (y : Strs) (w w' : W) :
    carryAtZ Z lay m (z, s) y w ↔
      carryAtZ Z lay m (z', s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) y w' :=
  carry_of_door Z lay m _ _ y w w' (doorZ_shut Z m hL).symm

/-- **ACROSS THE LEAVING OF A LINK rest IS ONE**, where the live copy's flag is down (as it is
behind the shutting). -/
theorem rest_left {s : S} (hi : s.inLink = true) (hf : s.live.inLink = false) :
    rest s.leaveLink = rest s := by
  have e : ({ s.live with inLink := false } : OnBytes.Model.ChainCheck) = s.live := by
    cases hc : s.live
    rw [hc] at hf
    simp only at hf
    subst hf
    rfl
  have hl : s.leaveLink = { s with check := s.live, here := .between } := by
    unfold S.leaveLink
    rw [if_pos hi]
  rw [hl, rest_out _ rfl]
  unfold rest
  rw [if_pos hi, e]

/-- So is the way in: at the head's sort, where the state does not stand in the head. -/
theorem doorZ_left (Z : ProofFile.Pub) (m : ℕ) {s : S} (hi : s.inLink = true)
    (hf : s.live.inLink = false)
    (hh : (ProofFile.pAtK2 Z m).stands = .head → ∀ a, s.here ≠ .head a) :
    doorZ Z m s.leaveLink = doorZ Z m s := by
  have hb : s.leaveLink.here = .between := by
    unfold S.leaveLink
    rw [if_pos hi]
  unfold doorZ
  rw [rest_left hi hf]
  cases hs : (ProofFile.pAtK2 Z m).stands with
  | link => rfl
  | finish => rfl
  | head =>
    simp only [hb]
    cases hq : s.here with
    | head a => exact absurd hq (hh hs a)
    | lay a => rfl
    | att a => rfl
    | between => rfl
    | fin a => rfl
    | mem a => rfl

/-- **«carry m» SAYS THE SAME IN FRONT OF AND BEHIND A «cleared» THAT LEAVES NO ROW.** -/
theorem carry_over_left {P W : Type} (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ) (z z' : P) {s : S}
    (hi : s.inLink = true) (hf : s.live.inLink = false)
    (hh : (ProofFile.pAtK2 Z m).stands = .head → ∀ a, s.here ≠ .head a) (y : Strs) (w w' : W) :
    carryAtZ Z lay m (z, s) y w ↔ carryAtZ Z lay m (z', s.leaveLink) y w' :=
  carry_of_door Z lay m _ _ y w w' (doorZ_left Z m hi hf hh).symm

/-- Behind the shutting a link is still open and the live copy's flag is down: rest_left's two
premises. -/
theorem shut_facts {s : S} {L : LinkCtx} (hL : s.link? = some L) :
    (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)).inLink = true ∧
      (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)).live.inLink = false := by
  unfold S.link? at hL
  cases hq : s.here with
  | lay a =>
    simp [S.putLink, S.inLink, S.fork?, S.live, S.link?, hq, VerifiableInference.Desc.K9.closed]
  | att a =>
    simp [S.putLink, S.inLink, S.fork?, S.live, S.link?, hq, VerifiableInference.Desc.K9.closed]
  | head a =>
    rw [hq] at hL
    cases ho : a.opened with
    | false => simp [ho] at hL
    | true =>
      simp [S.putLink, S.inLink, S.fork?, S.live, S.link?, hq, ho,
        VerifiableInference.Desc.K9.closed]
  | between => rw [hq] at hL; cases hL
  | fin a => rw [hq] at hL; cases hL
  | mem a => rw [hq] at hL; cases hL

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.shut_facts

#print axioms VerifiableInference.Desc.First.K2Caller.carry_over_shut
#print axioms VerifiableInference.Desc.First.K2Caller.carry_over_left

#print axioms VerifiableInference.Desc.First.K2Caller.carry_of_door
#print axioms VerifiableInference.Desc.First.K2Caller.rest_shut
