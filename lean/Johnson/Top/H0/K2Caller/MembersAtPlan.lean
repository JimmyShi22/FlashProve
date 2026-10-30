-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/MembersAtPlan.lean: the code switch (the kind K2): the test `membersK2B`
(MembersAtK2.lean) AT THE TERMS OF THE COMPOSED MEANING's PARAMETERS: the table's members
ms := `P5T.msAtR Z rad` (Johnson/P5T/MembersByMake.lean), and the table's numbers N.

Main names:
  `membersPlanB Z rad N l r`: THE TEST at the switch into group l: at the plain lists of which
    `P5T.msAtR Z rad` is made, the tenants `N.keptOf (l - 1)` and `N.sent l 0`, and the numbers r.
  `kept_at_plan`: where it passes, at a place p of the kind K2 whose row lays, with
    l := p.link.getD links.length: at every tenant of `N.keptOf (l - 1)` a member of ms sits; every
    member of ms that sits there is one of the table's `minePadAt` and is `Alike` to a kept member
    of r.lo, at any seats with `SeatsKept`; and the members of `minePadAt` have different seats.
    (With the kept member as a held member of the library's choice: MembersAtHeld.lean.)
  `new_at_plan`: member by member: every member of ms that sits at the seat of the member i of the
    typed new sending r.l (`N.sent l 0` by place) is `Alike` to that member; these seats are just
    the tenants `N.sent l 0`; at each a member of ms sits.
Limits. The test's value is a premise. At the stored full-size example's plan (`VerifierAndGoals.storedPublicFiles`)
Lean's evaluator gave "true" at all 25 code switches, and "false" at all 25 in two negative tests
(the sheet Johnson/Loose/H2K2/MembersAtFull.lean [not in this library; so here read: not tested in
this library]): that is evidence and no proof, and it is of that
plan alone.
Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.MembersAtK2
import Johnson.P5T.MembersByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound (SitsAt Alike seatOf minePadAt seatsByPlace)
open VerifiableInference.Desc.First (ModelPart Numbers rowOf)

/-- **THE TEST, at the composed meaning's terms.** -/
def membersPlanB (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (N : Numbers) (l : ℕ) (r : SwRow) : Bool :=
  membersK2B (P5T.memberListsR Z.made.proof.1.sends.length rad (P5T.planSeats Z Z.D.1))
    (N.keptOf (l - 1)) (N.sent l 0) r

variable {Z : ProofFile.Pub} {rad : ℕ → ℕ → ℕ} {N : Numbers} {r : SwRow}

/-- **The table's members at a kept tenant are the typed kept members.** -/
theorem kept_at_plan (H : r.OK) (links : List ModelPart) (p : Place) (hk : p.kind = .K2)
    (hl : (rowOf links p).lays = true)
    (h : membersPlanB Z rad N (p.link.getD links.length) r = true)
    (seat : Fin r.lo.length → ℕ × ℕ)
    (hseat : SeatsKept r (N.keptOf (p.link.getD links.length - 1)) seat) :
    (∀ q ∈ N.keptOf (p.link.getD links.length - 1),
      (∃ x ∈ P5T.msAtR Z rad, SitsAt x q.1 q.2) ∧
      ∀ x ∈ P5T.msAtR Z rad, SitsAt x q.1 q.2 → x ∈ minePadAt (P5T.msAtR Z rad) N links p ∧
        ∃ i : Fin r.lo.length, i.val ∈ r.kept ∧ Alike x ⟨⟨r.lo, seat⟩, i⟩) ∧
      ((minePadAt (P5T.msAtR Z rad) N links p).map seatOf).Nodup :=
  kept_at_table H N links p hk hl h seat hseat

/-- **Whoever of the table's members sits at the seat of the member i of the typed new sending is
alike to that member**; these seats are just the tenants `N.sent l 0`; at each a member sits. -/
theorem new_at_plan (l : ℕ) (h : membersPlanB Z rad N l r = true) :
    (∀ i : Fin r.l.length, ∀ x ∈ P5T.msAtR Z rad,
      SitsAt x (seatsByPlace (N.sent l 0) r.l.length i).1
          (seatsByPlace (N.sent l 0) r.l.length i).2 →
        Alike x ⟨⟨r.l, seatsByPlace (N.sent l 0) r.l.length⟩, i⟩) ∧
      (∀ q ∈ N.sent l 0, ∃ i : Fin r.l.length, seatsByPlace (N.sent l 0) r.l.length i = q) ∧
      (∀ i : Fin r.l.length, seatsByPlace (N.sent l 0) r.l.length i ∈ N.sent l 0) ∧
      ∀ q ∈ N.sent l 0, ∃ x ∈ P5T.msAtR Z rad, SitsAt x q.1 q.2 :=
  new_of_B h

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.kept_at_plan
#print axioms VerifiableInference.Desc.First.K2Caller.new_at_plan
