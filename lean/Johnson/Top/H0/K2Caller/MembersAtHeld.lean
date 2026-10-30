-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/MembersAtHeld.lean: the code switch (the kind K2): what the test
`membersK2B` (MembersAtK2.lean) gives, WORDED AS THE PREMISES hex, hall AND hN OF `pinJT_kept`
(Johnson/Top/H0/K2Caller/PinKeptJoin.lean), less `KeptFacts`: the typed kept member is a held member
k of the library's choice `plainHd r H` (SlotIs.lean).

Main names:
  `held_of_kept`: each member of r.lo whose number stands in r.kept is a held member.
  `held_of_B`: where the test passes: at every tenant q of kq a member of the table sits, every
    member that sits there is one of those whose pads the row lays and is `Alike` to a held member
    k, at any seats with `SeatsKept` (MembersAtK2.lean); and the members whose pads the row lays
    have different seats.
  `held_at_table`: the same with these members written as the table's own `minePadAt`.
  `held_at_plan`: the same at the composed meaning's term ms := `P5T.msAtR Z rad`, from the test
    `membersPlanB` (MembersAtPlan.lean).
Limits. `KeptFacts` is not touched. The test's value at a real plan is not shown here. Nothing on
soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.MembersAtPlan
import Johnson.Top.H0.K2Caller.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (MemberLists Place)
open VerifiableInference.Desc.Sound (Mem msOf SitsAt Alike seatOf minePadAt)
open VerifiableInference.Desc.First (ModelPart Numbers rowOf)

variable {L : MemberLists} {kq nq : List (ℕ × ℕ)} {r : SwRow}

/-- **A kept member of the typed list is a held member.** -/
theorem held_of_kept (H : r.OK) (i : Fin r.lo.length) (hi : i.val ∈ r.kept) :
    ∃ k : {a // (plainHd r H).cl a}, k.1.1 = i :=
  ⟨⟨⟨i, hi⟩, ⟨by
    have h := H.kept i.val hi
    rw [List.getElem?_eq_getElem i.isLt] at h
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1, hi⟩⟩, rfl⟩

/-- **The table's members at a kept tenant are the held members.** -/
theorem held_of_B (H : r.OK) (h : membersK2B L kq nq r = true)
    (seat : Fin r.lo.length → ℕ × ℕ) (hseat : SeatsKept r kq seat) :
    (∀ q ∈ kq, (∃ x ∈ msOf L, SitsAt x q.1 q.2) ∧
      ∀ x ∈ msOf L, SitsAt x q.1 q.2 →
        x ∈ ((msOf L).filter fun x => kq.contains (x.1.seat x.2)) ∧
        ∃ k : {a // (plainHd r H).cl a}, Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩) ∧
      (((msOf L).filter fun x => kq.contains (x.1.seat x.2)).map seatOf).Nodup := by
  obtain ⟨h1, h2⟩ := kept_of_B H h seat hseat
  refine ⟨fun q hq => ⟨(h1 q hq).1, fun x hx hs => ?_⟩, h2⟩
  obtain ⟨hm, i, hi, hA⟩ := (h1 q hq).2 x hx hs
  obtain ⟨k, rfl⟩ := held_of_kept H i hi
  exact ⟨hm, k, hA⟩

/-- The same at the table's own letters. -/
theorem held_at_table (H : r.OK) (N : Numbers) (links : List ModelPart) (p : Place) (hk : p.kind = .K2)
    (hl : (rowOf links p).lays = true)
    (h : membersK2B L (N.keptOf (p.link.getD links.length - 1)) nq r = true)
    (seat : Fin r.lo.length → ℕ × ℕ)
    (hseat : SeatsKept r (N.keptOf (p.link.getD links.length - 1)) seat) :
    (∀ q ∈ N.keptOf (p.link.getD links.length - 1), (∃ x ∈ msOf L, SitsAt x q.1 q.2) ∧
      ∀ x ∈ msOf L, SitsAt x q.1 q.2 → x ∈ minePadAt (msOf L) N links p ∧
        ∃ k : {a // (plainHd r H).cl a}, Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩) ∧
      ((minePadAt (msOf L) N links p).map seatOf).Nodup := by
  obtain ⟨h1, h2⟩ := kept_at_table H N links p hk hl h seat hseat
  refine ⟨fun q hq => ⟨(h1 q hq).1, fun x hx hs => ?_⟩, h2⟩
  obtain ⟨hm, i, hi, hA⟩ := (h1 q hq).2 x hx hs
  obtain ⟨k, rfl⟩ := held_of_kept H i hi
  exact ⟨hm, k, hA⟩

/-- The same at the composed meaning's term for the table's members. -/
theorem held_at_plan {Z : ProofFile.Pub} {rad : ℕ → ℕ → ℕ} {N : Numbers} (H : r.OK) (links : List ModelPart)
    (p : Place) (hk : p.kind = .K2) (hl : (rowOf links p).lays = true)
    (h : membersPlanB Z rad N (p.link.getD links.length) r = true)
    (seat : Fin r.lo.length → ℕ × ℕ)
    (hseat : SeatsKept r (N.keptOf (p.link.getD links.length - 1)) seat) :
    (∀ q ∈ N.keptOf (p.link.getD links.length - 1),
      (∃ x ∈ P5T.msAtR Z rad, SitsAt x q.1 q.2) ∧
      ∀ x ∈ P5T.msAtR Z rad, SitsAt x q.1 q.2 → x ∈ minePadAt (P5T.msAtR Z rad) N links p ∧
        ∃ k : {a // (plainHd r H).cl a}, Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩) ∧
      ((minePadAt (P5T.msAtR Z rad) N links p).map seatOf).Nodup :=
  held_at_table H N links p hk hl h seat hseat

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.held_at_plan
#print axioms VerifiableInference.Desc.First.K2Caller.held_of_kept
#print axioms VerifiableInference.Desc.First.K2Caller.held_of_B
#print axioms VerifiableInference.Desc.First.K2Caller.held_at_table
