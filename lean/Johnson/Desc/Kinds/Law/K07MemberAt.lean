-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07MemberAt.lean: A TOY FOR THE ROW K07_law AT THE OUTPUT HEAD's REAL SEAT
(Johnson/Stored/HeadSeatAt.lean: Head.seatAt, at the first chain's record S) AND AT THE HEAD's
PUBLIC NUMBERS OF THE STORED FULL-SIZE EXAMPLE. Beside the toy of Law/K07Member.lean.

WHAT IT IS NOT. NOT A MEMBER AT THE RELEASE: THE FOUR RECORDS ARE LAID BY HAND, NOT BY A RUN: blank ones; what the
lookup heard (its point zx of 27 coordinates, one coordinate zy, the six key points) is made up, in the shape in which the lookup lays it (a tail
of zy, then zx) and of the sizes that given's third test asks. No file is read IN LEAN's KERNEL: THAT hR IS THE hS OF
THE PUBLIC RECORD WHICH THE VERIFIER's publicOf MAKES OF THE STORED FILES (VerifierAndGoals.storedPublicFiles) IS HELD BY AN EVALUATION
ALONE (a trial sheet, field by field and by the two prints), BY NO THEOREM; hR_full (nine of its fields are FullH's) is a theorem. The
request's words are not laid (the law's T, r, e are free letters: 1024, 0, 1024
here). The law is over one seat, and so is this toy: the next token's block is
seated at out.reply, which the head's seat takes by name (Stored/ReplySeatAt.lean:
seatAt); what neither half of the law says: K07Statement.lean. Nothing on soundness.




WHAT IT IS.
  K07MemberAt | k07MemberAt   K07Member's clauses with S := the first chain's record, L := Head.seatAt hR 0, p := Head.parOf hR 0: the seat
        gives back what is laid AT EVERY RECORD · the next token's decision returns from s1 (inside the head's link, NOT YET
        OPENED, no reply) to s1', at the LAST token of the vocabulary, 202,047 · at sH (the link opened, the lookup heard, that
        reply) the head's letters are there: given returns: its third test passes at key points of 28 28 28 27 27 27
        coordinates · at sE (between links, that reply) the last test's part says yes at asked = 202,047, T = e = 1024.
  k07MemberAt_member   it is a K07Member: so k07Member_spends applies.
  TEETH: refuses_at_V: the same decision refuses the element 202,048 · fin_other: the last test's part says no at asked = 202,046.

-/
import Johnson.Desc.Kinds.Law.K07Member
import Johnson.Stored.HeadSeatAt
import Johnson.Road.HeadPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open VerifiableInference.Desc.First (S)

namespace K07Real

/-- The head's public numbers, as the verifier's publicOf prints them of the stored full-size example's files. -/
def hR : OnBytes.Model.Head.Shape :=
  { lt := 10, la := 16, d := 5120, lPd := 13, V := 202048, MF := 44, KF := 30, epsF := 53687,
    toksrc := 1, wbEmb := 21, wbHead := 13, clipC := 256, theta := 256, cap := 0, logS := 15,
    digSh := 8, tabS := 4, famF := 24, lmhf := 16, NHf := 4, lmhd := 14, lmhr := 13, lmbH := 15,
    iotaH := [1, 1, 1, 0, 0, 0], nmin := 20, NMINH := 27, LIDB := 28, XL := 5,
    polCallsH := [["R16a", "R16", "NF", "NFH", "HD0"], ["R16b", "R16", "HD1"],
      ["R8", "R8", "ROW", "HD2"], ["FEa", "FE", "HE0"], ["FEb", "FE", "HE1"], ["FC", "FC", "CNF"]] }

/-- Nine of its numbers are those at which the library's head is written. -/
theorem hR_full : OnBytes.Road.Hd.FullH hR := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def pR : Par := parOf hR 0

/-- Made-up coordinates, no two alike. -/
def co (i : Nat) : E := E.mk3 (i + 2).toUInt64 0 0

/-- The lookup's point on the place in a tree: 27 coordinates. -/
def zxR : Point := ⟨(List.range 27).map co⟩
/-- Its point on the tree's number: one coordinate. -/
def zyR : Point := #[co 100]
/-- The key point of call number i, in the lookup's manner: the last iota_i coordinates of zy, then zx. -/
def zkR (i : Nat) : Point := if i < 3 then zyR ++ zxR else zxR

/-- What the lookup heard, made up. -/
def gR : OnBytes.Model.Forest.Heard :=
  { shape := {}, leaves := {}, zx := zxR, zy := zyR
    zk := #[zkR 0, zkR 1, zkR 2, zkR 3, zkR 4, zkR 5] }

/-- The last token of the vocabulary. -/
def tok : E := E.mk3 202047 0 0

/-- Inside the head's link, not yet opened, no reply: enterHead's shape. -/
def s1 : S :=
  { S.blank with
    failed := none
    here := .head { fr := S.blank.check.frame, kept := #[], ids := #[],
                    L := { check := S.blank.check }, F := {}, tl := {}, Fm := {} } }

/-- Behind the next token's decision at this seat. -/
def s1' : S := (seatAt hR 0).setReply s1 tok

/-- At the head's place: the link opened, the lookup heard, the reply held. -/
def sH : S :=
  { S.blank with
    failed := none
    out := { S.blank.out with reply := some tok }
    here := .head { fr := S.blank.check.frame, kept := #[], ids := #[],
                    L := { check := S.blank.check }, F := {}, tl := {}, Fm := {},
                    opened := true, lookHeard := some gR,
                    x := some { VerifiableInference.Desc.First.blankHeard with g1 := gR } } }

/-- Behind all links: between, the reply held. -/
def sE : S := { S.blank with failed := none, out := { S.blank.out with reply := some tok } }

theorem given_returns : (given pR (seatAt hR 0) sH).toOption.isSome = true := by decide

/-- The six key points' numbers of coordinates. -/
theorem zk_sizes : (List.range 6).map (fun i => (zkR i).size) = [28, 28, 28, 27, 27, 27] := by
  decide

/-- A tooth: the element 202,048 is no token of this vocabulary: the decision refuses. -/
theorem refuses_at_V :
    Reply.decide pR.sizes.V (seatAt hR 0).toSeat s1 [Reply.quiet [.e (202048, 0, 0)]] = none := rfl

/-- A tooth: another token is asked: the last test's part says no. -/
theorem fin_other : Reply.fin pR.sizes.V 1024 0 1024 202046 (seatAt hR 0).toSeat sE = false := by
  decide

end K07Real

open K07Real in
/-- **The premises of K07LawStatement, met together at the head's real seat and the stored example's public numbers.** -/
def K07MemberAt : Prop :=
  ∃ (g : Given),
    (∀ s x, (seatAt hR 0).reply ((seatAt hR 0).setReply s x) = some x) ∧
    Reply.decide pR.sizes.V (seatAt hR 0).toSeat s1 [Reply.quiet [.e (202047, 0, 0)]] = some s1' ∧
    (seatAt hR 0).reply sH = (seatAt hR 0).reply s1' ∧
    (seatAt hR 0).reply sH = (seatAt hR 0).reply sE ∧
    given pR (seatAt hR 0) sH = .ok g ∧
    Reply.fin pR.sizes.V 1024 0 1024 202047 (seatAt hR 0).toSeat sE = true

open K07Real in
theorem k07MemberAt : K07MemberAt := by
  have hg := given_returns
  cases hq : given pR (seatAt hR 0) sH with
  | error e => rw [hq] at hg; cases hg
  | ok g => exact ⟨g, fun _ _ => rfl, rfl, rfl, rfl, hq, by decide⟩

open K07Real in
/-- It is a member in Law/K07Member.lean's sense. -/
theorem k07MemberAt_member (m : K07MemberAt) : K07Member := by
  obtain ⟨g, h1, h2, h3, h4, h5, h6⟩ := m
  exact ⟨S, seatAt hR 0, pR, 1024, 0, 1024, 202047, s1, s1', _, sH, sE, g, h1, h2, h3, h4, h5, h6⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07MemberAt
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07MemberAt_member
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K07Real.refuses_at_V
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K07Real.fin_other
