-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MembersJoin.lean: the kind "the code switch" (K2): THE MEMBERS
OF THE ROWS THAT AN HONEST PROVER's CLOSING MAKES OF A WRITTEN SEGMENT ARE THE CLOSED GROUP's
MEMBERS AT THEIR TRUE SHAPES, AT THE SWITCH's OWN FRONT, UNDER THE HEAD's PREMISE, AT ALL THREE
SORTS OF THE KIND's PLACES. The first clause of the premise hR of `claimTrue_at_segmentLeft`
(Law/ClaimAtClosing.lean). Statements with their proofs: joins; no definition.

  `members_of_pairs` two lists of members with the same pairs (shape, flag) are one list
  `membersOfSeg_written` l < 25 · `segsW[l]? = some Sg` ⊢ `membersOfSeg Sg (l != 0)` is link l's
                    written list's members, as members: from the kernel's test `segMembers_written`
                    (Law/MembersWritten.lean)
  `link_members_front` the head `AtMgA` · m < 23 · a reached (`AtMg.rch`) at 14 (m + 1) + 2 · the
                    front fx that the switch's block takes off a's state · `segsW[m]? = some Sg` ·
                    `prev.isSome = (m != 0)` · `segmentGroupRows table Sg prev prevKept own k base
                    withFresh = .ok R` ⊢ `R.members = membersTrue fx.st fx.f.rows`
  `head_members_front` the same at 339, at `segsW[23]?`, with `prev.isSome = true`
  `fin_members_front` the same at 353, behind the quiet step in front, at `segsW[24]?`, with
                    `prev.isSome = true`

By: `segmentRows_members` (Law/GroupMembers.lean): the prover's side · `link_membersTrue_front`,
`head_membersTrue_front`, `fin_membersTrue_front`
(Johnson/Desc/K2/Honest/Returns/TrueMembersAtHead.lean): the state's side.

Limits. TWO PUBLIC PREMISES ARE LEFT HERE: that Sg is the written segment of that number, and that a
fold stands in front just where the number is not 0: nothing in this file ties them to the Sg and
the prev at which the closing's walk (`closingFrom`) calls `segmentGroupRows`: that is
Law/MembersAtWalk.lean's. No run is given at which the head's premise and "reached" hold together.
Nothing on the rows' entries. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MembersWritten
import Johnson.Desc.K2.Honest.Returns.TrueMembersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (GroupMember Left membersTrue)
open VerifiableInference.Desc.K2.Honest.Returns (link_membersTrue_front head_membersTrue_front
  fin_membersTrue_front)
open VerifiableInference.Desc.LinkJoin (loAt kbW)
open VerifiableInference.Desc.Sound (allOf EAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- Two lists of members with the same pairs (shape, flag) are one list. -/
theorem members_of_pairs : ∀ {A B : List GroupMember},
    A.map (fun m => (m.shape, m.kept)) = B.map (fun m => (m.shape, m.kept)) → A = B
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | ⟨s, k⟩ :: A, ⟨s', k'⟩ :: B, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h₁, h₂⟩ := List.cons.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
    rw [members_of_pairs h₂]

/-- **A written segment's public members are the written list's**, as members. -/
theorem membersOfSeg_written {l : Nat} (hl : l < 25) {Sg : SegmentPub} (h : segsW[l]? = some Sg) :
    membersOfSeg Sg (l != 0) =
      (VerifiableInference.Desc.First.Close.membersOf (loAt l)).map fun i =>
        ⟨((loAt l).get i).1, kbW l i⟩ := by
  have e := (List.all_eq_true.1 segMembers_written) l (List.mem_range.2 hl)
  have e' : segMembersAt l = listMembersAt l := by simpa using e
  unfold segMembersAt at e'
  rw [h] at e'
  apply members_of_pairs
  have e'' : (membersOfSeg Sg (l != 0)).map (fun m => (m.shape, m.kept)) = listMembersAt l := e'
  rw [e'', List.map_map]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE LOCK's CLAUSE ON THE MEMBERS, AT A SEGMENT's FIRST PLACE**: under the head, at the front
that the switch's block takes off a state reached at 14 (m + 1) + 2, m < 23: the members of whatever
rows `segmentGroupRows` makes of the written segment m are the closed group's at their true shapes. -/
theorem link_members_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .link) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx)
    {Sg : SegmentPub} (hSg : segsW[m]? = some Sg)
    {table : FreshTable} {prev : Option Left} {prevKept : List OnBytes.OracleShape}
    {own : Nat → Nat → Nat → Cb.Gl.E} {k : Nat → Except String Stretch} {base : Nat}
    {withFresh : Bool} {R : GroupRows} (hp : prev.isSome = (m != 0))
    (hR : segmentGroupRows table Sg prev prevKept own k base withFresh = .ok R) :
    R.members = membersTrue fx.st fx.f.rows := by
  rw [segmentRows_members hR, hp, membersOfSeg_written (by omega) hSg,
    link_membersTrue_front h h23 a hr hq hfx]

/-- **The same at the output head's front** (339): the written segment 23. -/
theorem head_members_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .head) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx)
    {Sg : SegmentPub} (hSg : segsW[23]? = some Sg)
    {table : FreshTable} {prev : Option Left} {prevKept : List OnBytes.OracleShape}
    {own : Nat → Nat → Nat → Cb.Gl.E} {k : Nat → Except String Stretch} {base : Nat}
    {withFresh : Bool} {R : GroupRows} (hp : prev.isSome = true)
    (hR : segmentGroupRows table Sg prev prevKept own k base withFresh = .ok R) :
    R.members = membersTrue fx.st fx.f.rows := by
  rw [segmentRows_members hR, hp]
  exact (membersOfSeg_written (l := 23) (by omega) hSg).trans
    (head_membersTrue_front h a hr hq hfx).symm

/-- **The same at the front behind the last segment** (353): the written segment 24. -/
theorem fin_members_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S}
    (he : VerifiableInference.Desc.First.K2.finishFrontQ a.1.2 = .ok t)
    {p : VerifiableInference.Desc.First.K2.P2} (hq : p.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hfx : VerifiableInference.Desc.First.K2.frontAt p t = some fx)
    {Sg : SegmentPub} (hSg : segsW[24]? = some Sg)
    {table : FreshTable} {prev : Option Left} {prevKept : List OnBytes.OracleShape}
    {own : Nat → Nat → Nat → Cb.Gl.E} {k : Nat → Except String Stretch} {base : Nat}
    {withFresh : Bool} {R : GroupRows} (hp : prev.isSome = true)
    (hR : segmentGroupRows table Sg prev prevKept own k base withFresh = .ok R) :
    R.members = membersTrue fx.st fx.f.rows := by
  rw [segmentRows_members hR, hp]
  exact (membersOfSeg_written (l := 24) (by omega) hSg).trans
    (fin_membersTrue_front h a hr he hq hfx).symm

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.members_of_pairs
#print axioms ProofFile.Honest.K2.Law.membersOfSeg_written
#print axioms ProofFile.Honest.K2.Law.link_members_front
#print axioms ProofFile.Honest.K2.Law.head_members_front
#print axioms ProofFile.Honest.K2.Law.fin_members_front
