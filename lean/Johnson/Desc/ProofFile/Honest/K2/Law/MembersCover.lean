-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MembersCover.lean: the kind "the code switch" (K2): THE LOCK's
TWO CLAUSES ON THE CLOSED GROUP's MEMBERS, FROM THE SAME CLAUSES MEMBER BY MEMBER: under the head,
at a link place (m < 23), the carried layout has just as many members as the segment's first sending
has messages in front of its mask, and two more: so what is had at each message of the first sending
and at the two later sendings' messages is had at every member. Three definitions: a name for the
two clauses at one member; two public tests. Two closed facts by Lean's kernel, one a control;
statements with their proofs.

WHICH SLOT IT IS FOR. As MemberClause.lean's of this folder: the second and third limb of
`LockAsks` (ClaimOfLock.lean), WHOLE, from the ends of `link_member_clause` (MemberClause.lean) or
`link_member_clause_first`, and of `link_member_clause_later` (MemberClauseK1.lean).

  `MemberTied`      THE TWO CLAUSES AT ONE MEMBER i: each entry of the i-th row's main and mask rows
                    is the word at the layout's i-th member: the text of the two limbs, i fixed
  `membersCountB`, `membersCountAnyB`, `membersCountW`, `membersCountW_can_fail`   at each of the 25
                    written segments the link's written list has as many members as the first
                    sending has messages but one, and two more; with one more: no, at every segment
  `link_members_size`   so, under the head, at the front that the switch's block takes off a reached
                    state: the number of the carried layout's members
  `limbs_of_tied`   THE COVER: `MemberTied` below s₀ and at s₀, s₀ + 1 ⊢ the two limbs

By: `link_membersNumbered_front` (Johnson/Desc/K2/Honest/Returns/MembersNumbered.lean) ·
`segments_at_head` (PlacesWritten.lean of this folder).

Limits. `limbs_of_tied` IS LOGIC OVER A COUNT: it pays nothing at any member. No run is given at
which the head's premise and "reached" hold together. Not at the places 339 and 353. CLOSED FACTS BY
LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. The full size and the format's second hash function
alone. NOT IN FRONT OF A LAW OVER COINS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Closing
import Johnson.Desc.K2.Honest.Returns.MembersNumbered
import Johnson.Desc.Means.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2 noId)
open OnBytes.Means (Words)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K2.Honest.Returns (link_membersNumbered_front)
open VerifiableInference.Desc.Sound (allOf EAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **THE LOCK's TWO CLAUSES AT ONE MEMBER.** A definition: the form of a premise or an end. It
speaks at every place of the member's main rows, the pads' places too, and at its mask rows: entries
that hold coins. -/
def MemberTied (fx : _root_.Tw.K2.Front) (R : GroupRows) (w : Words GE) (i : Nat) : Prop :=
  (∀ b j,
    b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.mainRows →
    (R.rows.getD i zeroMessage).main
        ((fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.mainDeg
          == 3) b j =
      w (fx.f.rows.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
        (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId)
          default).shape.mainRows)) ∧
  ∀ b j,
    b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.maskRows →
    (R.rows.getD i zeroMessage).mask b j =
      w (fx.f.rows.layout.members.getD i noId) .mask (b + j * 2 ^ ceilLog2
        (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId)
          default).shape.maskRows)

/-- A PUBLIC TEST: at each written segment the link's written list has as many members as the first
sending has messages but one, and two and d more. 0 is the test. -/
def membersCountB (d : Nat) : Bool :=
  segsW.zipIdx.all fun x =>
    (VerifiableInference.Desc.First.Close.membersOf (loAt x.2)).length ==
      (x.1.sent.headD #[]).size - 1 + 2 + d

/-- For a control: `membersCountB` with "at some segment" for "at each segment". -/
def membersCountAnyB (d : Nat) : Bool :=
  segsW.zipIdx.any fun x =>
    (VerifiableInference.Desc.First.Close.membersOf (loAt x.2)).length ==
      (x.1.sent.headD #[]).size - 1 + 2 + d

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL. -/
theorem membersCountW : membersCountB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one more the test says no, at every segment; and there are 25 segments. -/
theorem membersCountW_can_fail : membersCountAnyB 1 = false ∧ segsW.length = 25 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- No run is given at which the head's premise and "reached" hold together. **THE NUMBER OF THE
CARRIED LAYOUT's MEMBERS**, at a segment's first place (m < 23). -/
theorem link_members_size (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {q : VerifiableInference.Desc.First.K2.P2}
    (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt q a.1.2 = some fx)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg) :
    fx.f.rows.layout.members.size = (Sg.sent.headD #[]).size - 1 + 2 := by
  rw [segments_at_head h.toAtMg O] at hS
  have e := link_membersNumbered_front h h23 a hr hq hfx
  have e1 : fx.f.rows.layout.members.size =
      (VerifiableInference.Desc.First.Close.membersOf (loAt m)).length := by
    rw [← Array.length_toList, e, List.length_map]
  have hz : (Sg, m) ∈ segsW.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact hS
  have t := List.all_eq_true.1 membersCountW (Sg, m) hz
  rw [e1]
  exact beq_iff_eq.1 t

/-- **THE COVER.** s₀: the number of the first sending's messages in front of its mask. Logic over a
count: it pays nothing at any member. -/
theorem limbs_of_tied {fx : _root_.Tw.K2.Front} {R : GroupRows} {w : Words GE} {s₀ : Nat}
    (hsz : fx.f.rows.layout.members.size = s₀ + 2)
    (HA : ∀ n, n < s₀ → MemberTied fx R w n) (HB : ∀ q, q < 2 → MemberTied fx R w (s₀ + q)) :
    (∀ i b j, i < fx.f.rows.layout.members.size →
      b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.mainRows →
      (R.rows.getD i zeroMessage).main
          ((fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.mainDeg
            == 3) b j =
        w (fx.f.rows.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
          (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId)
            default).shape.mainRows)) ∧
    (∀ i b j, i < fx.f.rows.layout.members.size →
      b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.maskRows →
      (R.rows.getD i zeroMessage).mask b j =
        w (fx.f.rows.layout.members.getD i noId) .mask (b + j * 2 ^ ceilLog2
          (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId)
            default).shape.maskRows)) := by
  have all : ∀ i, i < fx.f.rows.layout.members.size → MemberTied fx R w i := by
    intro i hi
    rw [hsz] at hi
    by_cases h0 : i < s₀
    · exact HA i h0
    · have e : i = s₀ + (i - s₀) := by omega
      rw [e]
      exact HB (i - s₀) (by omega)
  exact ⟨fun i b j hi hb => (all i hi).1 b j hb, fun i b j hi hb => (all i hi).2 b j hb⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.MemberTied
#print axioms ProofFile.Honest.K2.Law.membersCountB
#print axioms ProofFile.Honest.K2.Law.membersCountAnyB
#print axioms ProofFile.Honest.K2.Law.membersCountW
#print axioms ProofFile.Honest.K2.Law.membersCountW_can_fail
#print axioms ProofFile.Honest.K2.Law.link_members_size
#print axioms ProofFile.Honest.K2.Law.limbs_of_tied
