-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.Sits
import Johnson.Desc.K12.Law.SeatKeeps
import Johnson.Desc.First.Link.Law.Shape
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.K12.AtFinish
import Johnson.Desc.K14.Blocks
import Johnson.Desc.Third.Chain
/-
Johnson/Desc/K12/Law/SitsChains.lean: THE THREE CHAINS' FLAT LISTS CUT AT THE PROXIMITY TEST's FOUR
PLACES, AND THAT THE ENTRY THERE SITS (Johnson/Desc/K12/Law/Sits.lean). Of the chains' own makers in
the library's tree: the driver's firstChain (Johnson/Desc/First/Driver/Chain.lean) · the shared
chain's chainOf at Seat.tests | Seat.last (Johnson/Desc/K14/Blocks.lean ·
Johnson/Desc/K12/Seat/Fill.lean) · the last chain's lastChainWithOwnTest (Johnson/Desc/Third/Chain.lean);
the two later chains behind Chain.retype, GENERAL IN THE TYPE OF CLAIMS. No harness's file lies
beneath. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO
NEW MATHEMATICS.
  a12 · pL N · pGu N · pGomega nO · pOwn N     the first chain's address of the kind; the four
      places' numbers as the seats' texts lay them: H2U.proximityTestParametersAt ⟨1, none, 2, .K12⟩ N.L · ⟨2, none, 9,
      .K12⟩ N.U · ⟨2, none, 10, .K12⟩ nO · ⟨3, none, 2, .K12⟩ N.W.
  chainShape_back · firstChain_cut       (off Shape.firstChain_shape | ChainShape: the
      driver's text is not walked again) firstChain H links several = some c gives c.blocksInOrder = pre ++
      firstEntry H.same b :: l, b the block that the socket gives at a12.
  firstEntry same b · firstEntry_sits     ({ b with place := a12 }.guarded same hearsReply).asBare;
      if b sits, it sits, the guard's test bound behind the way out.
  guEntry N · omegaEntry nO · ownEntry K     the entries of the later chains' flat lists;
      guEntry_sits · omegaEntry_sits · ownEntry_sits (the last GENERAL IN THE BLOCK K at T12).
  shared_cut · shared_cut_omega · second_cut     the two flat lists, written out (sharedPre ·
      sharedEnd · secondPre · secondEnd: what stands in front and behind, under names).
  firstEntry_keeps · guEntry_keeps · omegaEntry_keeps · ownEntry_keeps     each entry has the kind's
      block's «before» and declared rounds (Keeps: Johnson/Desc/K12/Law/SeatKeeps.lean).
LIMITS. That a written description's chains are these makers' values, and what its socket gives at
a12: left to files under Johnson/Loose/. pre and l stand under «there is» in firstChain_cut. NO RUN.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)

/-- The first chain's address of the kind. -/
abbrev a12 : Place := ⟨1, none, 2, .K12⟩

/-- The places' numbers as the seats' own texts lay them. -/
def pL (N : H2U.Places4) : P12 := H2U.proximityTestParametersAt a12 N.L
def pGu (N : H2U.Places4) : P12 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U
def pGomega (nO : H2U.PlaceNums) : P12 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO
def pOwn (N : H2U.Places4) : P12 := H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W

/-! ### the first chain -/

/-- The entry of the first chain's flat list at a12: b: what the socket gives there. -/
def firstEntry {S Cl : Type} (same : S → S → Bool) (b : Block S Cl) : Block S Cl :=
  (({ b with place := a12 } : Block S Cl).guarded same First.hearsReply).asBare

theorem firstEntry_sits {S T Cl Cl' : Type} (same : S → S → Bool) {b : Block S Cl}
    {K : Block T Cl'} {enter : S → Except String T} {leave : S → T → Except String S}
    (h : Sits b K enter leave) :
    Sits (firstEntry same b) K enter (fun s t => (leave s t).bind (seatSame same s)) :=
  ((h.same ({ b with place := a12 } : Block S Cl) rfl rfl id).guarded same First.hearsReply
    rfl).asBare

/-- The entry has what the socket's block has of «before» and declared rounds. -/
theorem firstEntry_keeps {S T Cl Cl' : Type} (same : S → S → Bool) {b : Block S Cl}
    {K : Block T Cl'} (h : H2K.Made.Keeps b K) : H2K.Made.Keeps (firstEntry same b) K :=
  ⟨h.1, h.2⟩

/-- The driver's chain without the guard: its back's second block is the socket's at a12: off
ChainShape (Johnson/Desc/First/Link/Law/Shape.lean). -/
theorem chainShape_back {S Cl : Type} {H : First.Blocks S Cl} {links : List First.ModelPart}
    {several : Bool} {c : Chain S Cl} (h : Shape.ChainShape H links several c) :
    ∃ b2 b rest, H.block a12 = some b ∧ c.back = b2 :: { b with place := a12 } :: rest := by
  obtain ⟨_, _, _, hk, _⟩ := h
  obtain ⟨tl, ha⟩ : ∃ tl, First.addresses none (First.backKinds several) =
      ⟨1, none, 1, .K2⟩ :: a12 :: tl := by
    cases several <;> exact ⟨_, rfl⟩
  rw [ha] at hk
  cases hb : c.back with
  | nil => rw [hb] at hk; cases hk
  | cons b2 r =>
    cases r with
    | nil => rw [hb] at hk; simp at hk
    | cons b12 rest =>
      rw [hb] at hk
      simp only [List.map_cons, List.cons.injEq] at hk
      obtain ⟨b, hb', e⟩ := Option.map_eq_some_iff.1 hk.2.1.symm
      exact ⟨b2, b, rest, hb', by rw [← e]⟩

/-- The first chain's flat list is cut at the proximity test's address. -/
theorem firstChain_cut {S Cl : Type} (H : First.Blocks S Cl) (links : List First.ModelPart)
    (several : Bool) (c : Chain S Cl) (h : First.firstChain H links several = some c) :
    ∃ b pre l, H.block a12 = some b ∧ c.blocksInOrder = pre ++ firstEntry H.same b :: l := by
  obtain ⟨_, c0, hs, rfl⟩ := Shape.firstChain_shape h
  obtain ⟨b2, b, rest, hb, hk⟩ := chainShape_back hs
  refine ⟨b, (c0.first.guarded H.same First.hearsReply).asBare ::
      (c0.links.map (Link.guarded H.same First.hearsReply)).flatMap Link.blocksInOrder ++
        [(b2.guarded H.same First.hearsReply).asBare],
    (rest.map (Block.guarded H.same First.hearsReply)).map Block.asBare ++
      [(c0.last.guarded H.same First.hearsReply).asBare], hb, ?_⟩
  rw [Chain.flat_eq]
  simp [Chain.guarded, hs.2.1, hk, firstEntry]

/-! ### the shared chain -/

def guEntry (Cl' : Type) (N : H2U.Places4) : Block _root_.Desc.K14.St Cl' :=
  ((onGu (proximityTestKind guardedProximityTestParts (pGu N) : Blk')).retype (Cl' := Cl')).asBare

def omegaEntry (Cl' : Type) (nO : H2U.PlaceNums) : Block _root_.Desc.K14.St Cl' :=
  ((onGomega (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk')).retype (Cl' := Cl')).asBare

theorem guEntry_sits (Cl' : Type) (N : H2U.Places4) :
    Sits (guEntry Cl' N) (proximityTestKind guardedProximityTestParts (pGu N) : Blk') (Seat.enter (·.gU) (·.firstMask))
      Seat.leave :=
  (sits_inside _ _ _).retype.asBare

theorem omegaEntry_sits (Cl' : Type) (nO : H2U.PlaceNums) :
    Sits (omegaEntry Cl' nO) (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk')
      (Seat.enter (·.gOmega) fun _ => none) Seat.leave :=
  (sits_inside _ _ _).retype.asBare

theorem guEntry_keeps (Cl' : Type) (N : H2U.Places4) :
    H2K.Made.Keeps (guEntry Cl' N) (proximityTestKind guardedProximityTestParts (pGu N) : Blk') := ⟨rfl, rfl⟩

theorem omegaEntry_keeps (Cl' : Type) (nO : H2U.PlaceNums) :
    H2K.Made.Keeps (omegaEntry Cl' nO) (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk') := ⟨rfl, rfl⟩

/-- What stands in front of the test on G_u: the chain's front block and the shared chain's
own blocks. -/
def sharedPre (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (N : H2U.Places4) : List (Block _root_.Desc.K14.St Cl') :=
  ((_root_.Desc.K14.chainOf c P (Seat.tests N) Seat.last).retype (Cl' := Cl')).first.asBare ::
    (_root_.Desc.K14.blocksOr P).map fun b => (b.retype (Cl' := Cl')).asBare

/-- The shared chain's end as it is laid. -/
def sharedEnd (Cl' : Type) (P : _root_.Desc.K14.P14) (N : H2U.Places4) :
    Block _root_.Desc.K14.St Cl' :=
  ((Seat.last (_root_.Desc.K14.blocksOr P ++ Seat.tests N)).retype (Cl' := Cl')).asBare

/-- The shared chain's flat list, behind Chain.retype, cut at the test on G_u. -/
theorem shared_cut (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (N : H2U.Places4) :
    ((_root_.Desc.K14.chainOf c P (Seat.tests N) Seat.last).retype (Cl' := Cl')).blocksInOrder =
      sharedPre Cl' c P N ++ guEntry Cl' N ::
        ((N.O.toList.map fun nO => omegaEntry Cl' nO) ++ [sharedEnd Cl' P N]) := by
  rw [Chain.flat_eq]
  simp [Chain.retype, _root_.Desc.K14.chainOf, Seat.tests, guEntry, omegaEntry, pGu, pGomega,
    sharedPre, sharedEnd, List.map_append, List.map_map, Function.comp_def]

/-- The same list cut at the test on G_omega, where the plan has one. -/
theorem shared_cut_omega (Cl' : Type) (c : OnBytes.Model.Verify.Chains)
    (P : _root_.Desc.K14.P14) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    ((_root_.Desc.K14.chainOf c P (Seat.tests N) Seat.last).retype (Cl' := Cl')).blocksInOrder =
      (sharedPre Cl' c P N ++ [guEntry Cl' N]) ++ omegaEntry Cl' nO :: [sharedEnd Cl' P N] := by
  rw [shared_cut, hO]
  simp

/-! ### the last chain -/

/-- The entry of the last chain's flat list at ⟨3, none, 2⟩: K: the block at T12 that the seat's
text hands the door. -/
def ownEntry (Cl' : Type) (K : Blk') : Block Third.S₃ Cl' :=
  ((Third.ownAt (onOwn K)).retype (Cl' := Cl')).asBare

theorem ownEntry_sits (Cl' : Type) (K : Blk') : Sits (ownEntry Cl' K) K enterOwn leaveOwn :=
  ((sits_inside enterOwn K leaveOwn).same (Third.ownAt (onOwn K)) rfl rfl id).retype.asBare

theorem ownEntry_keeps (Cl' : Type) (K : Blk') : H2K.Made.Keeps (ownEntry Cl' K) K := ⟨rfl, rfl⟩

/-- What stands in front of the own test: the last chain's first block and the taken trees' sources.
-/
def secondPre (Cl' : Type) (p : Third.P₁₄) (K : Blk') : List (Block Third.S₃ Cl') :=
  [((Third.lastChainWithOwnTest p (onOwn K)).retype (Cl' := Cl')).first.asBare,
    ((Third.takenSources (onOwn K)).retype (Cl' := Cl')).asBare]

/-- The last chain's end as it is laid. -/
def secondEnd (Cl' : Type) (p : Third.P₁₄) (K : Blk') : Block Third.S₃ Cl' :=
  ((Third.lastChainWithOwnTest p (onOwn K)).last.retype (Cl' := Cl')).asBare

/-- The last chain's flat list, behind Chain.retype, cut at the own test. -/
theorem second_cut (Cl' : Type) (p : Third.P₁₄) (K : Blk') :
    ((Third.lastChainWithOwnTest p (onOwn K)).retype (Cl' := Cl')).blocksInOrder =
      secondPre Cl' p K ++ ownEntry Cl' K :: [secondEnd Cl' p K] := by
  rw [Chain.flat_eq]
  simp [Chain.retype, Third.lastChainWithOwnTest, ownEntry, secondPre, secondEnd]

end H2K.JointK

#print axioms H2K.JointK.firstEntry_sits
#print axioms H2K.JointK.firstChain_cut
#print axioms H2K.JointK.guEntry_sits
#print axioms H2K.JointK.omegaEntry_sits
#print axioms H2K.JointK.ownEntry_sits
#print axioms H2K.JointK.shared_cut
#print axioms H2K.JointK.shared_cut_omega
#print axioms H2K.JointK.second_cut
