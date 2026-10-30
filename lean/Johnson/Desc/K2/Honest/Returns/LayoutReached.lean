-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/LayoutReached.lean: AT A STATE THAT IS REACHED IN FRONT OF A CODE
SWITCH, IN THE GOALS' SCOPE, THE CARRIED ROWS' LAYOUT IS THE DESCRIPTION's OWN LAYOUT OF A GROUP
(`layoutOf`, Johnson/Desc/Own/Layout.lean) AT THE FRONT's STATEMENT, IN THE SIX FIELDS THAT A FOLD
AND THE CLAIM READ: at all three sorts of the kind's places. One bundle of public clauses;
statements with their proofs. Over the library alone.

  `blockBits_grown` with `layoutOf_grown`: where a statement grows (`Grows`,
                    Johnson/Desc/Grows.lean) and a group's members are there in front, the sizes of
                    the group's blocks stay; so k, h, mainFirst and maskFirst of its layout stay
  `LayIs T G old` THE BUNDLE: old's layout names G's members and flags; G has as many flags as
                    members; k, h, mainFirst and maskFirst are those of `layoutOf T G`
  `layout_of_close` a yes of the frame's closing (`closeFrame`), and T grown out of the closing's
                    statement ⊢ there is a group G with `LayIs T G` at the rows that the closing
                    returned: no state of the walk
  `link_layout_reached` at a state reached in front of the switch into a later group (the places 14
                    (m + 1) + 2, m < 23): at `frontAt s L Q`'s statement and carried rows, for all L
                    and Q
  `head_layout_reached` with `fin_layout_reached`: the like at the output head's front (339) and at
                    the front behind the last segment (353, behind its quiet step in front)

What it is for. The seven clauses are, one by one, the seven public premises of the law that the
claim at what an honest fold leaves of rows in full is the claim at what it leaves of words
(Johnson/Desc/K2/Honest/Carry/LayoutSame.lean, which this file does not import).

By, all the library's: `link_closed_reached` (Returns/ClosedReached.lean) · `head_closed_reached`,
`fin_closed_reached` (Returns/ClosedArms.lean) · `closeFrame_iff`, `fold_iff`, `bat_iff`
(Johnson/Desc/First/Close/Law/CloseMeans.lean) · `bat_inv_layout` (Close/Law/BatAtClosing.lean) ·
`layoutMade_eq`, `layoutMade_some` (Johnson/Desc/Own/LayoutAgree.lean) · `foldShapeFits_iff`
(Johnson/Desc/Own/FoldMean.lean) · `fold_grows` (Johnson/Goal/Meaning/GrowsSeated.lean) ·
`Grows.trans`. NEAR, NOT CALLED: `LayFits` (Returns/ClosedReached.lean): eight clauses on the same
layout at the same states: sizes, that each member's rows fit, the count of kept rows: none names
`layoutOf` · `layout_congr` (Johnson/Desc/First/Close/Law/LayoutDrawn.lean): two statements whose
groups agree member by member in "has rows" and in the bits of rows have layouts with these very
four fields alike: of the program's `Statement.layout`, at groups that stand in both statements:
here the group is a letter, and nothing says that it stands in the grown statement ·
`layoutOf_extends` (Johnson/Desc/Means/Keeps.lean): the other text of a group's layout stays WHOLE
where a statement extends, under five clauses on the group; with `layoutOf_same`
(Johnson/Desc/K10/Honest/Base.lean: the two texts are one where the group is there) it would want
the group's record at both statements · `tail_rows` (Johnson/IMR/GroupTail.lean): at the links' cuts
the layout's members and flags are the group's · FOUR LAWS ON THE SAME LAYOUT, EACH FROM `closeFrame
owed f S es rs = .ok x`, AT THE STATEMENT S IN FRONT OF THE CLOSING OR AT THE REQUEST's GROUP:
`closeFrame_reads` (Johnson/Desc/First/Link/Law/CloseReads.lean): the layout is, whole, the
program's `S.layout f.group`: `layout_of_close`'s proof could have called it · `layout_behind` (the
same file): from `ShapesAre` in front · `closeFrame_groups`
(Johnson/Desc/First/Close/Law/GroupsStay.lean): its members and flags are those of S's group at
f.group · `closeFrame_sizes` (Johnson/Desc/First/Link/Law/CarriedSizes.lean): its k and h are the
request's group's. None names `layoutOf`; none speaks at a statement that has grown.

Limits. WHICH GROUP G IS, is not said: there is one. "Reached" means `Reach 0 (c.blocksInOrder.map below)
(ProofFile.startS Z) k (z, s)`: some run of the first k of the chain's sub-protocols, each in its wrapped
form, leads from the start state to s. NO PUBLIC FILES, OPENING AND STATE ARE GIVEN HERE AT WHICH
THE PREMISES OF THE LAST THREE LAWS (in scope · the files read · the description opened · the state
reached) HOLD TOGETHER: as far as this file goes, these three could hold of nothing. The layout's
two fields on the codes' lengths are not treated. This file's imports are heavy. Nothing on any
property.
-/
import Johnson.Desc.K2.Honest.Returns.ClosedArms
import Johnson.Desc.First.Close.Law.BatAtClosing
import Johnson.Desc.Own.LayoutAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription Grows)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (finishFrontQ headFrontOf finFrontOf)
open VerifiableInference.Desc.First.Close (closeFrame closeFrame_iff fold_iff bat_iff
  bat_inv_layout)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2 (fold_grows)
open ProofFile (Cl)

/-! ## Where a statement grows, a group's layout stays -/

/-- The blocks' sizes of a group whose members are there stay where the statement grows. -/
theorem blockBits_grown {S T : Statement} (hg : Grows S T) (G : Group)
    (ht : ∀ i, i < G.members.size → ∃ x, S.oracles[G.members.getD i noId]? = some x)
    (part : OnBytes.Part) : Own.blockBits T G part = Own.blockBits S G part := by
  unfold Own.blockBits
  apply Array.map_congr_left
  intro i hi
  obtain ⟨x, hx⟩ := ht i (Array.mem_range.1 hi)
  obtain ⟨x', hx', e, -⟩ := hg.2.2 _ x hx
  dsimp only
  unfold Own.tableThere Statement.rowBits
  rw [hx, hx']
  show (if ((some x').any fun y => decide (0 < y.shape.rows part)) &&
      !(part == .main && G.kept.getD i false) then some (ceilLog2 (x'.shape.rows part))
    else none) = _
  rw [Option.any_some, e]
  rfl

/-- So the four fields of its layout that a fold reads stay. -/
theorem layoutOf_grown {S T : Statement} (hg : Grows S T) (G : Group)
    (ht : ∀ i, i < G.members.size → ∃ x, S.oracles[G.members.getD i noId]? = some x) :
    (Own.layoutOf T G).k = (Own.layoutOf S G).k ∧ (Own.layoutOf T G).h = (Own.layoutOf S G).h ∧
      (Own.layoutOf T G).mainFirst = (Own.layoutOf S G).mainFirst ∧
      (Own.layoutOf T G).maskFirst = (Own.layoutOf S G).maskFirst := by
  unfold Own.layoutOf
  dsimp only
  rw [blockBits_grown hg G ht .main, blockBits_grown hg G ht .mask]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Right behind a closing: no state of the walk -/

/-- **The carried rows' layout is the description's own layout of the group G at the statement T, in
the six fields that a fold and the claim read**; and G has as many flags as members. -/
structure LayIs (T : Statement) (G : Group) (old : SingleRows) : Prop where
  members : old.layout.members = G.members
  kept : old.layout.kept = G.kept
  sizes : G.kept.size = G.members.size
  k : old.layout.k = (Own.layoutOf T G).k
  h : old.layout.h = (Own.layoutOf T G).h
  mainFirst : old.layout.mainFirst = (Own.layoutOf T G).mainFirst
  maskFirst : old.layout.maskFirst = (Own.layoutOf T G).maskFirst

/-- **The layout that a closing lays into the carried rows is the description's own layout of a
group, in the six fields read, at every statement grown out of the closing's.** -/
theorem layout_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T) :
    ∃ G : Group, LayIs T G x.1.rows := by
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ := (closeFrame_iff owed f S₀ es rs x.1 x.2).1 h
  obtain ⟨eB, es', rB, rs', -, -, m, -, row, L, S₁, hB, ⟨k1, k2⟩, hF⟩ := hc
  have hg1 := fold_grows ((fold_iff _ _ _ _ _ _ _ _).2 hF)
  obtain ⟨G₀, y, -, -, -, hS1, -, hl⟩ := bat_inv_layout ((bat_iff _ _ _ _ _ _ _).2 hB)
  rw [← hS1, ← Own.layoutMade_eq] at hl
  obtain ⟨G, -, rfl⟩ := Own.layoutMade_some.1 hl
  obtain ⟨eE, eR, rE, rR, -, -, -, -, hshape, -, -, d2, -, sum, eps, -, -, gamma, claim, -, hout,
    -⟩ := hF
  obtain ⟨c, zk, -, -, -, -, -, -, s1, -, -, hmem, -⟩ := (Own.foldShapeFits_iff _ _).1 hshape
  have ht : ∀ i, i < G.members.size → ∃ z, S₁.oracles[G.members.getD i noId]? = some z :=
    fun i hi => by
      obtain ⟨z, hz, -⟩ := hmem i hi
      exact ⟨z, hz⟩
  obtain ⟨a1, a2, a3, a4⟩ := layoutOf_grown (Grows.trans hg1 hg) G ht
  have eL : x.1.rows.layout = { Own.layoutOf S₁ G with k := Gf.k, h := Gf.h } := by
    rw [e]
    show rows.layout = _
    rw [hout]
    rfl
  refine ⟨G, by rw [eL]; rfl, by rw [eL]; rfl, s1, ?_, ?_, ?_, ?_⟩
  · rw [eL, a1]
    exact k1.symm
  · rw [eL, a2]
    exact k2.symm
  · rw [eL, a3]
  · rw [eL, a4]

/-! ## At a reached state -/

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **At the front's statement and carried rows, at a state reached in front of the switch into a
later group.** -/
theorem link_layout_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) :
    ∃ G : Group, LayIs (frontAt s L Q).st G (frontAt s L Q).f.rows := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := link_closed_reached hS hR O h23 hr
  obtain ⟨G, H⟩ := layout_of_close hx hg
  rw [← hf] at H
  exact ⟨G, H.members, H.kept, H.sizes, H.k, H.h, H.mainFirst, H.maskFirst⟩

/-- **At the head's front.** -/
theorem head_layout_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) (T : SwitchTarget) :
    ∃ G : Group, LayIs (headFrontOf s a T).st G (headFrontOf s a T).f.rows := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := head_closed_reached hS hR O hr here
  show ∃ G : Group, LayIs s.st G a.fr.rows
  rw [hf]
  exact layout_of_close hx hg

/-- **At the front behind the last segment.** -/
theorem fin_layout_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup) :
    ∃ G : Group, LayIs (finFrontOf t a Q).st G (finFrontOf t a Q).f.rows := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := fin_closed_reached hS hR O hr he here
  show ∃ G : Group, LayIs t.st G a.fr.rows
  rw [hf]
  exact layout_of_close hx hg

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.blockBits_grown
#print axioms VerifiableInference.Desc.K2.Honest.Returns.layoutOf_grown
#print axioms VerifiableInference.Desc.K2.Honest.Returns.LayIs
#print axioms VerifiableInference.Desc.K2.Honest.Returns.layout_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_layout_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_layout_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_layout_reached
