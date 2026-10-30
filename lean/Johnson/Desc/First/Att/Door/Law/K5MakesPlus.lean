-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-

row_makes: at the small door the layer asks nothing: there the equation holds by rfl.

Johnson/Desc/First/Att/Door/Law/K5MakesPlus.lean: kind K5: WHAT THE WIDER LIST OF EXTRA PUBLIC TESTS
(morePlus, Johnson/Desc/First/Att/Door/Plus.lean) LETS THE KIND's SUB-PROTOCOL MAKE: JUST ITS OWN
TWO NAMES, K5.okAt AND K5.plain: at every list of segments and every place of the kind (K5Place,
Johnson/Desc/First/Att/K05T2.lean). One small lemma a part. The like at the composed filling's own
list (the same merges, struck by leavesName).

After K5MakesAt.lean (at another form of the composed filling), whose small
lemmas on the parts that stay are taken over line for line. Nothing is claimed on soundness,
completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Plus
import Johnson.Desc.First.Att.K05T2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (K5Place)

section
variable {links : List ModelPart} {m : Nat} {p p' : Place} (Ix : K5Place links m p p')
include Ix

omit Ix in
theorem row_makes : (rowMore.rows links p).makes = [] := rfl

theorem ours_makes : (H2K5.Door.more.rows links p).makes = [(some m, "K5.okAt"), (some m, "K5.plain")] := by
  show (((moreReads.rows links p).makes ++ (moreOk.rows links p).makes) ++ (moreLive.rows links p).makes) ++
    (morePlain.rows links p).makes = _
  simp [moreReads, moreOk, moreLive, morePlain, atAtt, Ix.link, Ix.sub, Ix.piece]

theorem k12_makes : ((K12.Door.k12More.merge K12.Door.shapesMore).rows links p).makes = [] := by
  show (K12.Door.k12More.rows links p).makes ++ (K12.Door.shapesMore.rows links p).makes = []
  simp [K12.Door.k12More, K12.Door.shapesMore, Ix.link]

theorem live_makes : (Look.liveMore.rows links p).makes = [] := by
  simp [Look.liveMore, Look.liveAskers, Ix.link, Ix.sub, Ix.piece, shift]

theorem left_makes : (FillBare.leftMore.rows links p).makes = [] := by
  simp [FillBare.leftMore, Ix.link, Ix.sub]

theorem sent_makes : (FillSent.sentMore.rows links p).makes = [] := by
  simp [FillSent.sentMore, Ix.link, Ix.sub, Ix.piece, shift]

theorem sent1_makes : (FillSent.sent1More.rows links p).makes = [] := by
  simp [FillSent.sent1More, Ix.link, Ix.sub, Ix.piece, shift]

theorem bare_makes : (bareMoreAtt.rows links p).makes = [] := by
  simp [bareMoreAtt, Ix.link, Ix.sub, Ix.piece]

theorem wSits_makes : (K13.Law.wSitsMore.rows links p).makes = [] := by
  simp [K13.Law.wSitsMore, Ix.link]

/-- The merges before any strike. -/
theorem over9_makes (M0 : More) (h0 : (M0.rows links p).makes = []) :
    ((moreOver9 M0).rows links p).makes = [(some m, "K5.okAt"), (some m, "K5.plain")] := by
  show ((((((M0.rows links p).makes ++ (rowMore.rows links p).makes) ++ (FillBare.leftMore.rows links p).makes) ++
    (FillSent.sent1More.rows links p).makes) ++ (FillSent.sentMore.rows links p).makes) ++
      (H2K5.Door.more.rows links p).makes) ++ (K13.Law.wSitsMore.rows links p).makes = _
  rw [h0, row_makes, left_makes Ix, sent1_makes Ix, sent_makes Ix, ours_makes Ix, wSits_makes Ix]
  rfl

/-- **What the kind's sub-protocol is let to make, at the wider list.** -/
theorem k5_makes_plus (M0 : More) (h0 : (M0.rows links p).makes = []) :
    ((morePlus M0).rows links p).makes = [(some m, "K5.okAt"), (some m, "K5.plain")] := by
  show (((((moreOver9 M0).rows links p).makes ++ ((K12.Door.k12More.merge K12.Door.shapesMore).rows links p).makes) ++
    (Look.liveMore.rows links p).makes) ++ (bareMoreAtt.rows links p).makes).filter (fun n => !leavesBut3 n) = _
  rw [over9_makes Ix M0 h0, k12_makes Ix, live_makes Ix, bare_makes Ix]
  rfl

/-- The like at the composed filling's own list. -/
theorem k5_makes_9 (M0 : More) (h0 : (M0.rows links p).makes = []) :
    (((moreOver9 M0).strike leavesName).rows links p).makes = [(some m, "K5.okAt"), (some m, "K5.plain")] := by
  show (((moreOver9 M0).rows links p).makes).filter (fun n => !leavesName n) = _
  rw [over9_makes Ix M0 h0]
  rfl

end

end H2K5.Door

#print axioms H2K5.Door.over9_makes
#print axioms H2K5.Door.k5_makes_plus
#print axioms H2K5.Door.k5_makes_9
