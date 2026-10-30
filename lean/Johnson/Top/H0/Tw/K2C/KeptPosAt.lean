-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/KeptPosAt.lean: code switching (the kind K2): EVERY KEPT MEMBER OF THE TARGET
THAT A SWITCH IS HANDED HAS A MAIN ROW (`KeptPos x.T`), at each of the three sorts of place at
which a switch stands: a link, the output head's link, the finish. No sub-protocol imports this
file.

Why. `KeptPos x.T` is the first field of `LinkDebts` and `SwitchDebts`
(Johnson/Top/H0/Tw/K2C/HandsLink.lean, HandsCore.lean): there it is a premise on the front x that
the switch takes off the verifier's state. Here it follows from two facts on that state and one
test on the public shape.

Letters. s: the verifier's state in front of the switch (at the finish: in front of the step
"F.0.front", which leads to the switch). t: at the finish, the state that this step hands to the
switch. x: the front that the switch takes off the state. sh: the request's public shape.

The three premises, the same in all three theorems:
  hshape   s.check.frame.shape = sh
  hgroups  s.check.frame.groups = reqGroups s.check.frame.shape
  hok      reqShapeOk sh = true
hshape and hgroups are, to the letter, what the fields `shape` and `groups` of `FoldFacts`
(Johnson/Desc/First/FoldFacts.lean) say of a state; hok is part of the test `reqOk`, which
`ReqFrame.start` puts (OnBytes/Iop/Req.lean).

  keptPosB_of_keptPos   the test with code `K2Hands.keptPosB` (Johnson/Top/H0/K2Hands/FrontPub.lean)
                     accepts wherever `KeptPos` holds: the converse of that file's
                     `keptPos_of_test`: so a reject of the test refutes `KeptPos`
  keptPos_group      a group of a lawful shape: its target has `KeptPos`
                     (`Meaning.K2.kept_pos_at`, Johnson/Goal/Meaning/KeptRowsPos.lean)
  keptPos_atLink     at a link: x is what `firstFront` makes of the state
  keptPos_atFront    at a link or the output head's link: x is `frontAt p s`
  keptPos_atFinish   at the finish: x is `frontAt p t`

Beside. `K2.keptPos_link` (Johnson/Goal/Meaning/K2Share/FrontPlan.lean) says the like at a link's
place alone, for `frontAt p s`, from a structure that also asks the codes and `reqOk`. It is not
imported here.

Limits. AT THE FINISH THE END SAYS NOTHING AT A LAWFUL SHAPE: nothing is kept beyond the last link
(`reqShapeOk`), so the last group's target has no kept member: the field is idle there, and
`keptPos_atFinish` pays an idle field. The like at the first group. The three premises are met by
nobody here. Nothing on the other five fields of the two
structures. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.Tw.K2C.PositionAtPlan
import Johnson.Goal.Meaning.KeptRowsPos
import Johnson.Top.H0.K2Hands.FrontPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (firstFront)

/-- The test with code accepts wherever `KeptPos` holds. -/
theorem keptPosB_of_keptPos {T : SwitchTarget} (h : KeptPos T) : K2Hands.keptPosB T = true := by
  unfold K2Hands.keptPosB
  rw [Array.all_eq_true]
  intro i hi
  exact decide_eq_true (h i hi)

/-- The target of a group of a lawful shape. -/
theorem keptPos_group {sh : Params.ReqShape} (hok : reqShapeOk sh = true) {l : Nat} {G : ReqGroup}
    (hG : (reqGroups sh)[l]? = some G) : KeptPos G.target :=
  _root_.Meaning.K2.kept_pos_at hok hG

/-- **At a link.** -/
theorem keptPos_atLink {s : S} {x : _root_.Tw.K2.Front} {sh : Params.ReqShape}
    (hx : firstFront s.st s.check.frame = .ok x) (hshape : s.check.frame.shape = sh)
    (hgroups : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hok : reqShapeOk sh = true) : KeptPos x.T := by
  obtain ⟨L, G, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
  have hG := a.group
  rw [hgroups, hshape] at hG
  have e : x.T = G.target := by rw [a.out]
  rw [e]
  exact keptPos_group hok hG

/-- **At a link or the output head's link.** -/
theorem keptPos_atFront {p : P2} {s : S} {x : _root_.Tw.K2.Front} {sh : Params.ReqShape}
    (h : frontAt p s = some x) (hp : p.stands ≠ .finish) (hshape : s.check.frame.shape = sh)
    (hgroups : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hok : reqShapeOk sh = true) : KeptPos x.T := by
  rcases front_target h with ⟨e, _⟩ | ⟨_, G, hG, e⟩
  · exact absurd e hp
  · rw [hgroups, hshape] at hG
    rw [e]
    exact keptPos_group hok hG

/-- **At the finish.** The two facts are asked of s, the state in front of "F.0.front". -/
theorem keptPos_atFinish {p : P2} {s t : S} {x : _root_.Tw.K2.Front} {sh : Params.ReqShape}
    (he : finishFrontQ s = .ok t) (h : frontAt p t = some x) (hp : p.stands = .finish)
    (hshape : s.check.frame.shape = sh)
    (hgroups : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hok : reqShapeOk sh = true) : KeptPos x.T := by
  obtain ⟨a, G, ha, hG, hgr, _, _, _, hfg, _⟩ := finishFrontQ_fr he
  rcases front_target h with ⟨_, a', G', ha', hG', e⟩ | ⟨hn, _⟩
  · cases ha.symm.trans ha'
    obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
    rw [hfg, hgroups, hshape] at hgr
    rw [e]
    exact keptPos_group hok hgr
  · exact absurd hp hn

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.keptPosB_of_keptPos
#print axioms VerifiableInference.Desc.First.K2.keptPos_group
#print axioms VerifiableInference.Desc.First.K2.keptPos_atLink
#print axioms VerifiableInference.Desc.First.K2.keptPos_atFront
#print axioms VerifiableInference.Desc.First.K2.keptPos_atFinish
