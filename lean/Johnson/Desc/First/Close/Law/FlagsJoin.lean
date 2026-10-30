-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FlagsJoin.lean: THE FLAGS OF A LINK's GROUP, AS A WALK ALONG THE CHAIN
HAS THEM (the code switching's main message; the target's kept copies; the link's messages of the
moments 0, 1, 2 at a frame), ARE THE JOINERS' FLAGS (`joinersAt`, ReqKept.lean, beside this file):
the third of the four sentences that `shapesAre_full` (ShapesOfIds.lean) asks. Statements and
proofs.

  `flagsBy T f`: false; the flags "kept again" of the target T's kept copies; then, at the frame f,
    "its life is above 0" of the messages of the moments 0, 1 and 2.
  `flags_join`: where `byMoment s l` says yes (JoinersByMoment.lean), l is not 0, f.shape = s and
    f.link = l: `flagsBy` at the l-th group's target and f is `(joinersAt s l).map (·.2)`.
  `flags_join_full {l} (h1 : 1 ≤ l) (hl : l < 25)`, `flags_join_small`: so at the two written
    shapes.
Limits. Lists alone. That a group's flags in front of a closing are `flagsBy` at the plan's target
and frame is the end of a walk in other files (read in a text of this project that is not in this
repository; the file is not imported). Link 0 is not treated. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.JoinersByMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Params
open VerifiableInference.Desc.ReqLit

/-- The flags, sending by sending, at a target and a frame. -/
def flagsBy (T : SwitchTarget) (f : ReqFrame) : List Bool :=
  false :: T.kept.toList.map (·.keptAgain) ++
    ((f.atMoment 0).map fun m => decide (0 < m.life)) ++
    ((f.atMoment 1).map fun m => decide (0 < m.life)) ++
    ((f.atMoment 2).map fun m => decide (0 < m.life))

/-- **They are the joiners' flags.** -/
theorem flags_join {s : ReqShape} {l : ℕ} (hb : byMoment s l = true) (hl : l ≠ 0) {f : ReqFrame}
    (hs : f.shape = s) (hk : f.link = l) :
    flagsBy ((reqGroups s).getD l {}).target f = (joinersAt s l).map (·.2) := by
  unfold flagsBy
  rw [joiners_parts hb hl, atMoment_eq hs hk, atMoment_eq hs hk, atMoment_eq hs hk]
  simp [List.map_map, Function.comp_def]

theorem flags_join_full {l : ℕ} (h1 : 1 ≤ l) (hl : l < 25) {f : ReqFrame}
    (hs : f.shape = shapeFull) (hk : f.link = l) :
    flagsBy ((reqGroups shapeFull).getD l {}).target f = (joinersAt shapeFull l).map (·.2) :=
  flags_join (List.all_eq_true.1 by_moment_full l (List.mem_range.2 hl)) (by omega) hs hk

theorem flags_join_small {l : ℕ} (h1 : 1 ≤ l) (hl : l < 5) {f : ReqFrame}
    (hs : f.shape = shapeSmall) (hk : f.link = l) :
    flagsBy ((reqGroups shapeSmall).getD l {}).target f = (joinersAt shapeSmall l).map (·.2) :=
  flags_join (List.all_eq_true.1 by_moment_small l (List.mem_range.2 hl)) (by omega) hs hk

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.flags_join
#print axioms VerifiableInference.Desc.First.Close.flags_join_full
#print axioms VerifiableInference.Desc.First.Close.flags_join_small
