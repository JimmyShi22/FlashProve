-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormStepPlan.lean: what the stages of a proximity test ask of the plan: letters.
Public: no statement but its codes, no book, no round of a view, no value.

Main names (namespace `Johnson.Prover.Link`).
  `StepPlan p K j cur next last l c n dS dC`   the plan at the step from the stage cur (number j) to
      the stage next, at the codes K and the rounds l still to be dealt. c, n: the two stages as
      the program names them; dS, dC: the switch's two declared rounds
  `LastPlan p K j cur l c d₁ d₂`   the plan at the last stage
  `PlanFrom p`   the same from a stage on, by the frame's own recursion on the list of stages
      (`stagesFrom`, Johnson/Desc/K12/Frame.lean); with what holds of the rounds still to be dealt
      (`Dealt`, Johnson/Desc/K12/OpenLaws.lean), the plan's stages from here on, and that the first
      fold sends no mask of its own
  `PlanFrom.tail`   behind a step the plan holds from the next stage on

Limits. Letters: nothing says here that a plan meets them.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSwitch
import Johnson.Prover.Link.FormFold
import Johnson.Desc.K12.Law.ChainOf
import OnBytes.Slice.BlkSwitches
import OnBytes.Slice.Numbers
import Johnson.Desc.K12.OpenLaws
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open H2K.Pub (sgOf)

/-- **The plan at one step**: from the stage cur (number j) to the stage next, at the codes K and
the rounds l still to be dealt. c, n: the two stages as the program names them; dS, dC: the switch's
two declared rounds. -/
structure StepPlan (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool)
    (l : Laid) (c n : IoppStage) (dS dC : Fmt.DeclaredRound) : Prop where
  /-- the masks come early; a sample has one answer -/
  early : p.early = true
  one : p.answers = 1
  /-- the two stages as the program names them -/
  stage : stageAt p j cur = some c
  stageN : stageAt p (j + 1) next = some n
  idx : p.idx[j + 1]? = some (n.code, n.maskCode)
  /-- the stages' numbers -/
  hk : cur.h ≤ cur.k
  hkN : next.h ≤ next.k
  folds : 1 ≤ (sgOf cur).h + (sgOf cur).g
  ok : K12.stageOk false cur = true
  vars : cur.k + ceilLog2 cur.C.l ≤ 63
  shortN : next.Z.a ≤ next.C.a
  fits : CsFit (sgOf cur) (sgOf next)
  sized : (sgOf cur).Sized
  /-- the room of the packing in a mask row's message -/
  room : (sgOf cur).h + 2 * (sgOf cur).g + 1 ≤ (sgOf cur).Z.l
  /-- the four codes -/
  codes : StageCodes (sgOf cur) c K
  zk : (K.mask[c.maskCode]?).map codeOf = some (sgOf cur).Z
  codeN : (K.base[n.code]?).map codeOf = some (sgOf next).C
  zkN : (K.mask[n.maskCode]?).map codeOf = some (sgOf next).Z
  nk : n.k = (sgOf next).h + (sgOf next).g
  nh : n.h = (sgOf next).h
  lengths : K.lengthsOk = true
  /-- the new tables' index bits are at most 63 -/
  bounds : 2 ^ ((sgOf next).h + (sgOf next).g) * (sgOf next).C.l ≤ 2 ^ 63 ∧
    2 ^ (sgOf next).h * (sgOf next).Z.l ≤ 2 ^ 63
  /-- the frame's two cuts -/
  cutF : foldCut c.k ((l.take (1 + cur.k)).map (·.1)) = true
  cutS : ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC]
  cutSw : switchCut (sgOf cur).C.a dS dC = true
  opensS : dS.opens = []
  opensC : dC.opens.length = 1
  /-- the switch's counts -/
  drawE : dS.entry.drawE = (Send.cube K (swTarget p n).shape).bits + 1
  poss : dC.entry.poss = (sgOf cur).t
  count : dC.entry.rows = 2 + 3 * (sgOf cur).t
  /-- the switch's announcements are laid in one tree, in their order -/
  trees : Own.treesCan K (swNotices p n last) = true
  oneTree : OneTree K (OnBytes.Slice.sentOf (swTarget p n) (othersOf last n)) (sgOf next).C.a
  /-- into the last stage: the tree that this switch sends bears the base case's declared label -/
  label : last = true → p.nums.firstTree + (p.nums.free + j) = (basePar p next).label

/-- **The plan at the last stage.** -/
structure LastPlan (p : P12) (K : Codes) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (c : IoppStage)
    (d₁ d₂ : Fmt.DeclaredRound) : Prop where
  stage : stageAt p j cur = some c
  k0 : c.k = 0
  st : (sgOf cur).st = cur
  h0 : (sgOf cur).h = 0
  g0 : (sgOf cur).g = 0
  code : (K.base[c.code]?).map codeOf = some cur.C
  zk : (K.mask[c.maskCode]?).map codeOf = some cur.Z
  small : 1 + ceilLog2 cur.C.l ≤ 63
  cut : l.map (·.1) = [d₁, d₂]
  /-- "BASE lambda" draws one element; the positions of "BASE" are the main code's -/
  drawE : d₁.entry.drawE = 1
  logN : d₂.entry.logN = cur.C.a

/-- **The plan from a stage on.** -/
def PlanFrom (p : P12) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → Codes → Prop
  | [], j, cur, l, K =>
    (∃ c d₁ d₂, LastPlan p K j cur l c d₁ d₂) ∧ Dealt cur [] ((listsOf p.nums).drop j) l ∧
      p.nums.stages.drop j = [cur] ∧ p.nums.ownMask = false
  | next :: rest, j, cur, l, K =>
    (∃ c n dS dC, StepPlan p K j cur next rest.isEmpty l c n dS dC) ∧
      Dealt cur (next :: rest) ((listsOf p.nums).drop j) l ∧
      p.nums.stages.drop j = cur :: next :: rest ∧ p.nums.ownMask = false ∧
      PlanFrom p rest (j + 1) next (l.drop (cur.k + 3)) K

/-- Behind a step the plan holds from the next stage on. -/
theorem PlanFrom.tail {p : P12} {next : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {j : ℕ}
    {cur : Fmt.M1.Stage} {l : Laid} {K : Codes} (h : PlanFrom p (next :: rest) j cur l K) :
    PlanFrom p rest (j + 1) next (l.drop (cur.k + 3)) K := h.2.2.2.2

end Johnson.Prover.Link
