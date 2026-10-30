-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/StepPlanOk.lean: THE PLAN's SHARE OF THE PROXIMITY TEST's STAGES (StepPlan,
LastPlan, PlanFrom: Johnson/Prover/Link/FormStepPlan.lean) AS PUBLIC TESTS WITH CODE.

Main names (namespace Johnson.Prover.Link).
  stepPlanL, stepPlanOk   StepPlan's thirty-three fields as forty Booleans, each under its field's
    name (sized and codes have four each, bounds two); every clause says yes.
  declAt, two_of_length   the declared round at a place among those still to be dealt; a list of two
    is its two members: so no equality of declared rounds is tested.
  stepPlan_of_ok   where the test says yes StepPlan holds, at the two declared rounds behind the
    fold's.
  lastPlanL, lastPlanOk, lastPlan_of_ok   the same for LastPlan's eleven fields.
  dealtB, dealt_of_B   Dealt (Johnson/Desc/K12/OpenLaws.lean), with code.
  stageOr, planFromOk   PlanFrom by its own recursion; the letters behind "there is" are picked by
    code.
  planFrom_of_ok   WHERE THE TEST SAYS YES PlanFrom HOLDS.
  planFromNo   the names of the clauses that refuse, each behind its step's number: for a print and
    for controls.

By: csFitB, csFit_of_B, oneTreeB, oneTree_of_B (Johnson/Desc/K12/Law/PubOk.lean, ChainOf.lean): the
tests for the sizes of a switch and for "one tree", with their laws: called. Kin that cannot
be called: list_two (OnBytes/Slice/FoldPeel.lean) says what two_of_length says, and is private to
its file.

Limits. Nothing says here that the test says yes at any numbers: at a toy's, with controls:
Johnson/Prover/Link/StepPlanToy.lean; at the full size: StepPlanFull.lean. Nothing here ties
planFromNo to planFromOk but their text. The library's walk over the stages (walkL, PubOk.lean)
holds many of these clauses of the WRITTEN rounds; these tests read the DECLARED rounds with their
oracles, as the letters do; the two are tied nowhere here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormStepPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open H2K.Pub (sgOf csFitB csFit_of_B oneTreeB oneTree_of_B)

/-- **StepPlan's clauses, with code**, each under its field's name. -/
def stepPlanL (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool) (l : Laid)
    (c n : IoppStage) (dS dC : Fmt.DeclaredRound) : List (String × Bool) :=
  [("early", p.early),
   ("one", decide (p.answers = 1)),
   ("stage", decide (stageAt p j cur = some c)),
   ("stageN", decide (stageAt p (j + 1) next = some n)),
   ("idx", decide (p.idx[j + 1]? = some (n.code, n.maskCode))),
   ("hk", decide (cur.h ≤ cur.k)),
   ("hkN", decide (next.h ≤ next.k)),
   ("folds", decide (1 ≤ (sgOf cur).h + (sgOf cur).g)),
   ("ok", K12.stageOk false cur),
   ("vars", decide (cur.k + ceilLog2 cur.C.l ≤ 63)),
   ("shortN", decide (next.Z.a ≤ next.C.a)),
   ("fits", csFitB cur next),
   ("sized.small", decide ((sgOf cur).C.a ≤ 32)),
   ("sized.short", decide ((sgOf cur).Z.a ≤ (sgOf cur).C.a)),
   ("sized.roomC", decide ((sgOf cur).C.r + (sgOf cur).C.l ≤ 2 ^ (sgOf cur).C.a)),
   ("sized.roomZ", decide ((sgOf cur).Z.r + (sgOf cur).Z.l ≤ 2 ^ (sgOf cur).Z.a)),
   ("room", decide ((sgOf cur).h + 2 * (sgOf cur).g + 1 ≤ (sgOf cur).Z.l)),
   ("codes.base", decide ((K.base[c.code]?).map codeOf = some (sgOf cur).C)),
   ("codes.mask", decide (codeOf (K.mask.getD c.maskCode default) = (sgOf cur).Z)),
   ("codes.k", decide (c.k = (sgOf cur).h + (sgOf cur).g)),
   ("codes.h", decide (c.h = (sgOf cur).h)),
   ("zk", decide ((K.mask[c.maskCode]?).map codeOf = some (sgOf cur).Z)),
   ("codeN", decide ((K.base[n.code]?).map codeOf = some (sgOf next).C)),
   ("zkN", decide ((K.mask[n.maskCode]?).map codeOf = some (sgOf next).Z)),
   ("nk", decide (n.k = (sgOf next).h + (sgOf next).g)),
   ("nh", decide (n.h = (sgOf next).h)),
   ("lengths", K.lengthsOk),
   ("bounds.main", decide (2 ^ ((sgOf next).h + (sgOf next).g) * (sgOf next).C.l ≤ 2 ^ 63)),
   ("bounds.mask", decide (2 ^ (sgOf next).h * (sgOf next).Z.l ≤ 2 ^ 63)),
   ("cutF", foldCut c.k ((l.take (1 + cur.k)).map (·.1))),
   ("cutS", decide (((l.drop (1 + cur.k)).take 2).length = 2)),
   ("cutSw", switchCut (sgOf cur).C.a dS dC),
   ("opensS", dS.opens.isEmpty),
   ("opensC", decide (dC.opens.length = 1)),
   ("drawE", decide (dS.entry.drawE = (Send.cube K (swTarget p n).shape).bits + 1)),
   ("poss", decide (dC.entry.poss = (sgOf cur).t)),
   ("count", decide (dC.entry.rows = 2 + 3 * (sgOf cur).t)),
   ("trees", Own.treesCan K (swNotices p n last)),
   ("oneTree",
     oneTreeB K (OnBytes.Slice.sentOf (swTarget p n) (othersOf last n)) (sgOf next).C.a),
   ("label", !last ||
     decide (p.nums.firstTree + (p.nums.free + j) = (basePar p next).label))]

/-- The test: every clause says yes. -/
def stepPlanOk (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool) (l : Laid)
    (c n : IoppStage) (dS dC : Fmt.DeclaredRound) : Bool :=
  (stepPlanL p K j cur next last l c n dS dC).all (·.2)

/-- The declared round number i of those still to be dealt. -/
def declAt (l : Laid) (i : ℕ) : Fmt.DeclaredRound := (l.map (·.1)).getD i default

/-- A list of two is its two members. -/
theorem two_of_length {α : Type} [Inhabited α] : ∀ (l : List α), l.length = 2 →
    l = [l.getD 0 default, l.getD 1 default]
  | [_, _], _ => rfl

/-- **Where the test says yes StepPlan holds**, at the two declared rounds behind the fold's. -/
theorem stepPlan_of_ok {p : P12} {K : Codes} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool}
    {l : Laid} {c n : IoppStage}
    (h : stepPlanOk p K j cur next last l c n (declAt l (1 + cur.k)) (declAt l (1 + cur.k + 1)) =
      true) :
    StepPlan p K j cur next last l c n (declAt l (1 + cur.k)) (declAt l (1 + cur.k + 1)) := by
  unfold stepPlanOk stepPlanL at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, s1, s2, s3, s4, a14, c1, c2, c3, c4,
    a16, a17, a18, a19, a20, a21, b1, b2, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32,
    a33⟩ := h
  obtain ⟨cd, hcd, ecd⟩ := Option.map_eq_some_iff.1 c1
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, csFit_of_B a12, ⟨s1, s2, s3, s4⟩, a14,
    ⟨⟨cd, hcd, ecd⟩, c2, c3, c4⟩, a16, a17, a18, a19, a20, a21, ⟨b1, b2⟩, a23, ?_, a25,
    List.isEmpty_iff.1 a26, a27, a28, a29, a30, a31, oneTree_of_B a32, fun hl => ?_⟩
  · have e := two_of_length (((l.drop (1 + cur.k)).take 2).map (·.1)) (by
      rw [List.length_map]
      exact a24)
    rw [e]
    have hlen : 1 + cur.k + 2 ≤ l.length := by
      rw [List.length_take, List.length_drop] at a24
      omega
    unfold declAt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      List.getElem?_drop]
    simp
  · rw [hl] at a33
    simpa using a33

/-! ## The last stage -/

/-- **LastPlan's clauses, with code**, each under its field's name. -/
def lastPlanL (p : P12) (K : Codes) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (c : IoppStage)
    (d₁ d₂ : Fmt.DeclaredRound) : List (String × Bool) :=
  [("stage", decide (stageAt p j cur = some c)),
   ("k0", decide (c.k = 0)),
   ("st", decide ((sgOf cur).st = cur)),
   ("h0", decide ((sgOf cur).h = 0)),
   ("g0", decide ((sgOf cur).g = 0)),
   ("code", decide ((K.base[c.code]?).map codeOf = some cur.C)),
   ("zk", decide ((K.mask[c.maskCode]?).map codeOf = some cur.Z)),
   ("small", decide (1 + ceilLog2 cur.C.l ≤ 63)),
   ("cut", decide (l.length = 2)),
   ("drawE", decide (d₁.entry.drawE = 1)),
   ("logN", decide (d₂.entry.logN = cur.C.a))]

/-- The test: every clause says yes. -/
def lastPlanOk (p : P12) (K : Codes) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (c : IoppStage)
    (d₁ d₂ : Fmt.DeclaredRound) : Bool :=
  (lastPlanL p K j cur l c d₁ d₂).all (·.2)

/-- **Where the test says yes LastPlan holds**, at the two declared rounds that are left. -/
theorem lastPlan_of_ok {p : P12} {K : Codes} {j : ℕ} {cur : Fmt.M1.Stage} {l : Laid}
    {c : IoppStage} (h : lastPlanOk p K j cur l c (declAt l 0) (declAt l 1) = true) :
    LastPlan p K j cur l c (declAt l 0) (declAt l 1) := by
  unfold lastPlanOk lastPlanL at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8,
    two_of_length (l.map (·.1)) (by rw [List.length_map]; exact a9), a10, a11⟩

/-! ## The rounds still to be dealt -/

/-- Dealt (Johnson/Desc/K12/OpenLaws.lean), with code. -/
def dealtB (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (L : List (List Told)) (l : Laid) :
    Bool :=
  decide (l.map (·.1.opens) = fill (quiet cur rest) L) && l.all (·.1.stored.isEmpty)

theorem dealt_of_B {cur : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {L : List (List Told)}
    {l : Laid} (h : dealtB cur rest L l = true) : Dealt cur rest L l := by
  unfold dealtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, fun y hy => List.isEmpty_iff.1 (h.2 y hy)⟩

/-! ## From a stage on -/

/-- The stage as the program names it, picked by code. -/
def stageOr (p : P12) (j : ℕ) (s : Fmt.M1.Stage) : IoppStage := (stageAt p j s).getD default

/-- **PlanFrom, with code**: by its own recursion; where PlanFrom says "there is" (the stages as the
program names them; the declared rounds) the test takes the values of `stageOr` and `declAt`. -/
def planFromOk (p : P12) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → Codes → Bool
  | [], j, cur, l, K =>
    lastPlanOk p K j cur l (stageOr p j cur) (declAt l 0) (declAt l 1) &&
      dealtB cur [] ((listsOf p.nums).drop j) l && decide (p.nums.stages.drop j = [cur]) &&
      !p.nums.ownMask
  | next :: rest, j, cur, l, K =>
    stepPlanOk p K j cur next rest.isEmpty l (stageOr p j cur) (stageOr p (j + 1) next)
        (declAt l (1 + cur.k)) (declAt l (1 + cur.k + 1)) &&
      dealtB cur (next :: rest) ((listsOf p.nums).drop j) l &&
      decide (p.nums.stages.drop j = cur :: next :: rest) && !p.nums.ownMask &&
      planFromOk p rest (j + 1) next (l.drop (cur.k + 3)) K

/-- **Where the test says yes PlanFrom holds.** -/
theorem planFrom_of_ok (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage)
    (l : Laid) (K : Codes), planFromOk p rest j cur l K = true → PlanFrom p rest j cur l K
  | [], j, cur, l, K, h => by
    unfold planFromOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    exact ⟨⟨_, _, _, lastPlan_of_ok h.1.1.1⟩, dealt_of_B h.1.1.2, h.1.2, h.2⟩
  | next :: rest, j, cur, l, K, h => by
    unfold planFromOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    exact ⟨⟨_, _, _, _, stepPlan_of_ok h.1.1.1.1⟩, dealt_of_B h.1.1.1.2, h.1.1.2, h.1.2,
      planFrom_of_ok p rest (j + 1) next (l.drop (cur.k + 3)) K h.2⟩

/-- The names of the clauses that refuse, from a stage on: for a print and for controls. -/
def planFromNo (p : P12) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → Codes → List String
  | [], j, cur, l, K =>
    (((lastPlanL p K j cur l (stageOr p j cur) (declAt l 0) (declAt l 1)) ++
      [("Dealt", dealtB cur [] ((listsOf p.nums).drop j) l),
       ("stages", decide (p.nums.stages.drop j = [cur])),
       ("ownMask", !p.nums.ownMask)]).filter (!·.2)).map fun x => toString j ++ ":" ++ x.1
  | next :: rest, j, cur, l, K =>
    (((stepPlanL p K j cur next rest.isEmpty l (stageOr p j cur) (stageOr p (j + 1) next)
        (declAt l (1 + cur.k)) (declAt l (1 + cur.k + 1))) ++
      [("Dealt", dealtB cur (next :: rest) ((listsOf p.nums).drop j) l),
       ("stages", decide (p.nums.stages.drop j = cur :: next :: rest)),
       ("ownMask", !p.nums.ownMask)]).filter (!·.2)).map (fun x => toString j ++ ":" ++ x.1) ++
      planFromNo p rest (j + 1) next (l.drop (cur.k + 3)) K

end Johnson.Prover.Link
