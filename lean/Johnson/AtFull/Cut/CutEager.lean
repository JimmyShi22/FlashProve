-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Cut/CutEager.lean: AN EAGER TWIN OF THE FIRST CHAIN's TABLE OF STRETCHES (`cutOf`,
Johnson/Desc/First/Driver/Cut.lean), WITH ITS LAW `cutOfK_eq : cutOfK es = cutOf es`, so that Lean's
kernel can evaluate the table at a list of some tens of thousands of names without running out of
stack. Definitions with code and their laws; nothing is evaluated here.

Why. `upTo s ns` asks `ns.length` of THE WHOLE REST of the list at every call, and `cutOf` and
`finishCut` hand `ns.length` on as fuel. The kernel evaluates `List.length` by plain recursion, as
deep as the list is long. The twin asks neither:
  `upToE s a ns`: walks to the first s and counts eagerly (`Johnson.G.force`, Johnson/G/Eager.lean);
    `upToK s ns := upToE s 0 ns`; `upToK_eq : upToK s ns = upTo s ns`.
  the fuel is `Johnson.G.lenE 0 ns` (`lenE_eq`).
EVERYTHING ELSE IS THE FILE's OWN TEXT, COPIED BY PROGRAM, each name with a K behind it:
`lookLenK` · `scoresLenK` · `tailCutK` · `linkCutK` · `linksCutK` · `stagesCutK` · `finishCutK` ·
`membersCutK` · `cutOfK`; `begins` and `doorLen`, which read a short front alone, are called as they
are. Each copy has its law `…K_eq`: it IS the original, at every argument.
Limits. General: no value is treated. That the kernel gets through a given list is seen where a
theorem is checked. What `cutOf` is worth is its own file's to say. Nothing on soundness. On hiding
nothing.

-/
import Johnson.Desc.First.Driver.Cut
import Johnson.G.Eager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Cut
open VerifiableInference.Desc.First
open Johnson.G (force force_eq lenE lenE_eq)

/-- a plus the number of names in front of the first that is s; none if s does not come. -/
def upToE (s : String) : Nat → List String → Option Nat
  | _, [] => none
  | a, x :: xs => if x != s then force (a + 1) fun v => upToE s v xs else some a

/-- `upTo`, without the whole list's length. -/
def upToK (s : String) (ns : List String) : Option Nat := upToE s 0 ns

theorem upToE_eq (s : String) (ns : List String) : ∀ a,
    upToE s a ns = (upTo s ns).map (a + ·) := by
  induction ns with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    by_cases hx : (x != s) = true
    · have h1 : upTo s (x :: xs) = (upTo s xs).map (1 + ·) := by
        unfold upTo
        simp only [List.takeWhile_cons, hx, if_true, List.length_cons, Nat.add_lt_add_iff_right]
        split
        · simp only [Option.map_some, Nat.add_comm]
        · rfl
      rw [h1]
      simp only [upToE, hx, if_true, force_eq, ih, Option.map_map]
      congr 1
      funext k
      simp only [Function.comp_apply, Nat.add_assoc]
    · have h1 : upTo s (x :: xs) = some 0 := by
        unfold upTo
        simp only [List.takeWhile_cons, hx, List.length_cons]
        simp
      rw [h1]
      simp only [upToE, hx, Option.map_some, Nat.add_zero]
      rfl

theorem upToK_eq (s : String) (ns : List String) : upToK s ns = upTo s ns := by
  unfold upToK
  rw [upToE_eq]
  cases upTo s ns with
  | none => rfl
  | some k => simp only [Option.map_some, Nat.zero_add]

theorem lenE_zero {α : Type} (l : List α) : lenE 0 l = l.length := by
  rw [lenE_eq, Nat.zero_add]

/-- `lookLen`, over the eager twins. -/
def lookLenK (ns : List String) : Option Nat :=
  if !(begins ["LKP shift", "LKP"] ns || ns.head? == some "LKP") then none
  else (upToK "ZERO" ns).bind fun a => (upToK "PSC values" (ns.drop a)).map fun b => a + b + 1

/-- `scoresLen`, over the eager twins. -/
def scoresLenK (ns : List String) : Option Nat :=
  (upToK "BAT-sigma" ns).bind fun b =>
    ((ns.take b).zipIdx.filter fun x => x.1 == "PSC epsilon").getLast?.map (·.2)

/-- `tailCut`, over the eager twins. -/
def tailCutK (c L : String) (i pl : Nat) (head : Bool) (claims : List (String × String))
    (ns : List String) : Option (List Cut × Nat × List String) := do
  let at' := fun (j : Nat) (w : String) => L ++ "." ++ toString j ++ "." ++ w
  if !begins ["SEND seed", "SEND answer", "RNG", "SEND seed", "SEND answer"] ns then none
  let n₁ := ns.drop 5
  let k ← lookLenK n₁
  let n₂ := n₁.drop k
  let m ← upToK "BAT" n₂
  if m == 0 || (n₂.drop (m - 1)).head? != some "BAT-sigma" || (!head && m != 1) then none
  let n₃ := n₂.drop m
  let d := doorLen n₃
  if d == 0 then none
  let j := if head then i + 5 else i + 4
  let q := if head then pl + 5 else pl + 4
  pure (
    [⟨at' i "call", c ++ "Reads", pl, "send", 2⟩, ⟨at' i "quiet", c ++ "ReadsQuiet", pl, "send", 0⟩,
     ⟨at' (i + 1) "call", c ++ "Draw", pl + 1, "rng", 1⟩,
     ⟨at' (i + 2) "call", c ++ "Digits", pl + 2, "send", 2⟩,
     ⟨at' (i + 3) "call", c ++ "DigitsLook", pl + 3, "lookupDigits", k⟩,
     ⟨at' (i + 3) "quiet", c ++ "DigitsQuiet", pl + 3, "lookupDigits", 0⟩] ++
    (if head then
      [⟨at' (i + 4) "call", c ++ "Merge", pl + 4, "merge", m - 1⟩,
       ⟨at' (i + 4) "quiet", c ++ "MergeQuiet", pl + 4, "merge", 0⟩] else []) ++
    [⟨at' j "call", c ++ "Batch", q, "batSigma", 1⟩] ++
    (claims.map fun x => ⟨at' j x.1, c ++ x.2, q, "batSigma", 0⟩) ++
    [⟨at' (j + 1) "call", c ++ "Door", q + 1, "batFold", d⟩,
     ⟨at' (j + 1) "quiet", c ++ "DoorQuiet", q + 1, "batFold", 0⟩], q + 2, n₃.drop d)

/-- `linkCut`, over the eager twins. -/
def linkCutK (g a pl : Nat) (ns : List String) :
    Option (List Cut × Nat × Nat × Nat × Bool × List String) := do
  let isHead := ns.head? == some "REPLY"
  let n₀ := if isHead then ns.drop 1 else ns
  let first := pl == 0 && !isHead
  if !begins ["SEND seed", if first then "SEND answer" else "LOC"] n₀ then none
  let fk := if first then "send" else "sendLoc"
  let n₁ := n₀.drop 2
  let k ← lookLenK n₁
  let n₂ := n₁.drop k
  let o ← upToK "SEND seed" n₂
  if o == 0 then none
  if isHead then
    let (t, pl', rest) ← tailCutK "s" "H" 4 (pl + 4) true
      [("front", "WalkFront"), ("objects", "Objects"), ("back", "WalkBack"), ("quiet", "Tests")]
      (n₂.drop o)
    pure ([⟨"H.0.front", "sFront", pl, "reply", 0⟩, ⟨"H.0.call", "sReply", pl, "reply", 1⟩,
      ⟨"H.1.call", "sSwitch", pl + 1, fk, 2⟩, ⟨"H.1.quiet", "sSwitchQuiet", pl + 1, fk, 0⟩,
      ⟨"H.2.call", "sLook", pl + 2, "lookupCalls", k⟩,
      ⟨"H.3.call", "sOwn", pl + 3, "headRow", o⟩,
      ⟨"H.3.quiet", "sOwnQuiet", pl + 3, "headRow", 0⟩] ++ t, g, a, pl', true, rest)
  else if n₂.head? == some "PSC epsilon" then
    let L := "A" ++ toString a
    let sc ← scoresLenK (n₂.take o)
    let zr ← upToK "ZERO" n₂
    if !(decide (sc < zr) && decide (zr < o)) then none
    let (t, pl', rest) ← tailCutK "a" L 3 (pl + 3) false
      [("claims", "Claims"), ("objects", "Objects"), ("quiet", "Tests")] (n₂.drop o)
    pure ([⟨L ++ ".0.call", "aFirst", pl, fk, 2⟩, ⟨L ++ ".0.quiet", "aFirstQuiet", pl, fk, 0⟩,
      ⟨L ++ ".1.call", "aLook", pl + 1, "lookupCalls", k⟩,
      ⟨L ++ ".2.scores", "aScores", pl + 2, "chain", sc⟩,
      ⟨L ++ ".2.divide", "aDivide", pl + 2, "chain", zr - sc⟩,
      ⟨L ++ ".2.call", "aAttain", pl + 2, "chain", o - zr⟩] ++ t, g, a + 1, pl', false, rest)
  else
    let L := "G" ++ toString g
    let (t, pl', rest) ← tailCutK "g" L 3 (pl + 3) false
      [("front", "ClaimsFront"), ("objects", "Objects"), ("back", "ClaimsBack"), ("quiet", "Tests")]
      (n₂.drop o)
    pure ([⟨L ++ ".0.call", "gFirst", pl, fk, 2⟩, ⟨L ++ ".0.quiet", "gFirstQuiet", pl, fk, 0⟩,
      ⟨L ++ ".1.call", "gLook", pl + 1, "lookupCalls", k⟩,
      ⟨L ++ ".1.quiet", "gLookQuiet", pl + 1, "lookupCalls", 0⟩,
      ⟨L ++ ".2.call", "gOwn", pl + 2, "chain", o⟩] ++ t, g + 1, a, pl', false, rest)

/-- `linksCut`, over the eager twins. -/
def linksCutK : (fuel g a pl : Nat) → List String → Option (List Cut × Nat × List String)
  | 0, _, _, _, _ => none
  | fuel + 1, g, a, pl, ns => do
    let (rows, g', a', pl', wasHead, rest) ← linkCutK g a pl ns
    if wasHead then pure (rows, pl', rest)
    else
      let (more, pl'', rest') ← linksCutK fuel g' a' pl' rest
      pure (rows ++ more, pl'', rest')

/-- `stagesCut`, over the eager twins. -/
def stagesCutK : (fuel i pl : Nat) → List String → Option (List Cut × Nat × List String)
  | 0, _, _, _ => none
  | fuel + 1, i, pl, ns =>
    if ns.head? == some "FOLD epsilon" then do
      let c ← upToK "CS" ns
      let (more, j, rest) ← stagesCutK fuel (i + 1) pl (ns.drop (c + 1))
      pure ([⟨"F." ++ toString i ++ ".call", "fStage", pl, "test", c + 1⟩,
        ⟨"F." ++ toString i ++ ".quiet", "fStageQuiet", pl, "test", 0⟩] ++ more, j, rest)
    else some ([], i, ns)

/-- `finishCut`, over the eager twins. -/
def finishCutK (pl : Nat) (ns : List String) : Option (List Cut × Nat × List String) := do
  if !begins ["SEND seed", "LOC", "BAT"] ns then none
  let (st, i, rest) ← stagesCutK (lenE 0 ns) 2 (pl + 1) (ns.drop 3)
  if !begins ["BASE lambda", "BASE"] rest then none
  pure ([⟨"F.0.front", "fFront", pl, "sendLoc", 0⟩, ⟨"F.0.call", "fSwitch", pl, "sendLoc", 2⟩,
    ⟨"F.0.quiet", "fSwitchQuiet", pl, "sendLoc", 0⟩,
    ⟨"F.1.front", "fBatFront", pl + 1, "test", 0⟩, ⟨"F.1.call", "fBat", pl + 1, "test", 1⟩,
    ⟨"F.1.quiet", "fBatQuiet", pl + 1, "test", 0⟩] ++ st ++
    [⟨"F." ++ toString i ++ ".call", "fBase", pl + 1, "test", 2⟩], pl + 2, rest.drop 2)

/-- `membersCut`, over the eager twins. -/
def membersCutK (pl : Nat) (ns : List String) : Option (List Cut) := do
  let b ← upToK "SEND seed" ns
  if b != 0 && ns.head? != some "BAT-sigma" then none
  if (ns.drop b) != ["SEND seed", "SEND answer", "SEAL"] then none
  let q := if b == 0 then pl else pl + 1
  pure [⟨"M.0.front", "mFront", pl, "batPsc", 0⟩, ⟨"M.0.call", "mBatt", pl, "batPsc", b⟩,
    ⟨"M.0.quiet", "mBattQuiet", pl, "batPsc", 0⟩, ⟨"M.1.call", "mSend", q, "send", 2⟩,
    ⟨"M.1.quiet", "mSendQuiet", q, "send", 0⟩, ⟨"seal.behind", "seal", q + 1, "SEAL", 0⟩]

/-- `cutOf`, over the eager twins. -/
def cutOfK (es : List Fmt.Entry) : Option (List Cut) := do
  let ns := es.map (·.name)
  let (a, pl, r₁) ← linksCutK (lenE 0 ns) 0 0 0 ns
  let (b, pl', r₂) ← finishCutK pl r₁
  let c ← membersCutK pl' r₂
  pure (a ++ b ++ c)

theorem lookLenK_eq (ns : List String) : lookLenK ns = lookLen ns := by
  simp only [lookLenK, lookLen, upToK_eq]

theorem scoresLenK_eq (ns : List String) : scoresLenK ns = scoresLen ns := by
  simp only [scoresLenK, scoresLen, upToK_eq]

theorem tailCutK_eq (c L : String) (i pl : Nat) (head : Bool) (claims : List (String × String))
    (ns : List String) : tailCutK c L i pl head claims ns = tailCut c L i pl head claims ns := by
  simp only [tailCutK, tailCut, upToK_eq, lookLenK_eq]

theorem linkCutK_eq (g a pl : Nat) (ns : List String) : linkCutK g a pl ns = linkCut g a pl ns := by
  simp only [linkCutK, linkCut, upToK_eq, lookLenK_eq, scoresLenK_eq, tailCutK_eq]

theorem linksCutK_eq : ∀ (fuel g a pl : Nat) (ns : List String),
    linksCutK fuel g a pl ns = linksCut fuel g a pl ns := by
  intro fuel
  induction fuel with
  | zero => intro g a pl ns; rfl
  | succ n ih => intro g a pl ns; simp only [linksCutK, linksCut, linkCutK_eq, ih]

theorem stagesCutK_eq : ∀ (fuel i pl : Nat) (ns : List String),
    stagesCutK fuel i pl ns = stagesCut fuel i pl ns := by
  intro fuel
  induction fuel with
  | zero => intro i pl ns; rfl
  | succ n ih => intro i pl ns; simp only [stagesCutK, stagesCut, upToK_eq, ih]

theorem finishCutK_eq (pl : Nat) (ns : List String) : finishCutK pl ns = finishCut pl ns := by
  simp only [finishCutK, finishCut, stagesCutK_eq, lenE_zero]

theorem membersCutK_eq (pl : Nat) (ns : List String) : membersCutK pl ns = membersCut pl ns := by
  simp only [membersCutK, membersCut, upToK_eq]

/-- **THE TWIN IS THE TABLE, AT EVERY LIST OF ENTRIES.** -/
theorem cutOfK_eq (es : List Fmt.Entry) : cutOfK es = cutOf es := by
  simp only [cutOfK, cutOf, linksCutK_eq, finishCutK_eq, membersCutK_eq, lenE_zero]

end Johnson.AtFull.Cut

#print axioms Johnson.AtFull.Cut.upToE_eq
#print axioms Johnson.AtFull.Cut.upToK_eq
#print axioms Johnson.AtFull.Cut.lenE_zero
#print axioms Johnson.AtFull.Cut.lookLenK_eq
#print axioms Johnson.AtFull.Cut.scoresLenK_eq
#print axioms Johnson.AtFull.Cut.tailCutK_eq
#print axioms Johnson.AtFull.Cut.stagesCutK_eq
#print axioms Johnson.AtFull.Cut.linkCutK_eq
#print axioms Johnson.AtFull.Cut.linksCutK_eq
#print axioms Johnson.AtFull.Cut.finishCutK_eq
#print axioms Johnson.AtFull.Cut.membersCutK_eq
#print axioms Johnson.AtFull.Cut.cutOfK_eq
