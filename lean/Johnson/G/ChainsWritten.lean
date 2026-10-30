-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/ChainsWritten.lean: the routine that makes the seven chains (`chainsOf`,
OnBytes/Model/VerifyChains.lean) with a written value in the planner's place; and that it returns
the planner's chains, to the letter, wherever the planner makes that written value.

What it is for. `chainsOf` calls the planner twice: `Params.sized` for the sizes and
`Params.configure` for the plans and the parameter bytes. `chainsOfW` has its text with these two
lines turned: the four fields that do not hang on the digest (`Free`, Johnson/G/MadeFree.lean) are
picked by the parameter file's lines from written values, and the eight strings are spelled of them
(`spelled`, Johnson/G/MadeSpelled.lean). It is a brick for a description that takes the plan as
data.

All that is here are tools: the picking is a letter, and so is the routine that makes the shapes.
They name no file and no written value.

What stays of the text, to the token: the making of the links and shapes from the public part;
`linksFit`; the three readers of the parameter bytes, at the spelled strings.
Of what the planner asked of the run's shapes, these are kept as plain lines, refused under the
planner's own name for them: the shapes' two numbers of rows of the matrix are the same (the first
line of `sized`); what the key file's proof of the ranges looks up is what the written sizes of the
key file were made from (`rangesTie`: the second step of `Plan.keySized`, `Plan.rangesLines`, is run
on the shapes, and all six fields of what it gives are held against the written sizes' own); one
identifier for each link, one notice at the start, a pending row, one plain scalar in the last link
alone (four conditions of `configure`).
What leaves the text with the planner: the sizing and the pricing; the tests of `sized` on the
finished shapes; the four gates of OnBytes/Params/Gate.lean (`missedInTheLinks`,
`missedInTheRanges`, `missedOnTheTable`, `missedInTheChecks`); `Plan.keyOk`; the caller's bits. At a
written value those that read the sizes and plans alone are closed questions: they are owed there as
closed facts, and none is typed here. `missedInTheLinks` and `missedInTheChecks` also read the run's
shapes: they are not kept, and whether something else on this road asks what they ask is not settled
here.

Definitions.
  `chainsBy sh`: the text of `chainsOf` with the routine that makes the shapes as the letter sh.
  `rangesTie l s K`; `tailW l links x W cfg`: what follows the picking; `chainsOfW sh pick`.
Statements and proofs.
  `chainsOf_by`: `chainsOf` is `chainsBy shapesOf`.
  `rangesSized_lines`, `rangesTie_of_sized`: where `sized` returns, `rangesTie` says yes.
  `exc_pass`, `exc_stop`, `exc_step`: steps of a routine that can refuse. `tailW_ok`.
  `chainsOfW_of`: if `chainsBy sh X lay cfg` returns ch and the picking gives `freeOf ch.made`, then
    `chainsOfW sh pick X lay cfg` returns ch.
  Where it refuses: `chainsOfW_no_pick`: lines for which nothing is written; `tailW_no_rows`,
    `tailW_no_ranges`, `tailW_no_four`: a shape that fails a kept line.

What of OnBytes/Model/ is used: `Verify.Public`, `Verify.Chains`, `Verify.chainsOf`,
`Verify.shapesOf`, `Stages.LinkH`, `Stages.linksFit`.

Limits. The tie goes one way: from a planner that returns the written value. That it does so at any
public files is not said here: the proof file's sizes and first plan hang on the run's shapes. Where
the planner refuses, or makes another value, `chainsOfW` may still return. That the kept lines are
all that is needed is argued in no theorem. Nothing on soundness.
-/
import Johnson.G.MadeSpelled
import OnBytes.Model.VerifyChains
import OnBytes.Params.Fit.SizedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.MadeFree
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages

/-- The text of `chainsOf` with the routine that makes the links and the shapes as a letter. -/
def chainsBy (sh : Public → Option ByteArray → Except String (Array LinkH × Params.Shapes))
    (X : Public) (layoutFile : Option ByteArray) (cfg : ByteArray) : Except String Chains := do
  let (links, shapes) ← sh X layoutFile
  let z ← Params.sized X.P.frame shapes
  linksFit links z.proof.codes z.proof.request shapes.layout z.proof.batch.shape.kCol
  let made ← Params.configure X.P.frame shapes cfg 0
  match Params.KeyChains.read made.keyOneTime made.keyShared made.keySecond,
      Params.Link.read made.entryLink,
      Params.ProofChains.read made.first made.shared made.second with
  | some key, some link, some proof =>
    pure { made := made, key := key, link := link, proof := proof }
  | _, _, _ => throw "internal-parameter-bytes-not-read"

theorem chainsOf_by (X : Public) (layoutFile : Option ByteArray) (cfg : ByteArray) :
    chainsOf X layoutFile cfg = chainsBy shapesOf X layoutFile cfg := rfl

/-- What the key file's proof of the ranges looks up is what the sizes K were made from. -/
def rangesTie (l : Lines) (s : Plan.Shape) (K : Plan.KeySized) : Bool :=
  match Plan.rangesLines { s with kCol := l.blockLog } l.onceRanges l.rangesPart with
  | some L =>
    decide (L.kCol = K.ranges.lines.kCol) && decide (L.matrixRows = K.ranges.lines.matrixRows) &&
      decide (L.lookups = K.ranges.lines.lookups) && decide (L.group = K.ranges.lines.group) &&
      decide (L.masksRide = K.ranges.lines.masksRide) &&
      decide (L.messageId = K.ranges.lines.messageId)
  | none => false

/-- What follows the picking of the written value W. -/
def tailW (l : Lines) (links : Array LinkH) (shapes : Params.Shapes) (W : Free)
    (cfg : ByteArray) : Except String Chains := do
  let z := W.sized
  if shapes.sub.matrixRows != shapes.ranges.matrixRows then throw notAdmitted
  if !rangesTie l shapes.ranges z.key then throw notAdmitted
  linksFit links z.proof.codes z.proof.request shapes.layout z.proof.batch.shape.kCol
  if shapes.identifiers.length != z.proof.request.link.length ||
      z.proof.request.atStart.length != 1 || shapes.sub.pendingRows == 0 ||
      z.proof.request.link.map (·.plain) !=
        List.replicate (z.proof.request.link.length - 1) 0 ++ [1] then
    throw notAdmitted
  let made := W.at (spelled W shapes cfg)
  match Params.KeyChains.read made.keyOneTime made.keyShared made.keySecond,
      Params.Link.read made.entryLink,
      Params.ProofChains.read made.first made.shared made.second with
  | some key, some link, some proof =>
    pure { made := made, key := key, link := link, proof := proof }
  | _, _, _ => throw "internal-parameter-bytes-not-read"

/-- **The seven chains, with a written value in the planner's place.** pick: which written value
goes with the parameter file's lines, if any. -/
def chainsOfW (sh : Public → Option ByteArray → Except String (Array LinkH × Params.Shapes))
    (pick : Lines → Option Free) (X : Public) (layoutFile : Option ByteArray) (cfg : ByteArray) :
    Except String Chains := do
  let (links, shapes) ← sh X layoutFile
  match pick X.P.frame with
  | some W => tailW X.P.frame links shapes W cfg
  | none => throw notAdmitted

/-! ## Where the planner makes the written value -/

/-- What `rangesSized` returns holds the lines that it was given. -/
theorem rangesSized_lines {s : Setting} {L : Plan.RangesLines} {codes c : Codes}
    {z : Plan.RangesSized} (h : Plan.rangesSized s L codes = some (z, c)) : z.lines = L := by
  unfold Plan.rangesSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨last, _, h⟩ := opt_bind h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨test, _, h⟩ := opt_bind h
  split at h
  obtain ⟨first, _, h⟩ := opt_bind h
  replace h := opt_guard h
  cases h
  rfl

/-- Where `sized` returns, the tie on the ranges holds. -/
theorem rangesTie_of_sized {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    rangesTie l x.ranges z.key = true := by
  obtain ⟨T, L, rows, codes1, _, hL, _, _, hR⟩ := keySized_parts (sized_key h)
  have e := rangesSized_lines hR
  unfold rangesTie
  rw [hL, e]
  simp

/-! ## Steps of a routine that can refuse -/

theorem exc_pass {ε β : Type} {c : Prop} [Decidable c] {e : ε} {next : PUnit → Except ε β}
    (hc : ¬ c) :
    (if c then (throw e : Except ε PUnit) >>= next else pure PUnit.unit >>= next) =
      next PUnit.unit := by
  rw [if_neg hc]
  rfl

theorem exc_stop {ε β : Type} {c : Prop} [Decidable c] {e : ε} {next : PUnit → Except ε β}
    (hc : c) :
    (if c then (throw e : Except ε PUnit) >>= next else pure PUnit.unit >>= next) = .error e := by
  rw [if_pos hc]
  rfl

theorem exc_step {ε α β : Type} {x : Except ε α} {a : α} {f : α → Except ε β} (h : x = .ok a) :
    (x >>= f) = f a := by
  rw [h]
  rfl

/-- Where the kept lines pass and the readers accept the spelled strings, `tailW` returns. -/
theorem tailW_ok {l : Lines} {links : Array LinkH} {shapes : Params.Shapes} {W : Free}
    {cfg : ByteArray} {key : Params.KeyChains} {link : Params.Link} {proof : Params.ProofChains}
    {u : Unit} (h1 : ¬ (shapes.sub.matrixRows != shapes.ranges.matrixRows) = true)
    (h2 : rangesTie l shapes.ranges W.sized.key = true)
    (h3 : linksFit links W.sized.proof.codes W.sized.proof.request shapes.layout
      W.sized.proof.batch.shape.kCol = .ok u)
    (h4 : ¬ (shapes.identifiers.length != W.sized.proof.request.link.length ||
        W.sized.proof.request.atStart.length != 1 || shapes.sub.pendingRows == 0 ||
        W.sized.proof.request.link.map (·.plain) !=
          List.replicate (W.sized.proof.request.link.length - 1) 0 ++ [1]) = true)
    (hk : Params.KeyChains.read (W.at (spelled W shapes cfg)).keyOneTime
      (W.at (spelled W shapes cfg)).keyShared (W.at (spelled W shapes cfg)).keySecond = some key)
    (hl : Params.Link.read (W.at (spelled W shapes cfg)).entryLink = some link)
    (hq : Params.ProofChains.read (W.at (spelled W shapes cfg)).first
      (W.at (spelled W shapes cfg)).shared (W.at (spelled W shapes cfg)).second = some proof) :
    tailW l links shapes W cfg =
      .ok { made := W.at (spelled W shapes cfg), key := key, link := link, proof := proof } := by
  have h2' : ¬ (!rangesTie l shapes.ranges W.sized.key) = true := by
    rw [h2]
    decide
  unfold tailW
  refine (exc_pass h1).trans ?_
  refine (exc_pass h2').trans ?_
  refine (exc_step h3).trans ?_
  refine (exc_pass h4).trans ?_
  simp only [hk, hl, hq]
  rfl

/-- **Where the planner makes the written value, the routine returns the planner's chains.** -/
theorem chainsOfW_of
    {sh : Public → Option ByteArray → Except String (Array LinkH × Params.Shapes)}
    {pick : Lines → Option Free} {X : Public} {layoutFile : Option ByteArray} {cfg : ByteArray}
    {ch : Chains} (h : chainsBy sh X layoutFile cfg = .ok ch)
    (hp : pick X.P.frame = some (freeOf ch.made)) :
    chainsOfW sh pick X layoutFile cfg = .ok ch := by
  unfold chainsBy at h
  obtain ⟨⟨links, shapes⟩, hsh, h⟩ := exc_bind h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨u, hfit, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  have hzm : z = made.sized := Except.ok.inj (hz.symm.trans (configure_plans hm).1)
  have hM := configure_hung hm
  have hr : rangesTie X.P.frame shapes.ranges made.sized.key = true := by
    rw [← hzm]
    exact rangesTie_of_sized hz
  rw [hzm] at hfit
  split at h
  · rename_i key link proof hk hl hq
    cases h
    have hp' : pick X.P.frame = some (freeOf made) := hp
    rw [hM] at hk hl hq
    have t := tailW_ok (l := X.P.frame) (links := links) (shapes := shapes) (W := freeOf made)
      (cfg := cfg) (sized_rows hz) hr hfit (configure_kept hm) hk hl hq
    unfold chainsOfW
    refine (exc_step hsh).trans ?_
    show (match pick X.P.frame with
      | some W => tailW X.P.frame links shapes W cfg
      | none => throw notAdmitted) = _
    rw [hp']
    refine t.trans ?_
    rw [← hM]
  · cases h

/-! ## Where it refuses -/

/-- Lines for which nothing is written are refused. -/
theorem chainsOfW_no_pick
    {sh : Public → Option ByteArray → Except String (Array LinkH × Params.Shapes)}
    {pick : Lines → Option Free} {X : Public} {layoutFile : Option ByteArray} {cfg : ByteArray}
    {links : Array LinkH} {shapes : Params.Shapes} (hsh : sh X layoutFile = .ok (links, shapes))
    (hp : pick X.P.frame = none) : chainsOfW sh pick X layoutFile cfg = .error notAdmitted := by
  unfold chainsOfW
  refine (exc_step hsh).trans ?_
  show (match pick X.P.frame with
    | some W => tailW X.P.frame links shapes W cfg
    | none => throw notAdmitted) = _
  rw [hp]
  rfl

/-- Shapes with two numbers of rows of the matrix are refused. -/
theorem tailW_no_rows {l : Lines} {links : Array LinkH} {shapes : Params.Shapes} {W : Free}
    {cfg : ByteArray} (h : (shapes.sub.matrixRows != shapes.ranges.matrixRows) = true) :
    tailW l links shapes W cfg = .error notAdmitted := by
  unfold tailW
  exact exc_stop h

/-- Shapes whose ranges are not those of the written sizes are refused. -/
theorem tailW_no_ranges {l : Lines} {links : Array LinkH} {shapes : Params.Shapes} {W : Free}
    {cfg : ByteArray} (h1 : ¬ (shapes.sub.matrixRows != shapes.ranges.matrixRows) = true)
    (h : rangesTie l shapes.ranges W.sized.key = false) :
    tailW l links shapes W cfg = .error notAdmitted := by
  have h' : (!rangesTie l shapes.ranges W.sized.key) = true := by
    rw [h]
    rfl
  unfold tailW
  refine (exc_pass h1).trans ?_
  exact exc_stop h'

/-- Shapes that fail one of the four conditions are refused. -/
theorem tailW_no_four {l : Lines} {links : Array LinkH} {shapes : Params.Shapes} {W : Free}
    {cfg : ByteArray} {u : Unit}
    (h1 : ¬ (shapes.sub.matrixRows != shapes.ranges.matrixRows) = true)
    (h2 : rangesTie l shapes.ranges W.sized.key = true)
    (h3 : linksFit links W.sized.proof.codes W.sized.proof.request shapes.layout
      W.sized.proof.batch.shape.kCol = .ok u)
    (h : (shapes.identifiers.length != W.sized.proof.request.link.length ||
        W.sized.proof.request.atStart.length != 1 || shapes.sub.pendingRows == 0 ||
        W.sized.proof.request.link.map (·.plain) !=
          List.replicate (W.sized.proof.request.link.length - 1) 0 ++ [1]) = true) :
    tailW l links shapes W cfg = .error notAdmitted := by
  have h2' : ¬ (!rangesTie l shapes.ranges W.sized.key) = true := by
    rw [h2]
    decide
  unfold tailW
  refine (exc_pass h1).trans ?_
  refine (exc_pass h2').trans ?_
  refine (exc_step h3).trans ?_
  exact exc_stop h

end Johnson.G.MadeFree

#print axioms Johnson.G.MadeFree.chainsOf_by
#print axioms Johnson.G.MadeFree.rangesSized_lines
#print axioms Johnson.G.MadeFree.rangesTie_of_sized
#print axioms Johnson.G.MadeFree.exc_pass
#print axioms Johnson.G.MadeFree.exc_stop
#print axioms Johnson.G.MadeFree.exc_step
#print axioms Johnson.G.MadeFree.tailW_ok
#print axioms Johnson.G.MadeFree.chainsOfW_of
#print axioms Johnson.G.MadeFree.chainsOfW_no_pick
#print axioms Johnson.G.MadeFree.tailW_no_rows
#print axioms Johnson.G.MadeFree.tailW_no_ranges
#print axioms Johnson.G.MadeFree.tailW_no_four
