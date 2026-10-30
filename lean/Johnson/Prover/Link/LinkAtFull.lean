-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkAtFull.lean: THE THREE PUBLIC LISTS OF linkAll AGAINST THE ROUNDS' DATA OF
THE COPY's FILE's LINK AT THE FULL SIZE (dsFull, OnBytes/Flat/LinkSibAt.lean). linkAll's number of
rounds, the sorts of the items that each round shows and each written column's width are functions
of the place's stages (LinkShape.lean · LinkItems.lean · LinkWidths.lean): a second text of what the
protocol declares. Here the two texts are held against each other, by the kernel, at closed terms.

  frFirst, frRest, fr_cons    the place's stages, first and rest
  fr_rounds    dsFull has 6 + bodyLen rounds
  fr_sorts     each round's declared items, the roots apart, are linkAll's sorts
  fr_widths    each round's declared trees' widths: none where the list has 0, else the one number
  width_of     (general) from such an equation: a declared tree's width is the list's number
  linkNext_wide   so: every column that linkNext writes has its declared tree's width, at every
               history, at the full size: the premise hW of run_viewOf_full
               (Johnson/Prover/Link/ChainAtFull.lean)

LIMITS RAISED: set_option maxRecDepth at the four closed facts (the depth of elaboration; the kernel
checks the terms all the same), as the library does at this size
(Johnson/Desc/Link/LinkDoorsFull.lean).
Not shown here. Nothing on a decision, on soundness or on what any value discloses or does not
disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkItems
import Johnson.Prover.Link.LinkWidths
import OnBytes.Flat.LinkSibAt
import Johnson.Desc.K15.TypedP
import OnBytes.Slice.FullRecSz

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of frP)
open OnBytes.Flat (dsFull)
open TypedOracleCompiler.Run.PQ (RD)

def frFirst : Fmt.M1.Stage := (p12Of frP).nums.stages.headD default
def frRest : List Fmt.M1.Stage := (p12Of frP).nums.stages.tail

set_option maxRecDepth 100000 in
theorem fr_cons : (p12Of frP).nums.stages = frFirst :: frRest := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_rounds : dsFull.length = 6 + bodyLen frFirst frRest := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_sorts : dsFull.map (fun d => d.items.filter (· != .root)) =
    [[], [], [.answer, .answer], [], [], []] ++ bodyItems frFirst frRest := by decide +kernel

/-- No tree where the number is 0; else one tree of that width. -/
def asTrees (ws : List ℕ) : List (List ℕ) := ws.map fun w => if w = 0 then [] else [w]

set_option maxRecDepth 100000 in
theorem fr_widths : dsFull.map (fun d => d.trees.map (·.W)) =
    asTrees ([0, 3 * (frS.P.R + (frS.P.R + 1)), 0, 0, 0, 0] ++ bodyWidths frFirst frRest) := by
  decide +kernel

theorem width_of (ds : List RD) (ws : List ℕ)
    (h : ds.map (fun d => d.trees.map (·.W)) = asTrees ws) (j k : ℕ) (d : RD) (s : Fmt.Shape)
    (hd : ds[j]? = some d) (hs : d.trees[k]? = some s) : s.W = ws.getD j 0 := by
  have e := congrArg (·[j]?) h
  simp only [asTrees, List.getElem?_map, hd, Option.map_some] at e
  cases hw : ws[j]? with
  | none => rw [hw] at e; cases e
  | some w =>
    rw [hw] at e
    have e' : d.trees.map (·.W) = if w = 0 then [] else [w] := Option.some.inj e
    have e2 := congrArg (·[k]?) e'
    simp only [List.getElem?_map, hs, Option.map_some] at e2
    rw [List.getD_eq_getElem?_getD, hw]
    show s.W = w
    split at e2
    · cases e2
    · cases k with
      | zero => exact Option.some.inj e2
      | succ _ => cases e2

/-- **Every column that linkNext writes has its declared tree's width, at every history, AT THE FULL
SIZE**: the premise hW of run_viewOf_full (Johnson/Prover/Link/ChainAtFull.lean). -/
theorem linkNext_wide (t : ℕ) (X : LIn frS) (C : LCoins) (j k : ℕ) (d : RD) (s : Fmt.Shape)
    (hd : dsFull[j]? = some d) (hs : d.trees[k]? = some s) (h : List Fmt.Drawn) (x : ℕ) :
    ((linkNext frP frS t X C j h).col k x).length = s.W := by
  rw [linkNext_width frP frS t X C frFirst frRest fr_cons j h k x,
    width_of dsFull _ fr_widths j k d s hd hs]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.fr_cons
#print axioms Johnson.Prover.Link.fr_rounds
#print axioms Johnson.Prover.Link.fr_sorts
#print axioms Johnson.Prover.Link.fr_widths
#print axioms Johnson.Prover.Link.width_of
#print axioms Johnson.Prover.Link.linkNext_wide
