-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Batching.lean: KIND K13's JOINED SUB-PROTOCOL AT THE PLACE M:3 (K13.atM3,
Johnson/Desc/K13/AtS.lean: the front, in which the chain comes to its end; the batching of the rows
on the pile, 2 + kCol rounds; the step in front of W's commitment) AS ONE STEP ON THE SHAPE OF THE
STATE THAT THE FIRST CHAIN CARRIES (Chain.lean). General laws; nothing is evaluated.
  **`battG P`**: the step: another house's nine tests on its own shape pass (K13.Honest.readySh,
    Johnson/Desc/K13/Honest/Shape.lean, read through viewM3 of Chain.lean); the next 1 + 2 kCol free
    entries of the index masks' message are taken (Ground.Sh.takeMasksS,
    Johnson/Desc/Ground/Shape/More.lean). It lays: the chain stands at the memory; no count of rows
    waits; the core's statement behind the taking (the book of trees and the number of roots stay);
    at the memory W's message as the plan has it, no number handed on, and the claim's shape
    (K13.Honest.claimOfRow of claimSh: of the pile's rows' shapes and the entries taken).
  **`batt_carries`**: the strong form: behind a yes the step returns the shape behind. No premise on
    values.
  `batt_leaves`: a yes leaves the mark of failure and what goes out, and the makes of the
    statement's rows (Forms.lean) stay.
  **`batt_returns`**: where the step returns, the sub-protocol says yes on every list of rounds that
    fits its own rounds (roundsFit, Johnson/Desc/Block.lean), shown without the sealed digest. No
    test on values.
By another house's laws, called: shape_of_return (ShapeBack.lean), ready_of_shape (Shape.lean),
atM3_return_row (ShapeSim.lean), atM3_returns (ShapeAll.lean), laid_behind_m3 (ShapeTie.lean), all
under Johnson/Desc/K13/Honest/; and takeMasks_carries (More.lean), takeMasks_forms (Forms.lean),
shOf_view (Chain.lean).
Limits. The pile's rows' shapes (K13.Honest.RowSh) are handed on as they stand: no field of them is
read here; that type is to turn. The bare sub-protocol: the guards of a seat are not in it. No state
is shown at which the step returns. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.First.Shape.Forms
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.K13.Honest.ShapeAll
import Johnson.Desc.K13.Honest.ShapeTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh shD)
open VerifiableInference.Desc.K13.Honest (readySh shOf claimOfRow withClaim laidSh)

/-- **Kind K13's joined sub-protocol at the place M:3 (the front, the batching, the step in front of
W's commitment: K13.atM3), on the chain's shape.** Nine tests on its own shape
(readySh, read through viewM3); the next free entries of the index masks' message are taken
(takeMasksS); then: the chain stands at the memory; no count of rows waits; the core's statement
behind the taking; at the memory W's message as the plan has it, no number handed on, and the
claim's shape, made of the pile's rows' shapes and the entries taken. The default #[] at W's message
is never reached: readySh's last test is (linMessageW P.lin).isSome. -/
def battG (P : K13.Where) (a : ChainSh) : Option ChainSh :=
  if readySh P (viewM3 a) then
    (Ground.Sh.takeMasksS a.core a.indexMasks (Batt.masksOf P.lin.kCol)).map fun y =>
      ChainSh.mk a.marked 6 none none none none ⟨y.2.st, a.core.book, a.core.roots⟩ a.reply
        a.indexMasks a.pile
        (some ((linMessageW P.lin).getD #[], #[], some ⟨noId, noId, noId, none,
          claimOfRow (K13.Honest.claimSh P.lin.kCol a.pile
            (y.1.map fun i => ⟨a.indexMasks, i⟩))⟩))
        a.check none none none none none none none
  else none

/-- **"Carries", strong**: behind a yes the step returns the shape behind: no premise on values. -/
theorem batt_carries {P : K13.Where} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM3 (Cl := Unit) P).decide s rs gs = .ok t) :
    battG P (chainSh s) = some (chainSh t) := by
  have hr := K13.Honest.shape_of_return h
  obtain ⟨f, -, -, hfin, -⟩ := K13.Honest.ready_of_shape hr
  obtain ⟨y, msg, x, hd, o, hy, hm, hf, hrun, rfl⟩ := K13.Honest.atM3_return_row h
  obtain ⟨l, d'⟩ := y
  have hT := Ground.Sh.takeMasks_carries (K13.Law.dOf s) d' s.out.indexMasks _ l hy
  have hL := K13.Honest.laid_behind_m3 s d'.st msg hf hrun
  unfold battG
  rw [← shOf_view, if_pos hr]
  show (Ground.Sh.takeMasksS (shD (K13.Law.dOf s)) s.out.indexMasks _).map _ = _
  rw [hT, Option.map_some, hm]
  have hL' : laidSh { claim := memberClaim (Batt.rowOf s.out.pending o) } =
      ⟨noId, noId, noId, none, claimOfRow (K13.Honest.claimSh P.lin.kCol (shOf s).pile
        (l.map fun i => ⟨s.out.indexMasks, i⟩))⟩ := Option.some.inj hL
  congr 1
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .fin f := hfin
  show ChainSh.mk _ 6 none none none none _ _ _ _ (some (msg, #[], some _)) _ none none none none
    none none none = ChainSh.mk _ 6 none none none none _ _ _ _
      (some (msg, #[], some (laidSh { claim := memberClaim (Batt.rowOf out.pending o) }))) _ none
      none none none none none none
  rw [hL']
  rfl

/-- A yes leaves the mark of failure and what goes out; the makes of the statement's rows stay. -/
theorem batt_leaves {P : K13.Where} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM3 (Cl := Unit) P).decide s rs gs = .ok t) :
    t.failed = s.failed ∧ t.out = s.out ∧ formsOf t.st = formsOf s.st := by
  obtain ⟨y, msg, x, hd, o, hy, -, -, -, rfl⟩ := K13.Honest.atM3_return_row h
  exact ⟨rfl, rfl, takeMasks_forms hy⟩

/-- **"Returns"**: where the step returns, the sub-protocol says yes on rounds that fit its own
rounds (Block.roundsFit; as a step shows them: without the sealed digest). No test on values. Of the
step's return the proof spends only that readySh passes. -/
theorem batt_returns {P : K13.Where} {s : S} {u : ChainSh} (hg : battG P (chainSh s) = some u)
    (rs : List Fmt.RoundView) (hr : roundsFit (K13.battRounds P) rs = true)
    (gs : List (List (Nat × List UInt64))) :
    ∃ t, (K13.atM3 (Cl := Unit) P).decide s (rs.map noDigest) gs = .ok t := by
  unfold battG at hg
  split at hg
  · rename_i hc
    rw [← shOf_view] at hc
    obtain ⟨t, ht, -⟩ := K13.Honest.atM3_returns (Cl := Unit) hc rs hr gs
    exact ⟨t, ht⟩
  · cases hg

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.batt_carries
#print axioms VerifiableInference.Desc.First.Shape.batt_leaves
#print axioms VerifiableInference.Desc.First.Shape.batt_returns
#print axioms VerifiableInference.Desc.First.Shape.battG
