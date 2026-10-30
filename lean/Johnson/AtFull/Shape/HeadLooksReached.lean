-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/HeadLooksReached.lean: at the states s that 339 accepting steps reach, the
steps being those of the first 339 blocks of the proof file's first chain, each wrapped by below (a
narrower family than the blocks' own steps reach: see the limits): s.here = .head a, and the list
s.check.frame.groups has an entry at s.check.frame.link.

Words. The chain c is the first chain of the description that ProofFile.onlineDescription makes of three public
files; the premise O : IM.Open ... (Johnson/IMR/SeatOpen.lean) names the description's parts, each
by the call that made it. c.blocksInOrder is the chain's list of blocks, numbered from 0: "the first 339
blocks" are the blocks 0 to 338, and block 339 is the one that comes next. The chain has 25
sections, which the library calls links, numbered from 0. A state s has a field s.check, its record
of the calls made so far; s.check.frame.link is a counter in it. s.here says where the chain stands
(Here, Johnson/Desc/First/State.lean); .head a is one of its six forms.

What is shown.
  head_check: where the folds over the chain's first 338 and first 339 blocks, from one first state
    and at the same rounds and columns, return the states tm and t₀: t₀.check = tm.check. It lifts
    to two folds what h1_front says of the block alone; h1_check (Johnson/IMR/FrontPin.lean) says
    the same of the block alone.
  head_looks_reached: at every s with Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s) (Reach,
    Johnson/Top/H0/Walk/Reach.lean): 339 accepting steps from a first state, at whatever rounds and
    columns: there are a and G with s.here = .head a and
    s.check.frame.groups[s.check.frame.link]? = some G. THE STEPS ARE THOSE OF THE BLOCKS AS WRAPPED
    BY below, NOT OF THE CHAIN's OWN BLOCKS: see the limits.

How. s.here = .head a: head_here_reached (Johnson/Desc/K2/Honest/Returns/LinkReached.lean). The
group: block 338 leaves the field check as it was (the last clause of h1_front,
Johnson/IMR/HeadFront.lean); after the first 338 blocks the frame's link is 24 (laid_at at l = 24,
Johnson/IMR/FrontPin.lean); the frame's groups are those of Z.first.shape (open_recAll,
Johnson/IMR/ListsEnds.lean), one more than its links (reqGroups_size, Johnson/IMR/MsgsPlaces.lean),
which are 25 by the premise h25.

Limits. WHICH STATES: below (Johnson/Desc/Sound/ChainRule.lean) is, by its own docstring, a device
of the proof that runs nowhere: the block that first tests that every word which it is handed is
below the field's prime, and then decides as the block does. What the wrapped blocks reach, the
chain's own blocks reach (reach_raw, Johnson/Top/H0/Walk/Reach.lean); the converse is not given. So
head_looks_reached speaks of the narrower family, and whoever holds Reach over c.blocksInOrder itself cannot
call it; head_here_reached, which it calls, takes the wrapped form too.
Both theorems stand under: VerifierAndGoals.InScope P = true; VerifierAndGoals.readFiles P returns; O, stated at the
hash OnBytes.secondHashFunction alone, at any layout file lay. h25 (Z.first.shape.link.length = 25) is a premise
of the second. h25_of_hy (Johnson/Desc/K2/Honest/Returns/FinAtReached.lean) gives it from
VerifierAndGoals.InScope P = true and a yes of the test madePinnedAt
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean), BUT FOR AN O AT lay := P.lay ALONE; it is not
called here. That any state is reached at 339 is not said. Nothing is said of block 339 itself.
Nothing on soundness, completeness or hiding.
-/
import Johnson.IMR.HeadFront
import Johnson.IMR.FrontPin
import Johnson.IMR.FinPin
import Johnson.IMR.ListsEnds
import Johnson.IMR.MsgsPlaces
import Johnson.Desc.K2.Honest.Returns.LinkReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest.Returns (head_here_reached)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (front_len fold_back fold_next h1_front laid_at open_recAll)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- Where the folds over the chain's first 338 and first 339 blocks, from one first state and at the
same rounds and columns, return tm and t₀: the two states have the same field check. -/
theorem head_check (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R Rm R₀ : List Fmt.RoundView} {C Cm C₀ : List VerifiableInference.Desc.OpenedColumn} {tm t₀ : S}
    (fm : foldBlocks 0 (c.blocksInOrder.take 338) (ProofFile.startS Z p) R C = .ok (tm, Rm, Cm))
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.check = tm.check := by
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope hS hR O (by decide : 24 ≤ 24) 0).trans (by omega : _ = 338)] at k
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes hS hR O hj d0).1
  obtain ⟨x, a, -, -, -, -, ec⟩ := h1_front d0'
  exact ec

/-- **At every state s that 339 accepting steps reach**, the steps being those of the chain's blocks
as wrapped by below; if the shape has 25 links: there are a and G with s.here = .head a and
s.check.frame.groups[s.check.frame.link]? = some G. -/
theorem head_looks_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (h25 : Z.first.shape.link.length = 25) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) :
    ∃ a G, s.here = .head a ∧ s.check.frame.groups[s.check.frame.link]? = some G := by
  obtain ⟨a, ha⟩ := head_here_reached hS hR O hr
  obtain ⟨-, rs, cl, f⟩ := (reach_raw hr).fold
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f
  have hl : s.check.frame.link = 24 := by
    rw [head_check hS hR O fm f]
    exact (laid_at hS hR O (l := 24) (by omega) fm).2
  have RA : Meaning.K2.RecAll Z.first.codes Z.first.shape s :=
    open_recAll hS hR O (by omega : 2 ≤ 339) (by rw [front_len hS hR O]; omega) f
  have hgs : s.check.frame.link < s.check.frame.groups.size := by
    rw [RA.walk.groups, Meaning.Carry.reqGroups_size, hl, h25]
    omega
  exact ⟨a, _, ha, Array.getElem?_eq_getElem hgs⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.head_check
#print axioms Johnson.AtFull.Shape.head_looks_reached
