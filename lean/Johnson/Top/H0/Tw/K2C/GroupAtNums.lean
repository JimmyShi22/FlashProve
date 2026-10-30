-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/GroupAtNums.lean: code switching (the kind K2): THE TABLE's NUMBER OF A
SEGMENT's GROUP (`Numbers.groupAt`) IS THE NUMBER OF THE GROUP INTO WHICH THE SWITCH AT THAT PLACE
LEADS (`P1K2.Nums.grp`), at the table's numbers made off the list of rounds and closed over the
sub-protocols: `(P5T.numbersOf ps).atBlocks sh links bs` (Johnson/P5T/NumbersOf.lean,
Johnson/Desc/First/NumbersAtBlocks.lean). No sub-protocol imports this file.

Why. The three theorems that end in `IM.Hands` at a switch's places take the equation
`N.groupAt m = n.grp` as a premise on a letter N, bound by
`∀ P n, prepOf Z G₀ = some P → numsAt P ‹the place's link› = some n → …`. At the numbers that count
it is a fact on public numbers alone.

Letters. Z, G₀: the public parameters and the ground of the proof file's sub-protocols
(Johnson/Desc/ProofFile/). P: what `prepOf` makes once for all places. n: the numbers of the switch
at one place. l: a link's number.

  numsAt_grp       n.grp is the place's link's number; at the finish (no link) the number of the
                   links of the request's shape
  prepOf_request   the shape that P holds is the first state's frame's, and the ground's
  grp_of_id · grp_finish_of_id   the equation at every N whose `groupAt` is the identity
  grp_link · grp_finish     so at `N₀.atBlocks sh links bs`, which leaves N₀'s `groupAt`
  numbersOf_groupAt         `P5T.numbersOf ps` is such an N₀
  hgrp_link        **the equation at a link**, at every l: no premise beside the binder
  hgrp_finish      **the equation at the finish**, at segment number 25, under hlen
  prepOf_z         the sizes that P holds are the planner's own
  hgrp_finish_made   the same under hmade in the place of hlen

Limits. ONE PREMISE STAYS, at the finish alone, in one of two forms. hlen: the first state's
frame's shape has 25 links. hmade: the request's shape in the planner's sizes of the proof's chains
has 25 links: to the letter the end of `request_links_in_scope`
(Johnson/Goal/Numbers/RequestLinks.lean), which is not imported here. Each is a test with code on a
public value. Without it the equation is false: see `P1K2.Members.finish_bent`
(Johnson/Top/H0/Tw/K2C/Members/DebtsAtFull.lean). That `numsAt` answers at a place is the binder's
own premise: not shown here. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Lot.K2OfPlan
import Johnson.Desc.First.NumbersAtBlocks
import Johnson.P5T.NumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (Numbers ModelPart)

/-- The group's number at a place: the link's; at the finish the number of links. -/
theorem numsAt_grp {P : Prep} {link : Option Nat} {n : Nums} (h : numsAt P link = some n) :
    n.grp = link.getD P.z.request.link.length := by
  unfold numsAt at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, f, _, lay, _, rd, _, rfl⟩ := h
    rfl

/-- The shape that `prepOf` holds. -/
theorem prepOf_request {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {P : Prep} (h : prepOf Z G₀ = some P) :
    P.z.request = Z.s₀.check.frame.shape ∧ P.z.request = G₀.first.shape := by
  unfold prepOf prepareAt at h
  dsimp only at h
  split at h
  · cases h
  · rename_i ht
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, trees, _, rfl⟩ := h
    have ht' : tied Z.p.chains.made.sized.proof G₀.first Z.s₀.st.codes Z.s₀.check.frame.shape
        Z.P.samples = true := by simpa using ht
    unfold tied at ht'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
    exact ⟨ht'.1.2.symm, ht'.1.1.1.1⟩

/-- The sizes that `prepOf` holds are the planner's own. -/
theorem prepOf_z {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {P : Prep} (h : prepOf Z G₀ = some P) :
    P.z = Z.p.chains.made.sized.proof := by
  unfold prepOf prepareAt at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, trees, _, rfl⟩ := h
    rfl

section
variable {St Cl : Type}

/-- At a link, at every N whose `groupAt` is the identity. -/
theorem grp_of_id {N : Numbers} (hid : N.groupAt = id) {P : Prep} {l : Nat} {n : Nums}
    (h : numsAt P (some l) = some n) : N.groupAt l = n.grp := by
  rw [numsAt_grp h, hid]
  rfl

/-- At the finish, at every N whose `groupAt` is the identity. k: the number of links. -/
theorem grp_finish_of_id {N : Numbers} (hid : N.groupAt = id) {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    {k : Nat} (hlen : Z.s₀.check.frame.shape.link.length = k) {P : Prep} {n : Nums}
    (hP : prepOf Z G₀ = some P) (h : numsAt P none = some n) : N.groupAt k = n.grp := by
  rw [numsAt_grp h, (prepOf_request hP).1, hlen, hid]
  rfl

/-- At a link, at N₀ closed over the sub-protocols. -/
theorem grp_link {N₀ : Numbers} (hid : N₀.groupAt = id) (sh : Params.ReqShape) (links : List ModelPart)
    (bs : List (Block St Cl)) {P : Prep} {l : Nat} {n : Nums} (h : numsAt P (some l) = some n) :
    (N₀.atBlocks sh links bs).groupAt l = n.grp :=
  grp_of_id (N := N₀.atBlocks sh links bs) hid h

/-- At the finish, at N₀ closed over the sub-protocols. -/
theorem grp_finish {N₀ : Numbers} (hid : N₀.groupAt = id) (sh : Params.ReqShape)
    (links : List ModelPart) (bs : List (Block St Cl)) {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {k : Nat}
    (hlen : Z.s₀.check.frame.shape.link.length = k) {P : Prep} {n : Nums}
    (hP : prepOf Z G₀ = some P) (h : numsAt P none = some n) :
    (N₀.atBlocks sh links bs).groupAt k = n.grp :=
  grp_finish_of_id (N := N₀.atBlocks sh links bs) hid hlen hP h

theorem numbersOf_groupAt (ps : List P5T.PSeat) : (P5T.numbersOf ps).groupAt = id := rfl

/-- **The equation at a link.** -/
theorem hgrp_link (ps : List P5T.PSeat) (sh : Params.ReqShape) (links : List ModelPart)
    (bs : List (Block St Cl)) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : Nat) :
    ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      ((P5T.numbersOf ps).atBlocks sh links bs).groupAt l = n.grp :=
  fun _ _ _ h => grp_link (numbersOf_groupAt ps) sh links bs h

/-- **The equation at the finish.** -/
theorem hgrp_finish (ps : List P5T.PSeat) (sh : Params.ReqShape) (links : List ModelPart)
    (bs : List (Block St Cl)) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (hlen : Z.s₀.check.frame.shape.link.length = 25) :
    ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n →
      ((P5T.numbersOf ps).atBlocks sh links bs).groupAt 25 = n.grp :=
  fun _ _ hP h => grp_finish (numbersOf_groupAt ps) sh links bs hlen hP h

/-- **The equation at the finish**, from the planner's own sizes. -/
theorem hgrp_finish_made (ps : List P5T.PSeat) (sh : Params.ReqShape) (links : List ModelPart)
    (bs : List (Block St Cl)) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (hmade : Z.p.chains.made.sized.proof.request.link.length = 25) :
    ∀ P n, prepOf Z G₀ = some P → numsAt P none = some n →
      ((P5T.numbersOf ps).atBlocks sh links bs).groupAt 25 = n.grp := by
  intro P n hP h
  rw [numsAt_grp h, prepOf_z hP, Option.getD_none, hmade]
  rfl

end

end P1K2

#print axioms P1K2.numsAt_grp
#print axioms P1K2.prepOf_request
#print axioms P1K2.grp_of_id
#print axioms P1K2.grp_finish_of_id
#print axioms P1K2.grp_link
#print axioms P1K2.grp_finish
#print axioms P1K2.hgrp_link
#print axioms P1K2.hgrp_finish
#print axioms P1K2.prepOf_z
#print axioms P1K2.hgrp_finish_made
