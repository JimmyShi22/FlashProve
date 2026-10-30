-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K4.lean: K4's ROW OF THE ROUNDS' COLUMN at the full size: the declared rounds
of each block of K4's lot (`ProofFile.k4Lot`, Johnson/Desc/ProofFile/Lot/K4.lean) are the list that the
written table `listAt` (Johnson/AtFull/Rounds/ListAt.lean) gives at the name "G‹g›:3" of its group
g. UNDER PREMISES, of which (hn), on fifteen numbers of the public values, is the one of weight.

(1) What the rounds read. No kernel.
  `numsOf P hp` (Johnson/AtFull/Rounds/K4Nums.lean): the fifteen numbers that K4's table of rounds
    (`OnBytes.Desc.First.K4.rounds`, OnBytes/Desc/First/K4/Rounds.lean) reads of the layers' public
    values P and of a group's plan hp.
  `roundsN`: that table's text over a list of fifteen numbers. `rounds_eq`: the two are one, by
    `rfl`.
  `declOf`, `k4Block_rounds`, `k4Block_place`: what `ProofFile.k4Block` lays into its fields `rounds` and
    `place`, by `rfl`.
(2) The closed facts, BY THE KERNEL.
  `numsW g` (the same file): the fifteen numbers, written: read by a program off the table's two
    lists; it only proposes them. `k4Name g`: the name "G‹g›:3".
  `list_first`, `list_later`, `list_at`: at the written numbers the 170 declared rounds of the first
    group, and the 168 of each of the groups 1 to 11, are `listAt` at that group's name.
  Negative tests: `list_first_bent` (NCL raised by one), `list_later_bent` (lamS lowered by one: a
    round fewer), `list_later_bent_msg` (one end value more: as many rounds, one message longer):
    the rounds are not the table's list.
The row.
  **`k4_rounds_row`**: for public files in the goals' scope (hS, hR), where the public part Z (hZ)
    and the blank ground G₀ (hG) are returned: from (hn) at each group g below 12 and its plan hp in
    G₀.W.G: `numsOf G₀.W.layers hp = numsW g`: each block b of K4's lot at G₀ has a group g below 12
    with b.place at chain 1, link 2 g, piece 3, kind K4, and `b.rounds = listAt (k4Name g)`. By
    `IM.k4_seated` and `IM.k4_seated_scope` (Johnson/IMR/K4Seat.lean).
Whose text. `roundsN` follows `OnBytes.Desc.First.K4.rounds`: this tree's own file.

Limits. The full size alone; at the second hash function `OnBytes.secondHashFunction` alone. IT PAYS NONE OF ITS
PREMISES: that any public files meet hZ, hG or hn is shown nowhere here. That "G‹g›:3" is the name
of the place at that address is not said here. No opening is taken. Nothing on soundness. On hiding
nothing.

-/
import Johnson.AtFull.Rounds.K4Nums
import Johnson.AtFull.Rounds.ListAt
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Rd Par rounds entries entryOf pointRd batchRd masked layerRds)
open VerifiableInference.Desc (Place KindName)

/-! ## (1) What the rounds of K4's block read -/

/-- `OnBytes.Desc.First.K4.rounds` over the fifteen numbers; no round at a list of another
length. -/
def roundsN : List Nat → Nat → List Rd
  | [lt, ls, lPd, xl, NI, lNI, muV, nEnd, lamS, LamM, NCL, muH, ll, muH2, lk], g =>
    let first := g == 0
    [pointRd .zero lt] ++
    (if first then [pointRd .zero (ls + lt), pointRd .zero (lPd - ls)] else []) ++
    [batchRd (ledNS xl * NI) (ledNS xl), pointRd .join lNI] ++ layerRds muV ++
    [batchRd (ledNP xl * NI) (ledNP xl * NI)] ++ masked lt 2 2 (ledNO xl * NI) ++
    masked lt 2 1 nEnd ++ [batchRd 0 2] ++
    masked lamS 1 2 (2 + (1 + LamM) + (NCL - (if first then 1 else 0))) ++
    layerRds muH ++ [pointRd .join (ll - 1)] ++ layerRds muH2 ++
    [batchRd (if first then 1 else 0) NCL] ++ masked lk 1 1 1
  | _, _ => []

/-- **K4's table of rounds reads these fifteen numbers and the group's number alone.** -/
theorem rounds_eq (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) :
    rounds P hp g = roundsN (numsOf P hp) g := rfl

/-- A table of rounds as declared rounds: what K4's block lays into its field `rounds`. -/
def declOf (l : List Rd) : List Fmt.DeclaredRound := (l.map entryOf).map fun e => { entry := e }

/-- **The rounds of K4's block at a place.** -/
theorem k4Block_rounds (x : Bool × Par) :
    (ProofFile.k4Block x).rounds = declOf (roundsN (numsOf x.2.P x.2.hp) x.2.g) := rfl

/-- The place of K4's block. -/
theorem k4Block_place (x : Bool × Par) :
    (ProofFile.k4Block x).place = ⟨1, some x.2.link, x.2.piece, .K4⟩ := rfl

/-! ## (2) The closed facts -/

/-- The name of K4's place in the group g. -/
def k4Name (g : Nat) : String := "G" ++ toString g ++ ":3"

set_option maxRecDepth 100000 in
/-- BY THE KERNEL: at the written numbers the first group's 170 declared rounds are the table's list
at "G0:3". -/
theorem list_first : declOf (roundsN (numsW 0) 0) = listAt "G0:3" := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- BY THE KERNEL: at the written numbers the 168 declared rounds of each of the groups 1 to 11 are
the table's list at that group's name. -/
theorem list_later :
    ((List.range 11).all fun i =>
      decide (declOf (roundsN (numsW (i + 1)) (i + 1)) = listAt (k4Name (i + 1)))) = true := by
  decide +kernel

/-- So at every group below 12. -/
theorem list_at {g : Nat} (hg : g < 12) : declOf (roundsN (numsW g) g) = listAt (k4Name g) := by
  cases g with
  | zero => exact list_first
  | succ i =>
    exact of_decide_eq_true
      (List.all_eq_true.1 list_later i (List.mem_range.2 (by omega)))

/-! ## Negative tests, stated positively -/

set_option maxRecDepth 100000 in
/-- BY THE KERNEL: with NCL raised by one in the first group the rounds are not the table's list. -/
theorem list_first_bent :
    decide (declOf (roundsN ((numsW 0).set 10 34) 0) = listAt "G0:3") = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- BY THE KERNEL: with lamS lowered by one in the second group (167 rounds) they are not. -/
theorem list_later_bent :
    decide (declOf (roundsN ((numsW 1).set 8 22) 1) = listAt (k4Name 1)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- BY THE KERNEL: with the number of end values raised by one in the second group (168 rounds
against 168; one message longer) they are not. -/
theorem list_later_bent_msg :
    decide (declOf (roundsN ((numsW 1).set 7 267) 1) = listAt (k4Name 1)) = false := by
  decide +kernel

/-! ## The row -/

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **K4's ROW OF THE ROUNDS' COLUMN, BY THE GROUP.** For public files in the goals' scope, where
the public part Z and the blank ground G₀ are returned: if (hn) at each group below 12 the fifteen
numbers are the written ones: each block of K4's lot stands, for a group g below 12, at chain 1,
link 2 g, piece 3, kind K4, and its rounds are the table's list at the name "G‹g›:3". -/
theorem k4_rounds_row (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hn : ∀ g < 12, ∀ hp, G₀.W.G[g]? = some hp → numsOf G₀.W.layers hp = numsW g) :
    ∀ b ∈ (ProofFile.k4Lot Z).blocks G₀, ∃ g < 12,
      b.place = ⟨1, some (2 * g), 3, .K4⟩ ∧ b.rounds = listAt (k4Name g) := by
  intro b hb
  have hb' : b ∈ (ProofFile.k4From Z G₀ G₀.built.toList 0 none).map ProofFile.k4Block := hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb'
  obtain ⟨eP, -, -, hgp⟩ := IM.k4_seated hZ hG hx
  obtain ⟨hg, hl, hpc, -⟩ := IM.k4_seated_scope hS hR hZ hG hx
  refine ⟨x.2.g, hg, ?_, ?_⟩
  · rw [k4Block_place, hl, hpc]
  · rw [k4Block_rounds, eP, hn x.2.g hg x.2.hp hgp]
    exact list_at hg

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.rounds_eq
#print axioms Johnson.AtFull.Rounds.k4Block_rounds
#print axioms Johnson.AtFull.Rounds.k4Block_place
#print axioms Johnson.AtFull.Rounds.list_first
#print axioms Johnson.AtFull.Rounds.list_later
#print axioms Johnson.AtFull.Rounds.list_at
#print axioms Johnson.AtFull.Rounds.list_first_bent
#print axioms Johnson.AtFull.Rounds.list_later_bent
#print axioms Johnson.AtFull.Rounds.list_later_bent_msg
#print axioms Johnson.AtFull.Rounds.k4_rounds_row
