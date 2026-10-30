-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K8.lean: THE SMALLNESS TEST'S LOT, ITS SECOND ROW: each block's declared
rounds are the list that the written table `listAt` (Johnson/AtFull/Rounds/ListAt.lean) bears at the
written name of the block's place. At hypotheses by field. No soundness is claimed.

Why. A description's declared rounds are its blocks' rounds in a row. Laws
(Johnson/Desc/ProofFile/Law/Skel/SkelRoundsParts.lean, SkelLists.lean:
not imported here) bring "the first chain declares the written
rounds" down to one row a lot: of each block b of the lot and each spot p at b's place, b has no
round or `b.rounds = listAt p.name`. This is that row for the lot of the smallness test's draw
(Johnson/Desc/ProofFile/Lot/K8.lean). Its first row, on the blocks' skeletons, is
Johnson/AtFull/Desc/Lots/K8Row.lean.

What the rounds read. A block of the lot has one round: the name "RNG" and as many trits as the
built link's matrices have columns, times the link's number of combinations (`round`,
Johnson/Desc/First/K8/Hear.lean). So of the ground it reads, at each built link, the matrices'
numbers of columns and that number; of the public value nothing.

Main names.
  `k8TritsW`: the three written numbers of trits, by the link's kind (0 a feed-forward link, 1 an
    attention link, 2 the output head). They were read off a written literal
    (Johnson/Unfolds/DeclRecsLit.lean) and are held here by Lean's kernel (`k8Names_lists`).
  `k8TritsB G`: ONE TEST WITH CODE ON THE GROUND'S FIELDS: at each built link the number of trits
    that the block declares is the written one of the link's kind.
  `k8NameW kind nm`: the written name of the draw's place at a link: the link's name and ":5", at
    the output head ":6". The written table of the first chain's rows bears these names at the
    draw's 25 rows (`k8RowsW_names`, in the first row's file).
  `k8Rounds_whole`, `k8Place_whole`: laws at all letters, by definition: a block's rounds and place.
  `k8Names_lists` [BY THE KERNEL]: at each of the 25 written names `listAt` bears the one-round list
    at the written number of the link's kind.
  `k8Names_swapped` [BY THE KERNEL; NEGATIVE]: with the numbers of the first two kinds exchanged:
    no. Well-formed wrong data: a table that bore one list at both kinds would accept it.
  `k8Names_oneMore` [BY THE KERNEL; NEGATIVE]: every number one greater: no. Given `k8Names_lists`
    it cannot but refuse: it shows that the comparison reads the number, no more.
  `k8_rounds_at`: **THE ROW, LINK BY LINK: where the built links' kinds and names are the written
    ones and `k8TritsB G` says yes: the block at link l has the rounds `listAt` of the written name
    of its place.**
  `k8_lists_at`: **THE ROW IN THE FORM OF `Lst`: of each block b of the lot and each spot p at
    b's place: `b.rounds = listAt p.name`: UNDER ONE NAMED PREMISE MORE, hn: the spot at a draw's
    place bears the written name.** That is the right arm of `ProofFile.Sk.Lst listAt p.name b.rounds`.

Limits. THE HYPOTHESES ARE SHOWN AT NO GROUND HERE. `k8TritsB` is one test over three fields of each
built link, not an equation a field. hn IS A SEAM COMMON TO ALL LOTS' ROWS AND IS PAID NOWHERE HERE:
it is kept as a premise for one proof of all. The full size alone; the example's weights are
synthetic. No soundness is claimed.

-/
import Johnson.AtFull.Desc.Lots.K8Row
import Johnson.AtFull.Rounds.ListAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8L
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (K8.whole)
open OnBytes.Model.Stages (LinkH)
open Johnson.AtFull.Rounds (listAt)

/-! ### plain data -/

/-- The written numbers of trits, by the link's kind. -/
def k8TritsW (kind : Nat) : Nat :=
  if kind == 2 then 2649984 else if kind == 1 then 1311744 else 3083008

/-- The one-round list at a number of trits. -/
def k8RoundOn (t : Nat) : List Fmt.DeclaredRound := [{ entry := { name := "RNG", trits := t } }]

/-- The number of trits that a built link's block declares. -/
def k8TritsOf (X : LinkH) : Nat := (X.tl.mats.toList.map (·.k)).foldl (· + ·) 0 * X.tl.tau

/-- The test on the ground: at each built link that number is the written one of its kind. -/
def k8TritsB (G : ProofFile.Ground) : Bool := G.built.toList.all fun X => k8TritsOf X == k8TritsW X.kind

/-- The draw's place at a link of a kind. -/
def k8PlaceW (kind l : Nat) : Place := ⟨1, some l, if kind == 2 then 6 else 5, .K8⟩

/-- The written name of the draw's place at a link of a kind and a name. -/
def k8NameW (kind : Nat) (nm : String) : String := nm ++ (if kind == 2 then ":6" else ":5")

/-- At each written name the table bears the one-round list at f of the kind. -/
def k8NamesOkB (f : Nat → Nat) : Bool :=
  k8KindsW.all fun x => decide (listAt (k8NameW x.1 x.2) = k8RoundOn (f x.1))

/-! ### laws at all letters -/

/-- A block's rounds. -/
theorem k8Rounds_whole (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : LinkH) (l : Nat) :
    (K8.whole (ProofFile.k8ParW Z G X l)).rounds = k8RoundOn (k8TritsOf X) := rfl

/-- A block's place. -/
theorem k8Place_whole (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : LinkH) (l : Nat) :
    (K8.whole (ProofFile.k8ParW Z G X l)).place = k8PlaceW X.kind l := rfl

/-! ### closed facts -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The 25 written names bear the written lists. -/
theorem k8Names_lists : k8NamesOkB k8TritsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- With the numbers of the first two kinds exchanged: no. -/
theorem k8Names_swapped :
    k8NamesOkB (fun k => k8TritsW (if k == 0 then 1 else if k == 1 then 0 else k)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Every number one greater: no. -/
theorem k8Names_oneMore : k8NamesOkB (fun k => k8TritsW k + 1) = false := by decide +kernel

/-! ### the row -/

variable {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- **The row, link by link.** -/
theorem k8_rounds_at (hk : G.built.toList.map (fun X => (X.kind, X.name)) = k8KindsW)
    (ht : k8TritsB G = true) :
    ∀ x ∈ G.built.toList.zipIdx,
      (K8.whole (ProofFile.k8ParW Z G x.1 x.2)).rounds = listAt (k8NameW x.1.kind x.1.name) := by
  intro x hx
  have hX : x.1 ∈ G.built.toList := List.fst_mem_of_mem_zipIdx hx
  have hT : k8TritsOf x.1 = k8TritsW x.1.kind := eq_of_beq (List.all_eq_true.1 ht x.1 hX)
  have hm : (x.1.kind, x.1.name) ∈ k8KindsW := by
    rw [← hk]
    exact List.mem_map.2 ⟨x.1, hX, rfl⟩
  rw [k8Rounds_whole, hT]
  exact (of_decide_eq_true (List.all_eq_true.1 k8Names_lists _ hm)).symm

/-- **The row in the form of `Lst`, under the named premise hn.** -/
theorem k8_lists_at (hk : G.built.toList.map (fun X => (X.kind, X.name)) = k8KindsW)
    (ht : k8TritsB G = true) :
    ∀ b ∈ (ProofFile.P1K8.lot Z).blocks G, ∀ p : ProofFile.Spot, p.place = b.place →
      (∀ x ∈ k8KindsW.zipIdx, p.place = k8PlaceW x.1.1 x.2 → p.name = k8NameW x.1.1 x.1.2) →
      b.rounds = listAt p.name := by
  intro b hb p e hn
  have hb' : b ∈ ProofFile.k8Whole Z G := hb
  unfold ProofFile.k8Whole at hb'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb'
  have hm : ((x.1.kind, x.1.name), x.2) ∈ k8KindsW.zipIdx := by
    rw [← hk, List.zipIdx_map]
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  rw [hn _ hm (e.trans (k8Place_whole Z G x.1 x.2))]
  exact k8_rounds_at hk ht x hx

end P1K8L

#print axioms P1K8L.k8Rounds_whole
#print axioms P1K8L.k8Place_whole
#print axioms P1K8L.k8Names_lists
#print axioms P1K8L.k8Names_swapped
#print axioms P1K8L.k8Names_oneMore
#print axioms P1K8L.k8_rounds_at
#print axioms P1K8L.k8_lists_at
