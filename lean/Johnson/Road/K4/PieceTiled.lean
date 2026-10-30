-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PieceTiled.lean: A PIECE OF A CHAIN THAT HOLDS K4's DECLARED ROUNDS AND K4's WRITTEN
ROUNDS IS OWED JUST ITS STRETCH, AND ITS TREES ARE LISTED: the two premises `Piece.Owed` and
`Piece.Listed` that the rule of composition's `Tiled` asks of every piece
(Johnson/Desc/Sound/ChainRule.lean). A definition, statements and proofs.

A piece's written rounds (`Piece.ds`) are a free field: whoever makes the table's piece at K4's
place lays them. Here they are K4's own: the premise `k4Ds par = some pc.ds`
(Johnson/Desc/First/K4/Ds.lean; never none: `k4Ds_eq`, DsTail.lean; as an equation at a place:
`k4Ds_later`, `k4Ds_first`, Johnson/Road/K4/DsTailR.lean, which is not imported here).

General, for rounds that send no tree, open none and open no stored table:
  `treeShT_none`: the stretch has no tree. `wantsOf_bare`, `opened_nil`: its draws ask for no leaf;
    the view holds no opened leaf. `groupsOf_bare`: declared rounds of that sort read no column.
At K4:
  `k4_trees`, `k4_listed`: `Piece.trees` is 0; `Piece.Listed`: both clauses are empty of content: no
    tree is sent, none is opened. They ask nothing of the piece's block.
  `Declares b par`: the block b declares K4's rounds at the place: one round for each entry of K4's
    own table, without an opening. `Piece.Owed` reads nothing else of the block.
  `k4_owed`: `Piece.Owed`, at a piece whose block so declares and that puts no round behind its own:
    as many written rounds as the block declares; no leaf is read and none is shown. At any record
    and any type of a claim.
  `declares_block`, `declares_atS`, `declares_atC`, `declares_bare`, `declares_below`: WHICH BLOCKS
    SO DECLARE: K4's block at a seat; the block that rides at the first chain's carried record
    (`blockAtS par`); the same with its runs typed (`blockAtC par`) or struck (`bare`); and each of
    these with the test on the words in front (`below`, the rule's device).
  `k4_owed_atS`, `k4_owed_atC`, `k4_owed_bare`, `k4_owed_seat`: `k4_owed` at a piece that holds
    `below (blockAtS par)`, `below (blockAtC par)`, `below (bare (blockAtS par))` at any type of a
    claim, `below (block L par)`.

Limits. That the pieces' written rounds in a row are the file's data of the whole chain is not said
here (ChainRule.lean's own Limits: a piece's data are tied to the file's by nothing there). `base`
is free.

Nothing on soundness.
-/
import Johnson.Desc.Sound.ChainRule
import Johnson.Desc.First.K4.DsTail
import Johnson.Desc.First.K4.AtC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.Desc.First.K4
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block groupsOf)
open VerifiableInference.Desc.Sound (Frame Piece below)

/-! ### Rounds without a tree and without an opening -/

/-- A stretch that sends no tree has no tree. -/
theorem treeShT_none : ∀ (ds : List RDT), (∀ d ∈ ds, d.trees = []) → ∀ n, treeShT ds n = none
  | [], _, _ => rfl
  | d :: ds, h, n => by
    rw [treeShT_cons, h d (List.mem_cons.mpr (Or.inl rfl))]
    simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    exact treeShT_none ds (fun e he => h e (List.mem_cons.mpr (Or.inr he))) n

/-- The draws of rounds that open nothing ask for no leaf. -/
theorem wantsOf_bare (a : ℕ) (dep : ℕ → Option ℕ) : ∀ (ds : List RDT) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.opens = [] ∧ d.stored = []) → wantsOf a dep ds Rs = []
  | [], _, _ => by simp [wantsOf]
  | _ :: _, [], _ => by simp [wantsOf]
  | d :: ds, R :: Rs, h => by
    have hd := h d (List.mem_cons.mpr (Or.inl rfl))
    simp only [wantsOf, hd.1, hd.2, List.flatMap_nil, List.nil_append]
    exact wantsOf_bare a dep ds Rs fun e he => h e (List.mem_cons.mpr (Or.inr he))

/-- The view of such a stretch holds no opened leaf. -/
theorem opened_nil (C : CK) (S : StageD) (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds))
    (h : ∀ d ∈ S.ds, d.opens = [] ∧ d.stored = []) : (sView C S y τ).opened = [] := by
  have w : sWants C S (rhoT C S.ds τ) = [] := wantsOf_bare _ _ _ _ h
  show List.filterMap _ (sWants C S (rhoT C S.ds τ)) = []
  simp [w]

/-- Declared rounds that open nothing read no column. -/
theorem groupsOf_bare (ft : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → groupsOf ft ds Rs = []
  | [], _, _ => by simp [groupsOf]
  | _ :: _, [], _ => by simp [groupsOf]
  | d :: ds, R :: Rs, h => by
    have hd := h d (List.mem_cons.mpr (Or.inl rfl))
    simp only [groupsOf, hd.1, hd.2, List.map_nil, List.nil_append]
    exact groupsOf_bare ft ds Rs fun e he => h e (List.mem_cons.mpr (Or.inr he))

/-! ### K4's piece -/

variable {T Cl W : Type} {C : CK} {F : Frame}

/-- K4's stretch sends no tree. -/
theorem k4_trees (pc : Piece C F T Cl W) {par : Par} (hds : k4Ds par = some pc.ds) :
    pc.trees = 0 := by
  have hb := k4Ds_bare hds
  unfold Piece.trees
  have e : pc.ds.map (·.trees.length) = pc.ds.map fun _ => 0 :=
    List.map_congr_left fun d hd => by rw [(hb d hd).1]; rfl
  rw [e]
  simp

/-- **K4's piece's trees are listed**: it sends none and opens none. -/
theorem k4_listed (pc : Piece C F T Cl W) {par : Par} (hds : k4Ds par = some pc.ds) :
    pc.Listed := by
  have hb := k4Ds_bare hds
  refine ⟨fun n sh h => ?_, fun d hd j hj => ?_⟩
  · rw [treeShT_none pc.ds (fun d hd => (hb d hd).1) n] at h
    cases h
  · rw [(hb d hd).2.1] at hj
    cases hj

/-- The block declares K4's rounds at the place: one round for each entry of K4's own table, without
an opening. -/
def Declares (b : Block T Cl) (par : Par) : Prop :=
  b.rounds = (entries par.P par.hp par.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)

/-- **K4's piece is owed just its stretch.** -/
theorem k4_owed (pc : Piece C F T Cl W) {par : Par} (hr : Declares pc.b par)
    (hds : k4Ds par = some pc.ds) (hback : pc.back = []) : pc.Owed := by
  have hbare := k4Ds_bare hds
  have e : (rounds par.P par.hp par.g).map rdOf = pc.ds :=
    Option.some.inj ((k4Ds_eq par).symm.trans hds)
  have l : ∀ D, pc.b.reads F.ft D = [] := by
    intro D
    show groupsOf F.ft pc.b.rounds D = []
    rw [hr]
    refine groupsOf_bare _ _ _ fun d hd => ?_
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd
    exact ⟨rfl, rfl⟩
  refine ⟨?_, fun y τ => ?_⟩
  · rw [← e, hback, hr]
    simp [entries]
  · rw [l, opened_nil C pc.stage y τ fun d hd => ⟨(hbare d hd).2.1, (hbare d hd).2.2⟩]
    rfl

/-! ### Which blocks declare K4's rounds -/

/-- K4's block at a seat. -/
theorem declares_block (L : Seat T) (par : Par) : Declares (block L par) par := rfl

/-- The block that rides at the first chain's carried record. -/
theorem declares_atS (par : Par) : Declares (blockAtS par) par := rfl

/-- The same with its runs typed at the one type of a claim. -/
theorem declares_atC (par : Par) : Declares (blockAtC par) par := rfl

/-- A block without its claims and its runs behind the batching declares what the block declares. -/
theorem declares_bare {Cl' : Type} {b : Block T Cl} {par : Par} (h : Declares b par) :
    Declares (bare b : Block T Cl') par := h

/-- With the test on the words in front a block declares what it declares. -/
theorem declares_below {b : Block T Cl} {par : Par} (h : Declares b par) :
    Declares (below b) par := h

/-! ### At the blocks that stand at K4's place -/

/-- At the block that rides at the first chain's carried record. -/
theorem k4_owed_atS (pc : Piece C F VerifiableInference.Desc.First.S Aff W) {par : Par}
    (hb : pc.b = below (blockAtS par)) (hds : k4Ds par = some pc.ds) (hback : pc.back = []) :
    pc.Owed :=
  k4_owed pc (by rw [hb]; exact declares_below (declares_atS par)) hds hback

/-- At the same block with its runs typed at the one type of a claim. -/
theorem k4_owed_atC
    (pc : Piece C F VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim W) {par : Par}
    (hb : pc.b = below (blockAtC par)) (hds : k4Ds par = some pc.ds) (hback : pc.back = []) :
    pc.Owed :=
  k4_owed pc (by rw [hb]; exact declares_below (declares_atC par)) hds hback

/-- At the same block without its runs, at any type of a claim. -/
theorem k4_owed_bare (pc : Piece C F VerifiableInference.Desc.First.S Cl W) {par : Par}
    (hb : pc.b = below (bare (blockAtS par))) (hds : k4Ds par = some pc.ds)
    (hback : pc.back = []) : pc.Owed :=
  k4_owed pc (by rw [hb]; exact declares_below (declares_bare (declares_atS par))) hds hback

/-- At K4's block at a seat. -/
theorem k4_owed_seat (L : Seat T) (pc : Piece C F T Aff W) {par : Par}
    (hb : pc.b = below (block L par)) (hds : k4Ds par = some pc.ds) (hback : pc.back = []) :
    pc.Owed :=
  k4_owed pc (by rw [hb]; exact declares_below (declares_block L par)) hds hback

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_trees
#print axioms OnBytes.Road.K4.k4_listed
#print axioms OnBytes.Road.K4.k4_owed
#print axioms OnBytes.Road.K4.k4_owed_atS
#print axioms OnBytes.Road.K4.k4_owed_atC
#print axioms OnBytes.Road.K4.k4_owed_bare
#print axioms OnBytes.Road.K4.k4_owed_seat
#print axioms OnBytes.Road.K4.declares_atS
#print axioms OnBytes.Road.K4.declares_atC
