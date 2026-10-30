-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FenceAtBase.lean: the number of the first tree of a piece of the first row,
as a number off the list of the sub-protocols' rows (`PlanWritten.cutOf`); so, at the piece at 346
(the merge of the claims on the committed table), "every sampled tenant that is open there, and
every given member, lies in a tree that was sent in front of the piece" from tests with code.
Definitions with code, and theorems with their proofs.

Main names. G: an IOP as written in Lean, whose data D are made. R: three rows of pieces that hold
G's sub-protocols and tile its first chain, the first piece's first tree being 0.
  `toldTrees b`: how many trees the sub-protocol b tells.
  `rowTrees x`, `treesInFront cut k`: the same off a row of `cutOf`; summed over the first k rows.
  `sum_of_along`, `roots_of_shaped`, `told_sum`, `rowTrees_cut`, `treesInFront_cut`: steps.
  `trees_in_front`: the trees of the first k pieces are those that the first k sub-protocols tell.
  `base_at`: the piece at k has `base = treesInFront (PlanWritten.cutOf G.first.blocksInOrder) k`.
  `open346`: the items that are open at the border 346 of the written list of places.
  `lowAtB N O base`, `fencedB base ms`: the two tests with code; `low_of_test`, `fenced_of_test`.
  `fence_at_base`: where the first chain's rows are the written ones (`cutFirstFull`) and the two
    tests accept at `treesInFront cutFirstFull 346`: at the piece q at 346: every tenant in
    `sampledIn N open346` has its tree below q.base, and `Fenced q.base ms`.
  `base346_is`, `cut_len`: the written number; the written list has 358 rows: by the kernel.

Limits. That the first chain's rows are the written ones is a premise (a row of the verifier's entry
tests). That the two tests accept is a premise. The full size alone.
Nothing on soundness.
-/
import Johnson.Road.K4.PieceAtFits
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.Desc.First.Borders
import Johnson.Desc.Sound.WordsLaw
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Maker OnBytes.Flat
open OnBytes.Road.K4 (tiled_base fits_piece)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription Place Oracle numAt blocksOk)
open VerifiableInference.Desc.Sound
open VerifiableInference.PlanWritten (toldRounds cutFirstFull)

/-- How many trees a sub-protocol tells. -/
def toldTrees {S Cl : Type} (b : Block S Cl) : ℕ := (b.oracles.map (·.length)).sum

/-- The same, off a row of `cutOf`. -/
def rowTrees (x : String × Place × ℕ × ℕ × List (ℕ × List Oracle) × List (ℕ × ℕ)) : ℕ :=
  (x.2.2.2.2.1.map (·.2.length)).sum

/-- The trees that the first k rows tell. -/
def treesInFront (cut : List (String × Place × ℕ × ℕ × List (ℕ × List Oracle) × List (ℕ × ℕ)))
    (k : ℕ) : ℕ := ((cut.take k).map rowTrees).sum

/-- Along declared rounds and as many data: the data's trees are as many as the rounds' roots. -/
theorem sum_of_along (num : Fmt.TreeSource → ℕ) : ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT),
    Along (RoundIs num) rs ds → ds.length = rs.length →
    (ds.map (·.trees.length)).sum = (rs.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | r :: rs, d :: ds, hA, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, hA.1.2.2.2.2.2,
      sum_of_along num rs ds hA.2 (Nat.succ.inj h)]

/-- Two lists as long, with one number at each place, have one sum. -/
theorem sum_of_zip {α β : Type} (f : α → ℕ) (g : β → ℕ) : ∀ (a : List α) (b : List β),
    b.length = a.length → (∀ x ∈ a.zip b, g x.2 = f x.1) → (a.map f).sum = (b.map g).sum
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | x :: a, y :: b, h, hz => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      hz (x, y) (by rw [List.zip_cons_cons]; exact List.mem_cons_self ..),
      sum_of_zip f g a b (Nat.succ.inj h) fun z hz' =>
        hz z (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hz')]

/-- A shaped sub-protocol tells as many trees as its rounds have roots. -/
theorem roots_of_shaped {S Cl : Type} (b : Block S Cl) (h : b.shaped = true) :
    (b.rounds.map (·.entry.roots)).sum = toldTrees b := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine sum_of_zip _ _ b.rounds b.oracles (eq_of_beq h.1) fun x hx => ?_
  have h2 := h.2 x hx
  rw [Bool.and_eq_true] at h2
  exact eq_of_beq h2.1

/-- The lists that are not empty have the sum of all. -/
theorem told_sum {α : Type} : ∀ (l : List (List α)) (n : ℕ),
    (((l.zipIdx n).filter fun x => !x.1.isEmpty).map fun x => x.1.length).sum =
      (l.map (·.length)).sum
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.filter_cons]
    cases a with
    | nil => simpa using told_sum l (n + 1)
    | cons x a => simpa using told_sum l (n + 1)

theorem rowTrees_cut {S Cl : Type} (b : Block S Cl) :
    rowTrees (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before) =
      toldTrees b := by
  unfold rowTrees toldRounds toldTrees
  rw [List.map_map]
  exact told_sum b.oracles 0

theorem treesInFront_cut {S Cl : Type} (bs : List (Block S Cl)) (k : ℕ) :
    treesInFront (PlanWritten.cutOf bs) k = ((bs.take k).map toldTrees).sum := by
  unfold treesInFront PlanWritten.cutOf
  rw [← List.map_take, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => rowTrees_cut b

section
variable {Xi W : Type} {C : CK}

/-- **The trees of the first k pieces are those that the first k sub-protocols tell.** -/
theorem trees_in_front (G : FileDescription Xi) (file : String) (D : WholeD) (hD : G.data file = .ok D)
    {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W) (hO : OfDesc G R)
    (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁)
    (hb : blocksOk G.first.blocksInOrder = true) : ∀ k, k < G.first.blocksInOrder.length →
    (((R.p₁ :: R.l₁).take k).map (·.trees)).sum = ((G.first.blocksInOrder.take k).map toldTrees).sum
  | 0, _ => rfl
  | k + 1, hk => by
    have hlen : (R.p₁ :: R.l₁).length = G.first.blocksInOrder.length := by
      have h5 := congrArg List.length hO.b₁
      simpa only [List.length_map] using h5
    have hq : (R.p₁ :: R.l₁)[k]? = some ((R.p₁ :: R.l₁)[k]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hB : G.first.blocksInOrder[k]? = some (G.first.blocksInOrder[k]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    obtain ⟨-, -, hl, hA⟩ := fits_piece G file D hD R hO ht hd hq hB hk
    have hs : (G.first.blocksInOrder[k]'(by omega)).shaped = true := by
      have h1 := List.all_eq_true.1 hb _ (List.getElem_mem (by omega : k < G.first.blocksInOrder.length))
      rw [Bool.and_eq_true] at h1
      exact h1.2
    rw [List.take_add_one, List.take_add_one, hq, hB, Option.toList_some, Option.toList_some,
      List.map_append, List.map_append, List.sum_append, List.sum_append,
      trees_in_front G file D hD R hO ht hd hb k (by omega), List.map_singleton,
      List.map_singleton, List.sum_singleton, List.sum_singleton]
    congr 1
    unfold Piece.trees
    rw [sum_of_along _ _ _ hA hl, roots_of_shaped _ hs]

/-- **The first tree of the piece at k, off the sub-protocols' rows.** -/
theorem base_at (G : FileDescription Xi) (file : String) (D : WholeD) (hD : G.data file = .ok D)
    {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W) (hO : OfDesc G R)
    (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁) (h0 : R.p₁.base = 0)
    (hb : blocksOk G.first.blocksInOrder = true) {k : ℕ} (hk : k < G.first.blocksInOrder.length)
    {q : Piece C (Sound.frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) :
    q.base = treesInFront (PlanWritten.cutOf G.first.blocksInOrder) k := by
  rw [tiled_base R.l₁ R.p₁ ht k q hq, h0, Nat.zero_add,
    trees_in_front G file D hD R hO ht hd hb k hk, treesInFront_cut]

end

/-- The items that are open at the border 346 of the written list of places. -/
def open346 : List Item :=
  (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD []

/-- A test with code: every sampled tenant whose pin is open in O has its tree below base. -/
def lowAtB (N : Numbers) (O : List Item) (base : ℕ) : Bool :=
  (sampledIn N O).all fun y => decide (y.1 < base)

/-- A test with code: every member's tree is below base. -/
def fencedB (base : ℕ) (ms : List Mem) : Bool := ms.all fun x => decide ((x.1.seat x.2).1 < base)

theorem low_of_test {N : Numbers} {O : List Item} {base : ℕ} (h : lowAtB N O base = true) :
    ∀ y ∈ sampledIn N O, y.1 < base := fun y hy => of_decide_eq_true (List.all_eq_true.1 h y hy)

theorem fenced_of_test {base : ℕ} {ms : List Mem} (h : fencedB base ms = true) : Fenced base ms :=
  fun x hx => of_decide_eq_true (List.all_eq_true.1 h x hx)

set_option maxRecDepth 1000000 in
/-- The written list of the first chain's rows has 358 rows. -/
theorem cut_len : cutFirstFull.length = 358 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written rows in front of 346 tell 76 trees. -/
theorem base346_is : treesInFront cutFirstFull 346 = 76 := by decide +kernel

section
variable {Xi W : Type} {C : CK}

/-- **The fence at the piece's base, at 346.** -/
theorem fence_at_base (G : FileDescription Xi) (file : String) (D : WholeD) (hD : G.data file = .ok D)
    {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W) (hO : OfDesc G R)
    (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁) (h0 : R.p₁.base = 0)
    (hb : blocksOk G.first.blocksInOrder = true) (hc : PlanWritten.cutOf G.first.blocksInOrder = cutFirstFull)
    (N : Numbers) (ms : List Mem) (hlow : lowAtB N open346 (treesInFront cutFirstFull 346) = true)
    (hf : fencedB (treesInFront cutFirstFull 346) ms = true)
    (q : Piece C (Sound.frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W)
    (hq : (R.p₁ :: R.l₁)[346]? = some q) :
    (∀ y ∈ sampledIn N open346, y.1 < q.base) ∧ Fenced q.base ms := by
  have hk : 346 < G.first.blocksInOrder.length := by
    have e : (PlanWritten.cutOf G.first.blocksInOrder).length = G.first.blocksInOrder.length := by
      unfold PlanWritten.cutOf
      rw [List.length_map]
    rw [← e, hc, cut_len]
    decide
  rw [base_at G file D hD R hO ht hd h0 hb hk hq, hc]
  exact ⟨low_of_test hlow, fenced_of_test hf⟩

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.trees_in_front
#print axioms VerifiableInference.Desc.First.MergeLaw.base_at
#print axioms VerifiableInference.Desc.First.MergeLaw.cut_len
#print axioms VerifiableInference.Desc.First.MergeLaw.base346_is
#print axioms VerifiableInference.Desc.First.MergeLaw.fence_at_base
