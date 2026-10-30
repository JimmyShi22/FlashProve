-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BaseIsRoots.lean (no file of this library imports it): THE
PIECE's BASE IS THE NUMBER OF ROOTS THAT THE VERIFIER's STATE HAS COUNTED, at every state that is
reached in front of the piece, along the whole first chain of the proof file's description, in the
goals' scope. A JOIN OF THREE SETS OF FILES' LEMMAS; the join alone is this file's.

WHAT FOR (another's words): K02_law [not in this library] seats a switch's new members at (q.base +
the layout's tree, part); the book behind an acceptance seats them at (p.firstTree + (s.roots + the
layout's tree), part): the two are one only if q.base = p.firstTree + s.roots at the state in front.
The first tree's number is 0 there.
  rootsOf_blocks: the declared roots of a list of blocks, block by block. fileAt Z A B c: the
      description at an opening's letters (ProofFile.fileDescBy …): so that the first chain's type of a
      state is S by unfolding.
  base_is_roots: **InScope P · readFiles P = .ok pp · O : Open OnBytes.secondHashFunction … (fileAt Z A B c) … ·
      OfDesc (fileAt Z A B c) T · Tiled T.p₁ T.l₁ · T.p₁.base = 0 · hA: along every piece of the
      first row the stretch's data are those of its block's declared rounds (Along (RoundIs num)
      x.b.rounds x.ds) · every block of c.blocksInOrder passes its test on the plan · (T.p₁ :: T.l₁)[k]? =
      some q · Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s) ⇒ q.base = s.roots.**
THE PREMISE ON REACHING is RchAt (fileAt Z A B c) k a, unfolded
(Johnson/Top/H0/Walk/ReachAt.lean: RchAt F k a := Reach 0 (F.first.blocksInOrder.map below)
F.start₁ k a.1), at a.1 = (z, s). Johnson/Top/H0/Walk/ReachAt.lean itself is not imported.
NO "no mark" IS ASKED: the count holds at every fold's return.
THE THREE EQUATIONS. (1), (2) THE PLAN's
HALF: base_declared (Johnson/Top/H0/K2Hears/BaseAtPiece.lean): q.base = p.base + the
declared roots of the pieces in front; kind-free, at every size. OfDesc.b₁: the pieces hold the
blocks ("below" and "lift" keep the rounds). (3) THE STATE's HALF: reach_raw and Reach.fold
(Johnson/Top/H0/Walk/Reach.lean) · roots_at_cut_whole
(Johnson/IMR/RootsWhole.lean) · start_empty (Johnson/IMR/BookSeat.lean).
WHO CAN PAY. hA: stretchOfData (Johnson/Desc/Sound/Stretch.lean), at the maker's pieces.
T.p₁.base = 0: Three.Fits.base₁ (Johnson/Desc/Sound/FileRule.lean; not shown here). Tiled, OfDesc:
the rule of composition's own premises. The tests on the plan: F.planOk.
FELLOWS, NOT CALLED: base_at_flat (Johnson/Desc/Sound/BaseOfBookFit.lean: it wants
Johnson/Desc/First/BookNumbers.lean beneath) · trees_along (Johnson/Desc/Book/SeatOfLay.lean):
BaseAtPiece.lean has the like of both (base_at, trees_of_along) within itself.
OBJECT · USER · LETTERS. Object: the first row of pieces over ProofFile.onlineDescription OnBytes.secondHashFunction's value,
in scope. User: K02_law (every sender's tie). Letters: T, num.
Limits. In scope alone. No member: that a state is reached is shown of no proof. Book-keeping.
Nothing on soundness.
-/
import Johnson.IMR.RootsWhole
import Johnson.Top.H0.K2Hears.BaseAtPiece
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Sound.DescThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Maker
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Piece Tiled Along RoundIs OfDesc ThreeAt below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G.OfPlan (rootsOf)
open _root_.Run.PQ (CK)
open ProofFile (Cl)

/-- The declared roots of a list of blocks, block by block. -/
theorem rootsOf_blocks {T Cl : Type} : ∀ l : List (Block T Cl),
    rootsOf (H2K.First.declOf l) = (l.map fun b => (b.rounds.map (·.entry.roots)).sum).sum
  | [] => rfl
  | b :: l => by
    show rootsOf (b.rounds ++ H2K.First.declOf l) = _
    rw [H2K.First.rootsOf_append, rootsOf_blocks l, List.map_cons, List.sum_cons]
    rfl

/-- The proof file's description at an opening's letters. -/
abbrev fileAt (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE PIECE's BASE IS THE NUMBER OF ROOTS THAT THE VERIFIER's STATE HAS COUNTED**, at every
state that is reached in front of the piece, along the whole first chain, in the goals' scope. -/
theorem base_is_roots (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL (fileAt Z A B c) Z Bs base c A B) {C : CK}
    {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type} {T : ThreeAt C D all (fileAt Z A B c) X₁ X₂ W}
    (hT : OfDesc (fileAt Z A B c) T) (ht : Tiled T.p₁ T.l₁) (h0 : T.p₁.base = 0)
    {num : Fmt.TreeSource → Nat} (hA : ∀ x ∈ T.p₁ :: T.l₁, Along (RoundIs num) x.b.rounds x.ds)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : Nat} {q} (hq : (T.p₁ :: T.l₁)[k]? = some q)
    {z : ProofFile.InstPub} {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) :
    q.base = s.roots := by
  have e1 := First.K2.base_declared T.p₁ T.l₁ ht hA hq
  rw [h0, Nat.zero_add] at e1
  have e2 : ((T.p₁ :: T.l₁).take k).map (fun x => (x.b.rounds.map (·.entry.roots)).sum) =
      (c.blocksInOrder.take k).map fun b => (b.rounds.map (·.entry.roots)).sum := by
    have e := congrArg (fun l => (l.take k).map fun b => (b.rounds.map (·.entry.roots)).sum) hT.b₁
    simpa [List.map_take, List.map_map, Function.comp_def] using e
  obtain ⟨hk, rs, cols, hf⟩ := (Johnson.Desc.First.Walk.Tied.reach_raw hr).fold
  have e3 := roots_at_cut_whole hS hR O 0 _ rs cols k (by rw [← flat_len hS hR O]; exact hk)
    (fun b hb => hp b (List.mem_of_mem_take hb)) _ hf
  rw [(Meaning.K2.start_empty O.pub z).2, Nat.zero_add, rootsOf_blocks] at e3
  rw [e1, e2]
  exact e3.symm

#print axioms base_is_roots

end Meaning.Carry
