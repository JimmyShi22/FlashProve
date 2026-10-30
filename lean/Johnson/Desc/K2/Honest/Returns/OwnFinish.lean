-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/OwnFinish.lean: `ReadFits.own` (Returns/Read.lean) AT THE PLACE
BEHIND THE LAST SEGMENT, BEHIND ITS QUIET FRONT, AT A STATE THAT IS REACHED AT THE NUMBER 353, IN
THE GOALS' SCOPE, WITH NO TEST ON THE PUBLIC PART. With Returns/OwnReached.lean: 24 OF THE KIND's 25
PLACES; the switch into group 1 is left. Statements with their proofs: calls.

  `mates_opened24` THE CORE, from the fold's return at 353: in the book there, a message that has
                    the tree of one of the messages that the carried rows name is itself named by
                    them. `mates_opened` (Returns/OwnReached.lean) at the last segment's numbers:
                    its lines stand here again
  `fin_own_reached` `ReadFits.own`, in its own letters, at `inFront P9 (finFrontOf t a Q) t.book y
                    rL cols`: for all Q, P9, y, rL, cols; t the state behind the quiet front

By, this folder's: `members_behind_cleared`, `fresh_behind_cleared`, `counts_head`
(Returns/HeadSegment.lean) · `mem_ids`, `tree_of_opened` (Returns/OwnReached.lean) · `cut_kept`,
`cut_mates` (Returns/CutsKept.lean) · `partsPlaced_reached`, `own_of_places`
(Returns/PartsPlaced.lean) · `fin_book_reached` (Returns/ArmsFree.lean) · `finishFrontQ_rows`
(Returns/ClosedArms.lean). The library's: `open_has` (Johnson/IMR/WalkGivesAt.lean) · `open_recAll`
(Johnson/IMR/ListsEnds.lean), `rows_of_pub` (Johnson/IMR/FrontPin.lean), `fin_link`, `front_len`
(Johnson/IMR/FinPin.lean): two masks · `fold_cut` (Johnson/IMR/GroupRest.lean) · `finishFrontQ_rest`
(Johnson/Top/H0/Tw/K2C/FinFront.lean) · `reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean).

Limits. The quiet front's yes and `here` are premises. "Reached" is: over the list of the wrapped
sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. This file's
imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.OwnReached
import Johnson.Desc.K2.Honest.Returns.HeadSegment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S FinOwn)
open VerifiableInference.Desc.First.K2 (finFrontOf finishFrontQ finishFrontQ_rest)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (open_has open_recAll rows_of_pub fin_link front_len fold_cut frontOf)
open _root_.Tw.K2 (Par9 Sent Col)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **A message of an opened message's tree is opened: the last segment's.** -/
theorem mates_opened24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (353)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    {o q τ j j' : Nat} (ho : o ∈ (singleRowsOracles t₂.check.frame.rows).toList)
    (po : t₂.book.place[o]? = some (τ, j)) (pq : t₂.book.place[q]? = some (τ, j')) :
    q ∈ (singleRowsOracles t₂.check.frame.rows).toList := by
  have hk : 353 ≤ (frontOf c).length := le_of_eq (front_len hS hR O).symm
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, g₀, g₃, g₅, hmem⟩ :=
    members_behind_cleared hS hR O f₂
  have hfresh := fresh_behind_cleared hS hR O g₀ f₂
  obtain ⟨t₁, R₁, C₁, g₁⟩ := fold_cut (k := 340) 13 f₂
  obtain ⟨t₄, R₄, C₄, g₄⟩ := fold_cut (k := 343) 10 f₂
  obtain ⟨t₆, R₆, C₆, g₆⟩ := fold_cut (k := 345) 8 f₂
  obtain ⟨c1, c4, c6⟩ := counts_head hS hR O g₀ g₁ g₃ g₄ g₅ g₆
  have hmasks : t₂.check.frame.rows.masks = 2 :=
    (rows_of_pub (open_recAll hS hR O (by omega) hk f₂).walk
      (by rw [fin_link hS hR O f₂]; omega)).2.2
  have hids : singleRowsOracles t₂.check.frame.rows =
      t₂.check.frame.rows.layout.members.push t₂.check.frame.rows.fresh := by
    unfold singleRowsOracles
    rw [hmasks]
    rfl
  rw [hids, hmem, hfresh, mem_ids] at ho ⊢
  have K₀ := cut_kept O (by omega : 339 ≤ 353) hk g₀ f₂
  have K₁ := cut_kept O (by omega : 340 ≤ 353) hk g₁ f₂
  have K₃ := cut_kept O (by omega : 342 ≤ 353) hk g₃ f₂
  have K₄ := cut_kept O (by omega : 343 ≤ 353) hk g₄ f₂
  have K₅ := cut_kept O (by omega : 344 ≤ 353) hk g₅ f₂
  have K₆ := cut_kept O (by omega : 345 ≤ 353) hk g₆ f₂
  rw [open_has O (by omega) g₀] at K₀
  rw [open_has O (by omega) g₁, c1] at K₁
  rw [open_has O (by omega) g₃] at K₃
  rw [open_has O (by omega) g₄, c4] at K₄
  rw [open_has O (by omega) g₅] at K₅
  rw [open_has O (by omega) g₆, c6] at K₆
  rcases ho with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl (cut_mates K₀ K₁ po pq a b)
  · exact Or.inr (Or.inl (cut_mates K₃ K₄ po pq a b))
  · exact Or.inr (Or.inr (cut_mates K₅ K₆ po pq a b))

/-- **`ReadFits.own` behind the quiet front of the place behind the last segment.** -/
theorem fin_own_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (hq : finishFrontQ s = .ok t)
    {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List OpenedColumn) :
    ∀ τ ∈ treesOf (inFront P9 (finFrontOf t a Q) t.book y rL cols), ∀ tree,
      (inFront P9 (finFrontOf t a Q) t.book y rL cols).book.trees[τ]? = some tree →
      ∀ q ∈ tree.parts.toList,
        q ∈ (idsOf (inFront P9 (finFrontOf t a Q) t.book y rL cols)).toList := by
  have hlen : 353 ≤ (frontOf c).length := le_of_eq (front_len hS hR O).symm
  obtain ⟨-, rs, cl, f₂⟩ := (reach_raw hr).fold
  have eb : t.book = s.book := (finishFrontQ_rest hq).1
  obtain ⟨a', ha', hrows⟩ := finishFrontQ_rows hq
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.fin a' = .fin a := ha'.symm.trans here
    cases e
    rfl
  have hP : partsPlaced t.book s.roots := by
    rw [eb]
    exact partsPlaced_reached O (reach_raw hr) hlen
  refine own_of_places (i := (inFront P9 (finFrontOf t a' Q) t.book y rL cols)) (r := s.roots) hP
    fun q τ k pq hτ => ?_
  obtain ⟨o, ho, e⟩ := tree_of_opened hτ
  have hlt := (fin_book_reached hS hR O hr hq here Q P9 y rL cols).1 o ho
  have hlt' : o < t.book.place.size := hlt
  have po : t.book.place[o]? = some (τ, (t.book.place.getD o (0, 0)).2) := by
    have e' : (t.book.place.getD o (0, 0)).1 = τ := e
    rw [← e', Array.getElem?_eq_getElem hlt']
    simp [Array.getD, hlt']
  have pq' : t.book.place[q]? = some (τ, k) := pq
  rw [eb] at po pq'
  have ho' : o ∈ (singleRowsOracles s.check.frame.rows).toList := by
    rw [← hrows]
    exact ho
  show q ∈ (singleRowsOracles a'.fr.rows).toList
  rw [hrows]
  exact mates_opened24 hS hR O f₂ ho' po pq'

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.mates_opened24
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_own_reached
