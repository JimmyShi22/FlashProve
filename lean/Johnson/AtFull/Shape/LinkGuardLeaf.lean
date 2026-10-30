-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkGuardLeaf.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: THE
TABLE's OWN GUARD (linkGd, SwitchReturns.lean) AT EVERY STATE THAT IS REACHED THERE, WHOEVER PLAYS:
OF THE THREE FACTS ON THE BOOK's TREES THAT LinkGuardReached.lean LEFT AS PREMISES THE FIRST FALLS,
AND OF THE SECOND's FOUR CLAUSES A TREE ONE FALLS. Under the head P5J.AtMgA. A joining of laws;
nothing is evaluated here.

  hOwn (a tree that holds one of the old messages holds old messages alone): PAID by link_own_all
    (Johnson/Desc/K2/Honest/Returns/OwnFirst.lean).
  hShapes (treesShapeB, Johnson/Desc/First/Shape/SwitchLinkFits.lean: at each such tree: it is in
    the book · what shares a leaf · it has not been opened where it may be opened once · it is no
    deeper than the range): "what shares a leaf" is PAID by link_leafOk_all (LeafOkLinks.lean).
  shapes_of_three: hShapes from the three clauses that are left, said of the state's own book.
  **linkGd_reached_leaf**: the guard accepts, from hThree (these three, tree by tree) and hRead (the
    plan's list of trees read is, tree for tree in one order: the tree's number less the first
    tree's, cut off at 0 · its depth · its width).

Limits. hThree AND hRead ARE PAID BY NOBODY HERE. hThree is asked at the code that the frame's shape
names; the guard looks up the carried rows' code: the two meet because link_fields_reached gives one
code at both. Beside the head the theorem takes the opening O and the return of the plan's numbers
(hP, hn). "Reached" is over the list of the wrapped sub-protocols. The links' places alone: nothing
at 339 or 353. The full size alone. It stands over another house's files
Johnson/Desc/K2/Honest/Returns/. Of a reached state: that anything is reached is not said. That the
head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkGuardReached
import Johnson.AtFull.Shape.LeafOkLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K2 (P2 par9)
open VerifiableInference.Desc.K2.Honest.Returns
open VerifiableInference.Desc.Ground.Sh (stSh bookSh treeSh tree_get)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P1K2 (Prep Nums numsAt prepOf)
open IM (k2P)
open _root_.Desc.K14.Law (secondAt seatZ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {z : ProofFile.InstPub}

/-- **The four clauses a tree, from the three that are left.** p, L, Q are letters for the law that
is called (link_leafOk_all holds at every one): the statement does not read them. -/
theorem shapes_of_three (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s)) (p : P2)
    (L : Params.ReqLink) (Q : ReqGroup) {c : Code}
    (hThree : ∀ t ∈ treesOfS (bookSh s.book) (singleSh s.check.frame.rows), ∃ tree,
      s.book.trees[t]? = some tree ∧ (!tree.oneList || tree.lists == 0) = true ∧
        tree.shape.logN ≤ c.logN) :
    treesShapeB
      (withGroupS (stSh s.st) s.check.frame.shape.code s.check.frame.shape.maskCode)
      (bookSh s.book) c.logN (treesOfS (bookSh s.book) (singleSh s.check.frame.rows)) = true := by
  unfold treesShapeB
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨tree, htree, h10, h11⟩ := hThree t ht
  have ht' : t ∈ treesOf (dummyIn p s L Q) := by
    rw [← trees_sh]
    exact ht
  have hl := link_leafOk_all h.scope h.reads O h23 hr L Q (par9 p)
    (sentOf p s L Q noRound noRound) noRound [] t ht' tree htree
  rw [leafOk_sh] at hl
  have hl' : leafOkS
      (withGroupS (stSh s.st) s.check.frame.shape.code s.check.frame.shape.maskCode)
      (treeSh tree) = true := by
    rw [← withGroup_sh]
    exact hl
  rw [tree_get, htree]
  show (leafOkS _ (treeSh tree) && (!tree.oneList || tree.lists == 0) &&
    decide (tree.shape.logN ≤ c.logN)) = true
  rw [hl', h10, decide_eq_true h11]
  rfl

/-- **THE TABLE's OWN GUARD AT A LINK's SWITCH, AT A REACHED STATE**, from three clauses a tree and
the plan's list of trees read. -/
theorem linkGd_reached_leaf (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String)
    (hThree : ∀ c : Code, s.st.codes.base[s.check.frame.shape.code]? = some c →
      ∀ t ∈ treesOfS (bookSh s.book) (singleSh s.check.frame.rows), ∃ tree,
        s.book.trees[t]? = some tree ∧ (!tree.oneList || tree.lists == 0) = true ∧
          tree.shape.logN ≤ c.logN)
    (hRead : readsOfS (bookSh s.book) Zp.P.firstTree
      (treesOfS (bookSh s.book) (singleSh s.check.frame.rows)) = some n.read) :
    linkGd (k2P Zp a nm .link n) (chainF s) = true := by
  obtain ⟨L, Q, -⟩ :=
    link_fields_reached h.scope h.reads O h.laid.value h.laid.planOk h23 hP hn hr a nm
  exact linkGd_reached h O h23 hP hn hr a nm
    (fun L' Q' => link_own_all h.scope h.reads O h23 hr L' Q' _ _ _ _)
    (fun c hc => shapes_of_three h O h23 hr (k2P Zp a nm .link n) L Q (hThree c hc)) hRead

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.shapes_of_three
#print axioms Johnson.AtFull.Shape.linkGd_reached_leaf
