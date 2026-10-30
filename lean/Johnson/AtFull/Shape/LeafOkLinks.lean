-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LeafOkLinks.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: AT EVERY
STATE THAT IS REACHED THERE THE TEST "WHAT SHARES A LEAF" (leafOk, Johnson/Top/H0/Tw/K2C/Asks.lean)
ACCEPTS AT EACH TREE THAT THE SWITCH OPENS, at the statement that the switch's front hands on. At
the proof file's seat, in the goals' scope, at an opening; whoever plays. A joining of two laws.

How. A tree that holds an opened message holds opened messages alone (link_own_all,
Johnson/Desc/K2/Honest/Returns/OwnFirst.lean); at such a tree the test accepts at the state's own
statement (leafOk_reached, LeafOkReached.lean); the front pushes a group and leaves the messages
(leafOk_same, Johnson/Desc/K2/Honest/Returns/SentRead.lean).

  **link_leafOk_all**: m < 23, s reached at 14 (m + 1) + 2: for each t of treesOf i and each tree at
    t in i's book: leafOk i.st tree = true, i := inFront P9 (frontAt s L Q) s.book y rL cols, at
    every L, Q, P9, y, rL, cols.

Limits. The links' places alone. "Reached" is over the list of the wrapped sub-protocols. At the
statement in front of the switch's sending, not behind it. It stands over another house's files
Returns/OwnFirst.lean and what it imports). Of a reached state: that anything is reached is not
said. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LeafOkReached
import Johnson.Desc.K2.Honest.Returns.OwnFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest.Returns (frontAt inFront treesOf link_own_all leafOk_same)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Tw.K2 (leafOk Par9 Sent Col)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **"WHAT SHARES A LEAF" AT EACH TREE THAT THE SWITCH INTO GROUP m + 1 OPENS.** -/
theorem link_leafOk_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView) (cols : List Col) :
    ∀ t ∈ treesOf (inFront P9 (frontAt s L Q) s.book y rL cols), ∀ tree,
      (inFront P9 (frontAt s L Q) s.book y rL cols).book.trees[t]? = some tree →
      leafOk (inFront P9 (frontAt s L Q) s.book y rL cols).st tree = true := by
  intro t ht tree htree
  have hp := link_own_all hS hR O h23 hr L Q P9 y rL cols t ht tree htree
  have e : leafOk (inFront P9 (frontAt s L Q) s.book y rL cols).st tree = leafOk s.st tree :=
    leafOk_same fun _ _ => rfl
  rw [e]
  exact leafOk_reached hS hR O (by omega) hr tree hp

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.link_leafOk_all
