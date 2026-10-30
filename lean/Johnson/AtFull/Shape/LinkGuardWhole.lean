-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkGuardWhole.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: THE
TABLE's OWN GUARD (linkGd, SwitchReturns.lean) ACCEPTS AT EVERY STATE THAT IS REACHED THERE, WHOEVER
PLAYS: NO PREMISE ON THE BOOK's TREES IS LEFT. Under the head P5J.AtMgA, at an opening O in the
head's letters, and where the plan's numbers at the place return (hP, hn). A joining of laws;
nothing is evaluated here.

How. LinkGuardLeaf.lean left hThree (each tree that holds one of the carried rows' messages is in
the book, has not been opened where it may be opened once, is no deeper than the range) and hRead
(the plan's list of trees read). Another group's files have them at a reached state, in another
form: link_unopened_all (Johnson/Desc/K2/Honest/Returns/UnopenedFirst.lean: such a tree has been
opened at no list) and link_five_reached (Returns/FiveReached.lean: AllFive, Returns/FiveTest.lean:
along the trees and the plan's list, pair by pair: in the book · no deeper than the written depth ·
number, depth, width), under six premises that the head pays (six_at_head, Returns/TiedReached.lean,
which gives a seventh fact too, on the codes: it is spent for the depth).

  allFive_there, allFive_reads: GENERAL: AllFive gives "in the book, no deeper" at each tree of the
    list, and the equation readsOfS … = some rd (Johnson/Desc/First/Shape/SwitchLinkFits.lean).
  **linkGd_reached_whole**.

Limits. O, hP, hn stay premises beside the head. "Reached" is over the list of the wrapped
sub-protocols. The links' places alone: nothing at 339 or 353. THE GUARD ALONE: that the step on
shapes returns behind it, and the tests on values, are other laws'. The full size alone: beneath
stand closed tests at the written values that Lean's kernel has evaluated (the other group's
five_full; ours of LinkLeftPlan.lean and its fellows). It stands over another house's files
Johnson/Desc/K2/Honest/Returns/). Of a reached state: that anything is reached is not said. That the
head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkGuardLeaf
import Johnson.Desc.K2.Honest.Returns.TiedReached

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
open VerifiableInference.Desc.Ground.Sh (bookSh tree_get)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (recAll_reached front_len frontOf pub_firstTree)
open P1K2 (Prep Nums numsAt prepOf)
open IM (k2P)
open _root_.Desc.K14.Law (secondAt seatZ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- AllFive: each tree of the list is in the book and no deeper than logN. -/
theorem allFive_there {ft logN : Nat} {B0 : TreeBook} :
    ∀ (ts : List Nat) (rd : List (Nat × Nat × Nat)), AllFive ft logN B0 ts rd →
      ∀ t ∈ ts, ∃ tree, B0.trees[t]? = some tree ∧ tree.shape.logN ≤ logN
  | [], [], _, _, ht => nomatch ht
  | t :: ts, r :: rd, h, u, hu => by
    obtain ⟨⟨tree, a, b, -⟩, rest⟩ := h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨tree, a, b⟩
    · exact allFive_there ts rd rest u hu
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- AllFive: the list rd is the trees' numbers less ft, depths and widths, in one order. -/
theorem allFive_reads {ft logN : Nat} {B0 : TreeBook} :
    ∀ (ts : List Nat) (rd : List (Nat × Nat × Nat)), AllFive ft logN B0 ts rd →
      readsOfS (bookSh B0) ft ts = some rd
  | [], [], _ => rfl
  | t :: ts, r :: rd, h => by
    obtain ⟨⟨tree, a, -, c, d, e⟩, rest⟩ := h
    have h1 : readOfS (bookSh B0) ft t = some r := by
      unfold readOfS
      rw [tree_get, a]
      show some (tree.number - ft, tree.shape.logN,
        tree.shape.mainWidth + tree.shape.maskWidth) = some r
      rw [c, d, e]
    show (readOfS (bookSh B0) ft t).bind (fun x => (readsOfS (bookSh B0) ft ts).map (x :: ·)) = _
    rw [h1, allFive_reads ts rd rest]
    rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {z : ProofFile.InstPub}

/-- **THE TABLE's OWN GUARD AT A LINK's SWITCH ACCEPTS AT EVERY REACHED STATE.** -/
theorem linkGd_reached_whole (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) :
    linkGd (k2P Zp a nm .link n) (chainF s) = true := by
  obtain ⟨hpl, hcut, hsh, hy, hB, hLd, hcs⟩ := six_at_head h.toAtMg O
  obtain ⟨L, Q, -⟩ :=
    link_fields_reached h.scope h.reads O h.laid.value h.laid.planOk h23 hP hn hr a nm
  have hlen : 14 * (m + 1) + 2 ≤ (frontOf cF).length := by
    rw [front_len h.scope h.reads O]
    omega
  have RA := recAll_reached h.scope h.reads O (reach_raw hr) (by omega) hlen
  have e : treesOfS (bookSh s.book) (singleSh s.check.frame.rows) =
      treesOf (dummyIn (k2P Zp a nm .link n) s L Q) :=
    trees_sh (dummyIn (k2P Zp a nm .link n) s L Q)
  have h5 : AllFive 0 logW s.book (treesOf (dummyIn (k2P Zp a nm .link n) s L Q)) n.read :=
    link_five_reached h.scope h.reads O hpl hcut hsh hy hB hLd h23 hP hn hr L Q _ _ _ _
  refine linkGd_reached_leaf h O h23 hP hn hr a nm (fun c hc t ht => ?_) ?_
  · rw [e] at ht
    obtain ⟨tree, h1, h2⟩ := allFive_there _ _ h5 t ht
    have h0 : tree.lists = 0 :=
      link_unopened_all h.scope h.reads O hpl hcut hsh h23 hr L Q _ _ _ _ t ht tree h1
    refine ⟨tree, h1, by rw [h0]; simp, ?_⟩
    rw [depth_written (RA.codes.trans hcs) (RA.walk.shape.trans hsh) hc]
    exact h2
  · rw [e, pub_firstTree O.pub]
    exact allFive_reads _ _ h5

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.allFive_there
#print axioms Johnson.AtFull.Shape.allFive_reads
#print axioms Johnson.AtFull.Shape.linkGd_reached_whole
