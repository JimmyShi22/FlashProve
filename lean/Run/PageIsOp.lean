-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsOp.lean: on the Merkle openings in the compiled verifier's input: in one round with a
tree, under the hypotheses of `comp_tree`, the verifier's checks are those that the opening read
from the file calls for. Tools for Run/PageIs.lean.

1. What the file contains. Definitions and lemmas with their proofs; no separate statement file.

2. What is checked when the file compiles. The proofs; there are no tests (#guard) here.

3. Theorems.
   `opL_top`, `opL_tail`: the function "opens" of the argument string that `toBPrf` makes
     (`opensAt`, Run/ParseLaws.lean, at the typing of Run/PlanQS.lean), at a position after the
     trivial round, is `opL` at the table of all openings; `opL` at a position after the first round
     is `opL` of the remaining rounds. Both hold by definition, so an induction on the rounds goes
     through with the table fixed.
   `comp_tree`: take a round with a tree of shape sh. Suppose that a table `tbl` finds (sh.W, Ob)
     under sh.tree, that Ob.a = sh.a, that Ob passes the test on an opening's record (`OpenB.ok`),
     and that a position is read exactly if its number is listed in Ob. Then `compP`
     (Run/ThinDefs.lean) over all places of the tree = some (checksOf (syOf ..) run rt Ob), with
     `checksOf` from Run/Toy1TieTree.lean.

4. What is not claimed.
   Nothing on hashes, roots or soundness: `rt` in `comp_tree` is any digest, under no hypothesis;
   both sides copy it unchanged into every check.
   That a table with these properties exists is the matter of Run/PageIsTab.lean's statements. That
   the record passes `OpenB.ok` is no part of that file's statements: it is the field `okb` of
   `OpenFacts` (Run/PageIs.lean).
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

A note on the interfaces. The run functions stand at the interface `LbS`, in which the protocol is
the field `onlineBatch` (Run/PlanQS.lean; tag "onl"; `Compile.Batch.vBS`; the ties vbs_*, vbsP_*, vbsPF_*).
The wirings of Run/M1RunTie*.lean, Run/M2Tie.lean and Run/PlanQSToy.lean and their laws are stated
at `LtS`, in which the protocol is the field `offline` (tag "test"; `Compile.Batch.vTS`); their field T
is the field B of the run functions' wiring (`Wb`, Run/PlanQS.lean).

Sources. No text from outside enters.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIsTab
import Run.Toy1TieChecks
import Run.ThinTieProofs

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-- the function "opens" of the parser's argument string, on the positions of a list of rounds, from
a table -/
def opL (C : CK) (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray)
    (ds : List RD) (p : OPos (uL C ds)) :
    Option (Opening 256 (OSym (uL C ds) p)) :=
  match tbl.lookup (placeSL C ds p).1 with
  | none => none
  | some x => x.2.at (symSL C ds p) run (placeSL C ds p).2

theorem opL_top (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (run : ByteArray)
    (o : ChainOut) (q : OPos (uL C (rds S))) :
    opensAt (TYS S C dec).up run o (.inr q) = opL C (opensB o) run (rds S) q := rfl

theorem opL_tail (C : CK) (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray) (d : RD)
    (ds : List RD) (q : OPos (uL C ds)) :
    opL C tbl run (d :: ds) (.inr q) = opL C tbl run ds q := rfl

section
variable {I X : Type} {L : BatchProtocol I X} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- a column as a function of the word's number -/
def colFn (W : ℕ) (col : List UInt64) : Fin W → UInt64 := fun i => col.getD i.val 0

theorem ofFn_colFn (W : ℕ) (col : List UInt64) (h : col.length = W) :
    List.ofFn (colFn W col) = col := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [colFn, List.getElem?_eq_getElem h2]

/-- how a position's number and a column become a symbol of the protocol that the interface holds:
through the first round of a list -/
def syOf (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (items : List _root_.Fmt.Item)
    (sh : _root_.Fmt.Shape) (opens : List ℕ) (ds : List RD)
    (inj : SymAny (uL C (⟨e, k, items, some sh, opens⟩ :: ds)) →
      SymAny (Compile.Batch.shapeOf L .onl))
    (x : ℕ) (col : List UInt64) :
    SymAny (Compile.Batch.shapeOf L .onl) :=
  if h : x < 2 ^ sh.a then inj ⟨.inl (⟨x, h⟩ : Fin (2 ^ sh.a)), colFn sh.W col⟩
  else inj ⟨.inl (⟨0, Nat.pos_of_ne_zero (by positivity)⟩ : Fin (2 ^ sh.a)), colFn sh.W col⟩

/-- One round with a tree, under `hl`, `ha`, `hok` and `hread`: the verifier's checks are those that
the parser's opening calls for. -/
theorem comp_tree (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (items : List _root_.Fmt.Item)
    (sh : _root_.Fmt.Shape) (opens : List ℕ) (ds : List RD) (tbl : List (ℕ × ℕ × OpenB))
    (run : ByteArray) (sb : ℕ) (Ob : OpenB) (hl : tbl.lookup sh.tree = some (sh.W, Ob))
    (ha : Ob.a = sh.a) (hok : Ob.ok sb sh.W = true)
    (inj : SymAny (uL C (⟨e, k, items, some sh, opens⟩ :: ds)) →
      SymAny (Compile.Batch.shapeOf L .onl))
    (isRead : OPos (uL C (⟨e, k, items, some sh, opens⟩ :: ds)) → Bool)
    (hread : ∀ x : Fin (2 ^ sh.a), isRead (.inl x) = decide (x.val ∈ Ob.idx)) (rt : Dig 256) :
    compP (fun _ => L) (roundS C ⟨e, k, items, some sh, opens⟩)
        (wireS C K chal ⟨e, k, items, some sh, opens⟩).posAtJ
        (wireS C K chal ⟨e, k, items, some sh, opens⟩).depthJ
        (fun p a => some (.inr ⟨.onl, inj ⟨.inl p, a⟩⟩)) rt (fun p => isRead (.inl p))
        (fun p => opL C tbl run (⟨e, k, items, some sh, opens⟩ :: ds) (.inl p))
        (List.range (2 ^ (wireS C K chal ⟨e, k, items, some sh, opens⟩).depthJ)) =
      some (TieTree.checksOf (syOf C e k items sh opens ds inj) run rt Ob) := by
  rw [compP_eq]
  have := TieTree.checksComp_at (L := L) (r := (roundS C ⟨e, k, items, some sh, opens⟩).up)
    (wireS C K chal ⟨e, k, items, some sh, opens⟩).posAtJ
    (fun p a => some (.inr ⟨.onl, inj ⟨.inl p, a⟩⟩))
    rt (fun p => isRead (.inl p)) (fun p : Fin (2 ^ sh.a) => p.val)
    (fun p l => symSL C (⟨e, k, items, some sh, opens⟩ :: ds) (.inl p) l)
    (syOf C e k items sh opens ds inj) run Ob sb sh.W hok
    (by
      intro j hj
      rw [ha] at hj
      exact ⟨⟨j, hj⟩, dif_pos hj, rfl⟩)
    hread
    (by
      intro p col hc
      have hw : col.length = sh.W := (TieTree.ok_list Ob sb sh.W hok).2.2 col hc
      refine ⟨fun i => col[i.val]'(by rw [hw]; exact i.isLt), dif_pos hw, ?_⟩
      have e2 : (fun i : Fin sh.W => col[i.val]'(by rw [hw]; exact i.isLt)) = colFn sh.W col :=
        funext fun i => by
          simp [colFn, List.getElem?_eq_getElem (show i.val < col.length by rw [hw]; exact i.isLt)]
      have e3 : syOf C e k items sh opens ds inj p.val col = inj ⟨.inl p, colFn sh.W col⟩ :=
        dif_pos p.isLt
      dsimp only
      rw [e3]
      exact congrArg
        (fun c : Fin sh.W → UInt64 => (some (Sum.inr ⟨Tag.onl, inj ⟨Sum.inl p, c⟩⟩) : Body L)) e2)
  rw [ha] at this
  rw [← this]
  congr 1
  funext p
  unfold opL
  show (match tbl.lookup sh.tree with | none => none | some x => x.2.at _ run p.val) = _
  rw [hl]
  rfl

end

end Run.PQ
