-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/TokTree.lean: Merkle trees on the prover's side of the compiled scheme, as token
programs (`Step`, Rom/Defer.lean). (Words of this library: lean/GLOSSARY.md.)

* Token trees (`TTree`): the trees over prover messages of Test, Link and Batch, and request trees.
  Every leaf of a tree over a message is salted, padding leaves too. The digest of a leaf or of an
  inner node is a token; an inner node is a marked query that is charged to its left child and holds
  its right child. So such a tree makes no ordinary query. Compared with an ordinary query to the
  node oracle, this costs one more hash term in the bound on index privacy and saves the argument
  that a query which no one has seen leaves no trace.
* Trees over encoded indices (`Compile.TreeH`, Compile/Bcs.lean): the digest of a salted leaf
  is shown at once, padding leaves and inner nodes are ordinary queries.

Notation: `St lam K L α`: `Step (spec lam K L) (split lam K L) α`: a token program (`Step`,
Rom/Defer.lean); `Step.marked o t us pt inj k`: a marked evaluation of the oracle o: charged to one
token t, in which its point pt is injective (inj); it may hold further tokens us; k takes an element
of `sp.Vis o` and a `Tok` (the rules in the head of Rom/Defer.lean); the endings T and E, the
leading r: the definitions under the headings "Token trees", "Trees over encoded indices", "Request
trees"; `nodeT a b`, `rnodeT a b`: a marked query to `OracleName.node`, to `OracleName.rnode`, charged to a, with
the further token b; `rleafT c`: a marked query to `OracleName.rleaf`, charged to c;
`commitE sMT depth leaf`: `leavesE` on the 2 ^ depth leaves, then `levelsM nodeE depth`; `sMT`: a
natural number: the length of the salt of a leaf (Compile/Batch/Verifier.lean).
-/
import Compile.Batch.Split
import Compile.Batch.Verifier

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

abbrev St (lam K : ℕ) (L : BatchProtocol I X) (α : Type) : Type := Step (spec lam K L) (split lam K L) α

/-- a string as a digest (the first lam bits; false beyond its end) -/
def digD (lam : ℕ) (v : Bits) : Dig lam := fun i => v.getD i.val false

/-! ## Token trees -/

/-- all levels of tokens of digests, leaves first; the token of the salt of each leaf (none in a
request tree) -/
structure TTree where
  levels : List (List Tok)
  salts : List Tok

def TTree.root (t : TTree) : Tok := rootOf t.levels

/-- the entries on the way from leaf j to the root, both included -/
def ancOf {D : Type} [Inhabited D] : List (List D) → ℕ → List D
  | [], _ => []
  | l :: ls, j => l.getD j default :: ancOf ls (j / 2)

/-- a salted leaf with the body b: its salt and its digest -/
def leafT (sMT : ℕ) (b : Body L) : St lam K L (Tok × Tok) :=
  Step.fresh sMT fun s =>
  Step.marked (S := spec lam K L) OracleName.leaf s [] (fun v _ => (⟨b, v⟩ : LeafIn L))
    (fun _ _ _ h => by cases h; rfl) fun _ d => Step.pure (s, d)

def nodeT (a b : Tok) : St lam K L Tok :=
  Step.marked (S := spec lam K L) OracleName.node a [b] (fun v vs => ((v, vs.headD []) : Bits × Bits))
    (fun _ _ _ h => (Prod.mk.inj h).1) fun _ d => Step.pure d

def leavesT (sMT : ℕ) : List (Body L) → St lam K L (List Tok × List Tok)
  | [] => pure ([], [])
  | b :: t => do
      let x ← leafT sMT b
      let r ← leavesT sMT t
      pure (x.2 :: r.1, x.1 :: r.2)

/-- commit to 2^depth leaves -/
def commitT (sMT depth : ℕ) (leaf : ℕ → Body L) : St lam K L TTree := do
  let x ← leavesT sMT ((List.range (2 ^ depth)).map leaf)
  let lv ← levelsM nodeT depth x.1
  pure ⟨lv, x.2⟩

/-- open leaf j: show its salt, the digests beside its path and those on it; this releases the
leaf and the nodes on the path -/
def openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) : St lam K L (Opening lam σ) :=
  Step.reveal (t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j)) fun vs =>
    Step.pure ⟨a, vs.headD [], (vs.tail.take (pathOf t.levels j).length).map (digD lam)⟩

/-- show one digest -/
def showT (t : Tok) : St lam K L (Dig lam) :=
  Step.reveal [t] fun vs => Step.pure (digD lam (vs.headD []))

/-! ## Request trees -/

def rleafT (c : Tok) : St lam K L Tok :=
  Step.marked (S := spec lam K L) OracleName.rleaf c [] (fun v _ => (v : Bits))
    (fun _ _ _ h => h) fun _ d => Step.pure d

def rnodeT (a b : Tok) : St lam K L Tok :=
  Step.marked (S := spec lam K L) OracleName.rnode a [b] (fun v vs => ((v, vs.headD []) : Bits × Bits))
    (fun _ _ _ h => (Prod.mk.inj h).1) fun _ d => Step.pure d

def rleavesT : List Tok → St lam K L (List Tok)
  | [] => pure []
  | c :: t => do
      let d ← rleafT c
      let r ← rleavesT t
      pure (d :: r)

/-- the request tree over the slot values cs -/
def reqT (depthReq : ℕ) (cs : List Tok) : St lam K L TTree := do
  let ls ← rleavesT cs
  let lv ← levelsM rnodeT depthReq ls
  pure ⟨lv, []⟩

/-! ## Trees over encoded indices -/

/-- one leaf: salted, with its digest shown at once; or padding, an ordinary query -/
def leafE (sMT : ℕ) (b : Body L) (blind : Bool) : St lam K L (Dig lam × Option (Tok × Tok)) :=
  if blind then
    (leafT sMT b).bind fun x => (showT x.2).bind fun d => Step.pure (d, some x)
  else Step.plain (S := spec lam K L) OracleName.leaf (⟨b, []⟩ : LeafIn L) fun d => Step.pure (d, none)

def nodeE (a b : Dig lam) : St lam K L (Dig lam) :=
  Step.plain (S := spec lam K L) OracleName.node ((List.ofFn a, List.ofFn b) : Bits × Bits) Step.pure

def leavesE (sMT : ℕ) :
    List (Body L × Bool) → St lam K L (List (Dig lam) × List (Option (Tok × Tok)))
  | [] => pure ([], [])
  | (b, bl) :: t => do
      let x ← leafE sMT b bl
      let r ← leavesE sMT t
      pure (x.1 :: r.1, x.2 :: r.2)

def commitE (sMT depth : ℕ) (leaf : ℕ → Body L × Bool) : St lam K L (TreeH lam) := do
  let x ← leavesE sMT ((List.range (2 ^ depth)).map leaf)
  let lv ← levelsM nodeE depth x.1
  pure ⟨lv, x.2⟩

/-- open leaf j of a tree over an encoded index: show its salt; this releases the leaf -/
def openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) : St lam K L (Opening lam σ) :=
  match t.salts.getD j none with
  | some (s, d) => Step.reveal [s, d] fun vs => Step.pure ⟨a, vs.headD [], pathOf t.levels j⟩
  | none => Step.pure ⟨a, [], pathOf t.levels j⟩

end Compile.Batch
