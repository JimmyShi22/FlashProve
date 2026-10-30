-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Tree.lean: HASH TREES AS TOKEN PROGRAMS, for the second form: every leaf is salted
and is a marked evaluation, its digest is a value at once, the inner nodes are ordinary queries.
DEFINITIONS ALONE.

The programs are laid, bind by bind, on the compiled prover's builders (leavesO, treeO, treesO,
OnBytes/Prover/Defs.lean): the same queries in the same order. What differs: where the builder is
handed a leaf's salt, the program here draws the salt's free bits as a token just before the leaf's
evaluation. It follows the pattern of the first form's trees over encoded indices (leafE, commitE,
Compile/Batch/TokTree.lean), used here for the trees over prover messages too; there a padding leaf
is an unsalted ordinary query, here every leaf is salted, as in the second form's committer and
prover.

The form of a salt: a public start, then ℓ free bits. The token is the free bits alone. The start
may hang on further tokens us (for a compiled run: on the run's first salt), which the point then
holds: pre is a function of their values. For a table us is empty and pre is constant.

Main names (namespace OnBytes.TokenSide).
  TreeT   a tree as a token program keeps it: the leaves' bodies; for each leaf the token of its
          salt's free bits and the token of the empty tail of its answer; all levels of digests.
  TreeT.root, TreeT.toksAt, TreeT.toK   its root; the two tokens of a leaf; the tree as the compiled
          prover keeps it (TreeK), with the salts read off values of tokens.
  leafT, leavesT, nodeT, treeT, treesT   the programs.

Limits. Definitions alone: that these programs erase to the compiled prover's builders, and that
they keep the rules, is not shown here (the first: Johnson/TokenSide/TieTree.lean). TreeT.toK lays
the empty string as the free bits of a leaf whose token has no value in val: in a compiled run it is
meant to be read at opened leaves alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Split
import OnBytes.Prover.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A tree as a token program keeps it. -/
structure TreeT (lam : ℕ) (L : BatchProtocolWithLeafBody I X) where
  /-- the body of leaf j -/
  body : ℕ → Body L
  /-- for each leaf: the token of the free bits of its salt, the token of its answer's empty tail -/
  tok : List (Tok × Tok)
  /-- all levels of digests, leaves first -/
  lv : List (List (Dig lam))

def TreeT.root (T : TreeT lam L) : Dig lam := rootOf T.lv

/-- the tokens that are shown when leaf j is opened; none where the tree has no such leaf -/
def TreeT.toksAt (T : TreeT lam L) (j : ℕ) : List Tok :=
  match T.tok[j]? with
  | some a => [a.1, a.2]
  | none => []

/-- The tree as the compiled prover keeps it: the salt of leaf j is the start pre, then the value of
the leaf's token; the empty string at a number at which the tree has no leaf. -/
def TreeT.toK (val : Tok → Bits) (pre : Bits) (T : TreeT lam L) : TreeK lam L :=
  ⟨fun j => ⟨T.body j, match T.tok[j]? with
    | some a => pre ++ val a.1
    | none => []⟩, T.lv⟩

/-- One leaf with the body b: ℓ fresh bits; the evaluation at (b, start ++ these bits), charged to
them. It gives the digest, the token of the free bits, the token of the empty tail. -/
def leafT (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) (b : Body L) :
    StT lam K L (Dig lam × Tok × Tok) :=
  Step.fresh ℓ fun s =>
  Step.marked (S := typedOracleFamily lam K L) OracleName.leaf s us (fun v vs => (⟨b, pre vs ++ v⟩ : LeafIn L))
    (fun _ _ _ h => List.append_cancel_left (congrArg (fun z : LeafIn L => z.salt) h))
    fun d e => Step.pure ((d : Dig lam), s, e)

/-- The leaves in turn: their digests, their tokens. -/
def leavesT (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) :
    List (Body L) → StT lam K L (List (Dig lam) × List (Tok × Tok))
  | [] => .pure ([], [])
  | b :: bs => (leafT (K := K) ℓ us pre b).bind fun u =>
      (leavesT ℓ us pre bs).bind fun r => .pure (u.1 :: r.1, u.2 :: r.2)

/-- an inner node: an ordinary query on two digests -/
def nodeT (a b : Dig lam) : StT lam K L (Dig lam) :=
  Step.plain (S := typedOracleFamily lam K L) OracleName.node ((List.ofFn a, List.ofFn b) : Bits × Bits) Step.pure

/-- build the tree of depth d over the leaves with the bodies body 0, .., body (2 ^ d - 1) -/
def treeT (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) (d : ℕ) (body : ℕ → Body L) :
    StT lam K L (TreeT lam L) :=
  (leavesT (K := K) ℓ us pre ((List.range (2 ^ d)).map body)).bind fun l =>
    (levelsM (nodeT (K := K) (L := L)) d l.1).bind fun lv => .pure ⟨body, l.2, lv⟩

/-- the trees of one component of one round, from tree number k on -/
def treesT {r : Round} (ℓ : ℕ) (us : List Tok) (pre : List Bits → Bits) (pad : Body L)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ℕ → List ℕ → StT lam K L (List (TreeT lam L))
  | _, [] => .pure []
  | k, d :: ds =>
    (treeT (K := K) ℓ us pre d fun j => match posAt k j with
        | some p => emb p (r.rd o p)
        | none => pad).bind fun T =>
      (treesT ℓ us pre pad posAt emb o (k + 1) ds).bind fun Ts => .pure (T :: Ts)

end OnBytes.TokenSide
