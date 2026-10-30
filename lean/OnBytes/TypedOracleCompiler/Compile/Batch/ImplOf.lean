-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ImplOf.lean: a second form of Compile/Batch/ImplOf.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

Comments apart, every declaration of this file has the text of Compile/Batch/ImplOf.lean; what it
means changes with the definitions that it names.

Where the head below says that the encodings c and cG are built (`codeReal`, `codeGhost`,
Compile/Batch/Ser.lean): these are encodings of the library's points. Here `RealPts` is over this
folder's `LeafIn`, `FbIn`, `JoiningRoundQuery` (a body of the type `Bd`, lists of roots), and this folder builds
no encoding for its own points. Where it says that the slot value becomes the slot's leaf in the
request tree: here the leaf's input is the slot value and `OneProtocolProof.rsalt` behind it.

The rest of this head is the head of Compile/Batch/ImplOf.lean, to be read with these changes; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/ImplOf.lean: an explicit query encoding of the compiled scheme's typed oracles over
one oracle on bit strings (`Rom.OracleCoding`) (words of this library: lean/GLOSSARY.md).

Hash blocks of lam bits in an answer: leaf, node, rleaf, rnode, g, other: 1; fb, and the ghost names
fbw: K + 1; ann: 0. (`blk`; K and the oracles: Notation, below.)
The encoding: an explicit injective encoding c of the points of the oracles leaf, node, rleaf,
rnode, fb, g (`RealPts`; data: `Rom.StrCode`), and `Rom.StrCode.hotel`, which makes room for the
points of the auxiliary oracle `other`, so that every string is the encoding of exactly one point.
The inverse is part of the data, not obtained by a choice principle, and no countability is assumed.
c, like cG below, is an argument of `implOf` (built: `codeReal`, `codeGhost`,
Compile/Batch/Ser.lean).
The ghost names `fbw t k` (Compile/Batch/Oracles.lean), which no algorithm of the scheme queries,
need a place in that bijection too. They get it on the side of `other`, by a second use of `hotel`:
a second encoding cG, of the ghost points (`GhostPts`), makes room for them among the strings of
`other`, and then c makes room for the points of `RealPts` as before. So the encodings of the points
of `RealPts` do not depend on cG: such a point is encoded as true :: c.put .., whatever cG is
(`code_real`, by definition). A string s of `other` has the encoding `c.hotel (.inr s)`, in which cG
does not occur, unless it is of the form false^k ++ true :: (the encoding of a ghost point)
(`code_other_of_free`).

Notation: `K`: a natural number; in `typedOracleFamily lam K L` (Compile/Batch/Oracles.lean) an answer of `fb t`
is K hash blocks, from which the challenge is made, and a chaining value; of the oracles (`OracleName`, the
head of the same file): `g t`: in the joining round (the first shared round after the local ones),
the slot value: the hash of a slot's chain that becomes its leaf in the request tree; `ann`: a
trivial answer: a query to it announces a digest, for the analysis; `other`: the auxiliary oracle on
bit strings, which only the schemes with a seed query, to derive coins.

-/
import Compile.Batch.ImplOf
import OnBytes.TypedOracleCompiler.Compile.Batch.Oracles
import Rom.Family
import Rom.Hotel
import Mathlib.Logic.Equiv.Fin.Basic

namespace TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol

variable {I X : Type}

/-- the number of hash blocks of lam bits in an answer -/
def blk (K : ℕ) : OracleName → ℕ
  | .leaf => 1
  | .node => 1
  | .rleaf => 1
  | .rnode => 1
  | .fb _ => K + 1
  | .g _ => 1
  | .ann => 0
  | .other => 1
  | .fbw _ _ => K + 1

/-- an answer as the tuple of its hash blocks; in a Fiat-Shamir answer the chaining value is the
last hash block -/
def rngEquiv (lam K : ℕ) : (o : OracleName) → rngOf lam K o ≃ (Fin (blk K o) → Fin lam → Bool)
  | .leaf => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .node => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .rleaf => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .rnode => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .fb _ => (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ : Fin (K + 1) => Dig lam)
  | .g _ => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .ann => ⟨fun _ i => i.elim0, fun _ => (), fun _ => rfl, fun _ => funext fun i => i.elim0⟩
  | .other => (Equiv.funUnique (Fin 1) (Dig lam)).symm
  | .fbw _ _ => (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ : Fin (K + 1) => Dig lam)

/-- all points: an oracle, a query, the number of a hash block of the answer -/
abbrev Pts (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : Type := Σ o : OracleName, domOf lam L o × Fin (blk K o)

/-- The points of leaf, node, rleaf, rnode, fb, g: a leaf query; a node query; a leaf query and a
node query of a request tree; a Fiat-Shamir query with the number of a hash block of its answer; a
query to g. (`ann` has no hash block; `other` is treated apart.) -/
abbrev RealPts (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : Type :=
  LeafIn L ⊕ (Bits × Bits) ⊕ Bits ⊕ (Bits × Bits) ⊕ (Σ t : Tag, FbIn lam L t × Fin (K + 1))
    ⊕ (Σ t : Tag, JoiningRoundQuery lam L t)

/-- The points of the ghost names: protocol, number of the name, Fiat-Shamir query, number of a hash
block. -/
abbrev GhostPts (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : Type := Σ t : Tag, ℕ × FbIn lam L t × Fin (K + 1)

def ptsTo (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : Pts lam K L → RealPts lam K L ⊕ (GhostPts lam K L ⊕ List Bool)
  | ⟨.leaf, q, _⟩ => .inl (.inl q)
  | ⟨.node, q, _⟩ => .inl (.inr (.inl q))
  | ⟨.rleaf, q, _⟩ => .inl (.inr (.inr (.inl q)))
  | ⟨.rnode, q, _⟩ => .inl (.inr (.inr (.inr (.inl q))))
  | ⟨.fb t, q, j⟩ => .inl (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩)))))
  | ⟨.g t, q, _⟩ => .inl (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩)))))
  | ⟨.ann, _, j⟩ => j.elim0
  | ⟨.other, s, _⟩ => .inr (.inr s)
  | ⟨.fbw t k, q, j⟩ => .inr (.inl ⟨t, k, q, j⟩)

def ptsOf (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : RealPts lam K L ⊕ (GhostPts lam K L ⊕ List Bool) → Pts lam K L
  | .inl (.inl q) => ⟨.leaf, q, (0 : Fin 1)⟩
  | .inl (.inr (.inl q)) => ⟨.node, q, (0 : Fin 1)⟩
  | .inl (.inr (.inr (.inl q))) => ⟨.rleaf, q, (0 : Fin 1)⟩
  | .inl (.inr (.inr (.inr (.inl q)))) => ⟨.rnode, q, (0 : Fin 1)⟩
  | .inl (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))) => ⟨.fb t, q, j⟩
  | .inl (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))) => ⟨.g t, q, (0 : Fin 1)⟩
  | .inr (.inr s) => ⟨.other, s, (0 : Fin 1)⟩
  | .inr (.inl ⟨t, k, q, j⟩) => ⟨.fbw t k, q, j⟩

def ptsEquiv (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) :
    Pts lam K L ≃ RealPts lam K L ⊕ (GhostPts lam K L ⊕ List Bool) where
  toFun := ptsTo lam K L
  invFun := ptsOf lam K L
  left_inv := fun x => by
    rcases x with ⟨o, q, j⟩
    cases o with
    | leaf => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
    | node => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
    | rleaf => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
    | rnode => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
    | fb t => rfl
    | g t => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
    | ann => exact j.elim0
    | other => have : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ j 0; subst this; rfl
    | fbw t k => rfl
  right_inv := fun y => by
    rcases y with ((q | (q | (q | (q | (⟨t, q, j⟩ | ⟨t, q⟩))))) | (⟨t, k, q, j⟩ | s)) <;> rfl

/-- how a point is encoded as a string -/
def codeEquiv (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) : Pts lam K L ≃ List Bool :=
  (ptsEquiv lam K L).trans ((Equiv.sumCongr (Equiv.refl _) cG.hotel).trans c.hotel)

/-- The query encoding over one oracle. -/
def implOf (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) : OracleCoding (typedOracleFamily lam K L) lam where
  blocks := blk K
  rng := rngEquiv lam K
  code := fun o q j => codeEquiv lam K L c cG ⟨o, q, j⟩
  inv := (codeEquiv lam K L c cG).symm
  inv_code := fun x => (codeEquiv lam K L c cG).symm_apply_apply x
  code_inv := fun s => (codeEquiv lam K L c cG).apply_symm_apply s

/-- The encodings of the points of `RealPts` do not depend on the ghost names: such a point is
encoded as true :: c.put .., whatever the encoding cG of the ghost points (`GhostPts`) is. -/
theorem code_real (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (x : RealPts lam K L) :
    codeEquiv lam K L c cG (ptsOf lam K L (.inl x)) = true :: c.put x := by
  rcases x with (q | (q | (q | (q | (⟨t, q, j⟩ | ⟨t, q⟩))))) <;> rfl

/-- the same, oracle by oracle, for `implOf` itself -/
theorem code_leaf (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (q : LeafIn L) (j : Fin 1) :
    (implOf lam K L c cG).code .leaf q j = true :: c.put (.inl q) := rfl
@[inherit_doc code_leaf]
theorem code_node (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (q : Bits × Bits) (j : Fin 1) :
    (implOf lam K L c cG).code .node q j = true :: c.put (.inr (.inl q)) := rfl
@[inherit_doc code_leaf]
theorem code_fb (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (t : Tag) (q : FbIn lam L t) (j : Fin (K + 1)) :
    (implOf lam K L c cG).code (.fb t) q j =
      true :: c.put (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))) := rfl
@[inherit_doc code_leaf]
theorem code_g (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (t : Tag) (q : JoiningRoundQuery lam L t) (j : Fin 1) :
    (implOf lam K L c cG).code (.g t) q j =
      true :: c.put (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))) := rfl

/-- If `cG.free s` (s is not of the form false^k ++ true :: (the encoding of a ghost point)), the
string s of `other` has the encoding `c.hotel (.inr s)`, in which cG does not occur. -/
theorem code_other_of_free (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (s : List Bool) (j : Fin 1) (h : cG.free s = true) :
    (implOf lam K L c cG).code .other s j = c.hotel (.inr s) := by
  show c.hotel (.inr (cG.enc (.inr s))) = _
  rw [show cG.enc (.inr s) = s from if_pos h]

end TypedOracleCompiler.Compile.Batch
