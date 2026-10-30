-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ByWalks.lean: what a part of the join owes so that it reads one raw string with
another part: its reading is made of the walks of one look, and the two looks agree.

OnBytes/Slice/PartO.lean joins three checkers over one random oracle and asks of two parts that they
read one raw string under every root, off every log in which no two strings have one answer
(`SameRaw`). A part there is a record over the one oracle alone (`PartO`): its reading `raw` is any
function of log and root. OnBytes/Slice/Look.lean has ways of reading a bit string as a vertex or as
a leaf (`Look`), the walk down a log from a digest, and that two looks that agree find the same
(`walk_same`). OnBytes/Slice/WalksO.lean says in Lean what it is for a part's reading to be made of
a look's walks, and goes from there to `SameRaw`, with no typed oracle in the statement: so a part
may come from another compiler than the library's. This file shows it of the library's parts.

Main definition (it stands in OnBytes/Slice/WalksO.lean, with `sameRaw_of_walks`).
 `PartO.ByWalks s k pos sym mk`   the part's reading is made of the walks of the look k: at each
                     place j the walk to the position `pos j`, then `sym j` of the leaf that is
                     found; then `mk` of what stands at all places.
Main theorems (the first stands in OnBytes/Slice/WalksO.lean).
 `sameRaw_of_walks`  two parts whose readings are made of walks, with ONE `pos` and ONE `mk`, read
                     one raw string, if the two looks read the same strings as the same vertices
                     and, string by string and place by place, `sym₁` of the first's leaf is `sym₂`
                     of the second's.
 `Part.toO_byWalks`  a part of the library's compiler (`Part`, OnBytes/Slice/JoinThree.lean) whose
                     reading goes by leaves (OnBytes/Slice/SameAt.lean), and whose implementation
                     has one block for a leaf's and a vertex's answer, is such a part, at the look
                     `lookOf s.m`.

What is owed beside "one look, and one law" (the head of OnBytes/Slice/Look.lean). Held against
`sameRaw_of_walks`:
 1. BY THE PAIR: the two looks agree. Both must read THE SAME SET of strings as vertices, also
    strings that belong to neither's stored trees. At the library's own reading, which keeps a
    stored symbol whatever the salt, the other compiler must read the library's escape strings (the
    byte 2 and then the library's spelling of a leaf query) as the same leaves.
 2. ONE tree shape and ONE map from places to positions.
 3. ONE way of making a raw string of what is found: one length, and one filling where nothing is
    found.
 4. OF THE FIRST PART: stability (`PartO.Stable`, OnBytes/Slice/PartO.lean), or `SameRaw` with a
    part that has it (`PartO.Stable.of_sameRaw`).
 5. FOR OnBytes/Slice/JoinAtSet.lean: its look reads none of the strings at which a verifier asks
    for digests of public bytes, as a vertex or as a leaf. That the looks agree does not give this
    for leaves. (`PartO.ByWalks.raw_offSet`, OnBytes/Slice/WalksO.lean, then carries it to the
    part's raw string.)
And ONE type of symbols and ONE numbering of places: beside the entry's part
a part must give its raw string in `Run.PQ.SgX`, a column a
place, whatever its own interface's symbols are, and carry its language over inside its own proof of
`PartO.OK`.

What a look cannot express.
 (a) `node` and `leaf` do not see the position. A reading that takes a vertex only at its own level
     or number, or under its own tree's number, is no walk of a look. At the leaf the place can be
     tested, through `sym j`; at a vertex it cannot.
 (b) A vertex is on exactly two digests: a top vertex on a list of roots, or a tree of another
     arity, is none.
 (c) `PartO.raw` takes one digest: a string that lies under several roots is several raw strings.
 (d) One kind of vertex and one kind of leaf.

What is not claimed. That any part but those of the library's compiler is made of walks (for the
compiler under OnBytes/TypedOracleCompiler/: OnBytes/TypedOracleCompiler/Slice/ByWalks.lean, of a form; a part of that form:
OnBytes/TypedOracleCompiler/Slice/PartEntryFull.lean; that it reads the raw string of the entry's part here:
OnBytes/TypedOracleCompiler/Slice/TieRaw.lean). That any two looks agree (for two encodings `Tie.theImplX`:
OnBytes/Slice/SameStoredAt.lean, in the form `SameRead`). No probability: the log is fixed in
`SameRaw`, and that no two of its strings have one answer stands there as a condition. Nothing on
any protocol, language, checker or hash function.

-/
import OnBytes.Slice.WalksO
import OnBytes.Slice.JoinThree
import OnBytes.Slice.SameAt

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch

variable {lam : ℕ} {γ Sg : Type}

/-- **A part of the library's compiler whose reading goes by leaves is made of walks**, at the look
through its implementation, in the perfect tree of its wiring's depth. Asked: one block for a leaf's
and a vertex's answer, taken as it is (`OneBlock`); the reading goes by leaves (`Reading.ByLeaves`).
The symbols are carried to the shared type by the part's match u, and back inside `mk`. -/
theorem Part.toO_byWalks (s : Part lam γ Sg) (h : OneBlock s.m)
    {keep : ℕ → LeafIn s.L → Option s.L.Symbol} {g : (ℕ → Option s.L.Symbol) → Fin s.L.wordLength → s.L.Symbol}
    (B : s.J.R.ByLeaves keep g) :
    s.toO.ByWalks (lookOf s.m) (posOf s.W.depth) (fun j q => (keep j q).map s.u)
      (fun φ => rawOf s.u (g fun j => (φ j).map s.u.symm)) where
  raw_eq := fun σ cm => by
    show rawOf s.u (s.J.R.of fun j => Batch.extLeaf (singleTr s.m σ) s.W.depth cm j) = _
    rw [B.of_eq]
    refine congrArg (fun f => rawOf s.u (g f)) (funext fun j => ?_)
    rw [extLeaf_eq_walk s.m h]
    show ((lookOf s.m).walk σ (posOf s.W.depth j) cm).bind (keep j) =
      (((lookOf s.m).walk σ (posOf s.W.depth j) cm).bind fun q => (keep j q).map s.u).map s.u.symm
    cases (lookOf s.m).walk σ (posOf s.W.depth j) cm with
    | none => rfl
    | some q =>
      show keep j q = ((keep j q).map s.u).map s.u.symm
      rw [Option.map_map, Equiv.symm_comp_self, Option.map_id]
      rfl

end OnBytes.Slice
