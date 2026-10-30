-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Strings.lean: an instance of the sibling's body of a leaf: the body is a string of bits,
what stands between start and salt in the format's string of a leaf.

The sibling (OnBytes/TypedOracleCompiler/) leaves the type of a leaf's body open, and asks of the ways of writing
only that what is written is read back. OnBytes/TypedOracleCompiler/Tagged.lean has the library's own body as an
instance: a symbol with the protocol's tag and its position. Here the body is a list of bits, at the
library's generic protocol for ANY list of rounds' data ds (the interface `Run.PQ.LtS C ds dec`,
whose Test is that protocol).

A symbol at a position is written as its leaf's own string: what its own tree's code writes: the
label with the index, the column, the fill (`embT`, from `OnBytes.Slice.ownStr`). A body is read at
a position by the code of that position's own tree (`prjT`, from `OnBytes.Slice.rdLeaf`). What is
written is read back if no tree is deeper than 63 (`prjT_embT`), and a GIVEN lawful wire of the
library at that interface then gives a lawful wire of the sibling with these bodies (`ofT`,
`ofT_okg`). The body is the bits of the format's label, with the position's OWN tree's numbers, and
of column and fill (`embT_fit`).

The code of leaf queries over such bodies is THE IDENTITY on the bodies that pass a test, with start
and salt around it (`pBody`, `pLeafS`, over the library's `pSalted`). One test is given: the body
begins with the 16 bits of the leaves' number (`ok164`); a symbol's body passes it under the
library's test `tagsOK` (`embT_ok164`). A leaf query on a symbol, with a typed salt made of 32 bytes
and a file's salt of the length `salt`, is written, and its string is the bits of `Fmt.oStr` at the
number 164 with the numbers of the position's own tree (`leaf_query`).

No condition is put on the trees' numbers. Two positions at one place of two trees with the same
number, width and depth have ONE body for one column (by `embT_fit`, whose right side names the tree
by these three alone, with the place and the column; no statement says it; tested by program at one
place in a test that is not in this library): nothing here or on the sibling's road forbids it or
needs
to.

Main definitions: `strung`, `embT`, `prjT`, `ofT`, `pBody`, `ok164`, `pLeafS`.
Main theorems: `prjT_embT`, `embT_fit`, `ofT_okg`, `embT_ok164`, `leaf_query`.

Not claimed. No lawful wire is given: `ofT_okg` is from one of the library's. The sibling's top
theorem is not applied: at this interface (no external string, no index) its conclusion is true of
every wire and would test nothing. The stored symbols' way of writing is trivial here, and a stored
leaf's body is not made (OnBytes/TypedOracleCompiler/StringsStoredAt.lean makes one); it is not the same work:
`embE` has no position, and its law is asked of all symbols, so the fall-back of `embT` (the empty
string, which is also `embE`'s one body here) must not be copied there. Link and Batch have no
round. No round here has two trees. That the code's strings are apart from a vertex's, a chain
call's and a stored leaf's is not shown. No page and no family over one oracle is built. The
LIBRARY's builders stand over the library's own queries, and `pBody` can be no leaf code of the
library's page, by type; the SIBLING has a page whose leaf code is a code of bodies:
OnBytes/TypedOracleCompiler/StringsPage.lean ties `pBody ok164` and `pLeafS` to it. `Fmt.oStr`
is total: that the numbers lie in the domain of the format's hash is not shown, and at a tree with
the mark "stored" the string is still that of the number 164. Nothing on padding: no leaf without a
position is written or read here. That the 32 bytes are the run's value of the chain that sent the
tree is a parser's matter. That the chains of one file can be laid as one list of rounds' data is
not shown. That any string is accepted is not shown.

In this file `Iop.BatchProtocolWithLeafBody`, `Iop.QueryLayout`, `Compile.Batch.LeafIn` are the SIBLING's (TypedOracleCompiler.…); the
library's are written with `_root_`.

THE FILES Strings* OF THIS DIRECTORY, IN THE ORDER TO READ THEM. Each imports only earlier ones.
 1. Strings: the idea, at the LIBRARY's protocol (one tree a round): `strung`, `embT`, `prjT`,
    `pBody`, `ok164`, `pLeafS`. (Its tests by program are not in this library.)
 2. StringsList: the same over the SIBLING's protocol (a list of trees a round). Then
    Slice/Plain3Strings: `embTail` (`StringsList.embT` behind the round in front) and
    `Stretches.embS` (three stretches).
 3. StringsPage: `pBody` and `pLeafS` against the sibling's page.
 4. StringsWhole: `okWhole`, a step on the way.
 5. StringsRead: `rd`, `okRd`, `rdOk`; `pageFit_leaf`.
 6. StringsBounds: the same from conditions on the trees and the salt alone. (Its tests by program
    are not in this library.)
 7. StringsMeet: these conditions from the sibling's `ok`; `pi_after_strings`.
 8. StringsBoth: `rd2`, `ok2`, `call2`: both leaves' numbers.
 9. StringsStored: the pattern of a stored symbol's body.
10. StringsStoredAt: `embX`, `prjX`, `leafOK2`, `storedIn`.
11. StringsAt: `okRd` is `ok2` with the number 164; `cX`; `okA`; `bodyS`, `leafS`.
12. StringsOwn: `ownFitsS`.
WHAT TO TAKE. Code of bodies, reader or map, and test on body and salt go together in threes; do not
mix them.
 - A page with a prover's own leaves alone (the sibling's `PageFit`, `famOf`; the road from a parsed
   file): leaf code `pBody okRd`; spelling of a leaf `rdOk`; the page's default test.
   `pageFit_leaf`, `leaf_of_ok`, `okRd_of_ok`.
 - A page with both numbers, made by hand (`FitX`, `famT`): leaf code `pBody ok2`; map of leaves
   `call2`; test `leafOK2` at the page's configuration digest; stored symbols `embX a salt c`,
   `prjX a salt c`. `pBody2_tag`, `fitX_leaf`, `storedIn`, `storedGet`, `leafOK2_embTail`.
 - The sibling's general form at a description (`pageXPd`, `famXPd`): `bodyS D.a D.base.plan.salt`
   and `leafS D`: leaf code `pBody (okA ..)`; spelling `ownB`, which is `rdOk`; stored symbols
   `embX`, `prjX` at `cX`; test and map are the general form's own (`leafOKX`, `leafX`). `ownFitsS`.
 - A prover's symbol as a body: `StringsList.embT` at one list of rounds, `Stretches.embS` at three
   stretches; `Strings.embT` at the library's protocol alone.
 - NEVER as a page's leaf code: `pBody ok164`, `pBody okWhole` (too wide for a page that fits).
   NEVER as a page's spelling of a leaf: `rd`, `rd2` (they refuse nothing).
 - How the tests lie: `okRd` is `ok2` with the number 164 (StringsAt); `okA` is `ok2` with, under
   174, a stored symbol's string alone; so what passes `okRd` passes `okA`, and what passes `okA`
   passes `ok2`.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Tagged
import OnBytes.Slice.OwnString
import Run.PlanQS
import Run.CodingPage164

set_option autoImplicit false

namespace TypedOracleCompiler.Strings
open _root_.Compile Rom
open _root_.Iop (OPos OSym BatchInteractiveOracleProof)
open _root_.Run _root_.Run.PQ OnBytes.Slice

/-- the library's interface with bodies that are lists of bits -/
def strung {I X : Type} (L : _root_.Iop.BatchProtocol I X) : Iop.BatchProtocolWithLeafBody I X :=
  { L with Bd := List Bool, annT := _root_.Iop.RoundSplits.allLocal _, annL := _root_.Iop.RoundSplits.allLocal _ }

/- salt: the length of a file's salt, in bytes -/
variable (C : CK) (salt : ℕ) (ds : List RD) (dec : View → Bool)

/-- A symbol at a position, as a body: its leaf's own string; the empty string where its own tree's
code writes nothing (a tree deeper than 63). -/
def embT (p : OPos (Twin.up (SOf C ds))) (a : OSym (Twin.up (SOf C ds)) p) : List Bool :=
  (ownStr C salt ds (lower C ds ⟨p, a⟩)).getD []

/-- A body read at a position: by the code of that position's own tree; the column, if the place is
the position's. -/
def prjT : (p : OPos (Twin.up (SOf C ds))) → List Bool → Option (OSym (Twin.up (SOf C ds)) p)
  | .inl p, _ => p.elim
  | .inr q, b => rdLeaf C salt ds q b

/-- What is written is read back, if no tree is deeper than 63. No condition on the trees'
numbers. -/
theorem prjT_embT (hd : ∀ d ∈ ds, posN d.tree + posN d.tree ≤ 2 ^ 64) :
    ∀ (p : OPos (Twin.up (SOf C ds))) (a : OSym (Twin.up (SOf C ds)) p),
      prjT C salt ds p (embT C salt ds p a) = some a
  | .inl p, _ => p.elim
  | .inr q, a => by
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ownStr_some C salt ds hd ⟨q, a⟩)
      show rdLeaf C salt ds q ((ownStr C salt ds ⟨q, a⟩).getD []) = some a
      rw [hm]
      exact rdLeaf_own C salt ds q a m hm

/-- The body is the bits of the format's label, with the position's own tree's numbers, and of
column and fill, if no tree is deeper than 63. -/
theorem embT_fit (hd : ∀ d ∈ ds, posN d.tree + posN d.tree ≤ 2 ^ 64)
    (p : OPos (Twin.up (SOf C ds))) (a : OSym (Twin.up (SOf C ds)) p) :
    embT C salt ds p a =
      bytesToBits (_root_.Fmt.label 164 (leafSL C salt ds (lower C ds ⟨p, a⟩)).1
          (leafSL C salt ds (lower C ds ⟨p, a⟩)).2.1) ++
        bytesToBits (leafSL C salt ds (lower C ds ⟨p, a⟩)).2.2 := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ownStr_some C salt ds hd (lower C ds ⟨p, a⟩))
  unfold embT
  rw [hm]
  exact ownStr_fit C salt ds _ m hm

/-- A wire of the library at the interface whose Test is the generic protocol, as a wire of the
sibling with bodies that are strings. -/
def ofT (W : _root_.Iop.QueryLayout 256 (LtS C ds dec)) : Iop.QueryLayout 256 (strung (LtS C ds dec)) where
  K := W.K
  T := Tagged.ofQB W.T
  Lk := Tagged.ofQB W.Lk
  B := Tagged.ofQB W.B
  depth := W.depth
  depthReq := W.depthReq
  depthReqT := W.depthReq
  depthReqL := W.depthReq
  embE := fun _ => ([] : List Bool)
  prjE := fun _ => some ()
  embT := embT C salt ds
  prjT := prjT C salt ds
  embL := fun p _ => p.elim
  prjL := fun p _ => p.elim
  embB := fun p _ => p.elim
  prjB := fun p _ => p.elim

/-- A lawful wire of the library gives a lawful wire of the sibling with these bodies, if no
tree is deeper than 63. -/
theorem ofT_okg {W : _root_.Iop.QueryLayout 256 (LtS C ds dec)} (h : W.OKG)
    (hd : ∀ d ∈ ds, posN d.tree + posN d.tree ≤ 2 ^ 64) : (ofT C salt ds dec W).OKG where
  T := Tagged.ofQB_okg h.T
  Lk := Tagged.ofQB_okg h.Lk
  B := Tagged.ofQB_okg h.B
  fits := h.fits
  slots := h.slots
  extDepth := h.extDepth
  depthT := h.depthT
  depthL := h.depthL
  depthB := h.depthB
  extT := h.extT
  extB := h.extB
  extL := h.extL
  prjE_emb := fun _ => rfl
  prjT_emb := prjT_embT C salt ds hd
  prjL_emb := fun p _ => p.elim
  prjB_emb := fun p _ => p.elim

/-! ## The code of leaf queries -/

/-- The identity on the bodies that pass a test, as a partial code. -/
def pBody (ok : List Bool → Bool) : PCode (List Bool) where
  put := fun b => if ok b then some b else none
  parse := fun s => if ok s then some s else none
  parse_put := fun b s h => by
    by_cases hb : ok b = true
    · rw [if_pos hb] at h
      cases h
      exact if_pos hb
    · rw [if_neg hb] at h
      cases h
  put_parse := fun s b h => by
    by_cases hs : ok s = true
    · rw [if_pos hs] at h
      cases h
      exact if_pos hs
    · rw [if_neg hs] at h
      cases h

/-- A test on bodies: at least 16 bits, and the first 16 are those of the leaves' number 164. It is
what the assembly of a page asks of a code of leaves (the law `leafTag` of `PageC`, in the library
and in the sibling). IT IS TOO WIDE FOR A PAGE THAT FITS: see OnBytes/TypedOracleCompiler/StringsPage.lean; the test
to take is `okRd` of OnBytes/TypedOracleCompiler/StringsRead.lean. -/
def ok164 (b : List Bool) : Bool := decide (16 ≤ b.length) && decide (b.take 16 = t164)

/-- A symbol's body passes that test, if no tree is deeper than 63 and every tree's word begins with
these 16 bits (the library's test `tagsOK`). -/
theorem embT_ok164 (hd : ∀ d ∈ ds, posN d.tree + posN d.tree ≤ 2 ^ 64)
    (hk : tagsOK salt ds = true) (p : OPos (Twin.up (SOf C ds)))
    (a : OSym (Twin.up (SOf C ds)) p) : ok164 (embT C salt ds p a) = true := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ownStr_some C salt ds hd (lower C ds ⟨p, a⟩))
  have h := ownStr_tag C salt ds hk _ m hm
  unfold embT ok164
  rw [hm]
  simp [h.1, h.2]

/-- The code of leaf queries over bodies that are strings: the 33 bytes in front, the first 256 bits
of the typed salt, the body as it is, the rest of the typed salt (n bits). A query is written
exactly if its typed salt has 256 + n bits and its body passes ok. -/
def pLeafS {I X : Type} (L : _root_.Iop.BatchProtocol I X) (n : ℕ) (ok : List Bool → Bool) :
    PCode (Compile.Batch.LeafIn (strung L)) :=
  (pSalted pre33 n (pBody ok)).congr
    ⟨fun x => ⟨x.1, x.2⟩, fun q => (q.body, q.salt), fun _ => rfl, fun _ => rfl⟩

/-- A leaf query on a symbol is written, with the bits of `Fmt.oStr` at the number 164 and the
numbers of the position's own tree. start: 32 bytes; fsalt: a file's salt of the length `salt`;
the typed salt is the bits of the one and then of the other. Asked: no tree is deeper than 63; the
body passes the code's test (for `ok164`: `embT_ok164`). -/
theorem leaf_query (ok : List Bool → Bool) (hd : ∀ d ∈ ds, posN d.tree + posN d.tree ≤ 2 ^ 64)
    (p : OPos (Twin.up (SOf C ds))) (a : OSym (Twin.up (SOf C ds)) p)
    (hok : ok (embT C salt ds p a) = true)
    (start fsalt : ByteArray) (hs : start.size = 32) (hf : fsalt.size = salt) :
    (pLeafS (LtS C ds dec) (8 * salt) ok).put
        ⟨embT C salt ds p a, bytesToBits start ++ bytesToBits fsalt⟩ =
      some (bytesToBits (_root_.Fmt.oStr 0 164 (leafSL C salt ds (lower C ds ⟨p, a⟩)).1
        (leafSL C salt ds (lower C ds ⟨p, a⟩)).2.1 start
        ((leafSL C salt ds (lower C ds ⟨p, a⟩)).2.2 ++ fsalt))) := by
  have hl : (bytesToBits start ++ bytesToBits fsalt).length = 256 + 8 * salt := by
    rw [List.length_append, length_bytesToBits, length_bytesToBits, hs, hf]
  have h256 : (bytesToBits start).length = 256 := by rw [length_bytesToBits, hs]
  show (if (bytesToBits start ++ bytesToBits fsalt).length = 256 + 8 * salt then
      (if ok (embT C salt ds p a) then some (embT C salt ds p a) else none).map fun m =>
        pre33 ++ ((bytesToBits start ++ bytesToBits fsalt).take 256 ++
          (m ++ (bytesToBits start ++ bytesToBits fsalt).drop 256)) else none) = _
  rw [if_pos hl, if_pos hok, embT_fit C salt ds hd p a, List.take_left' h256,
    List.drop_left' h256, oStr32_bits 164 _ _ start _ (by decide) hs, bytesToBits_append]
  simp only [Option.map_some, List.append_assoc]

end TypedOracleCompiler.Strings
