-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/KeyCut.lean: the strings of the typed queries of a key file's part of the compiled
verifier, cut out of the page of all three files (`codeJ`, OnBytes/Maker/Page/Frame.lean), as one
function on the real points; and what is enough for that function to be one to one where it writes.

`codeJ` gives a typed query and a block of its answer the string that the programs' format is meant
to hash there. Over all three files it is not one to one: its own head says why. An encoding in the
sense of the soundness theorem (`Rom.OracleCoding`) is one to one. OnBytes/TypedOracleCompiler/Run/PageOf.lean makes such an
encoding of any function on the real points that is one to one where it writes and whose strings
begin with the byte 0 or 1, and of a total code. Here the function for the key file is written. It
writes at the request tree's leaves and vertices, and at the chain queries and the queries for the
slot value under the key file's tag: there the string of the row's call, where the query passes a
test of fitness (a request leaf has none: its call's own test of length is all) and the call lies in
the domain of the format's hash with the half 0 or 1. And it writes what three spellings write that
are taken as they are: the page's leaves, the library's code of vertices (`pNode`,
Run/CodingPage166.lean), the page's field `seeds` (meant: the seeds' two queries; the type does not
bound it). A spelling goes first: where the field `seeds` writes at a chain query under the key
file's tag, the key file's own row at that point is not written. It writes nothing under the two
other tags. For proofs only; the program does not import this file.

Main definitions.
 `KeyCut`         the data: the page, and two tests of fitness, for chain queries with a block and
                  for queries for the slot value. They are letters here.
 `inDom`          the test on a call: the half is 0 or 1, and `Fmt.hDom` holds.
 `rowKey`         the call of a real point, at the rows of the key file and of the request tree.
 `takenKey`       what the three spellings write.
 `cutKey`         the function.
Main theorems.
 `cutKey_leaf`    with `cutKey_node`, `cutKey_seeds`, `cutKey_fb`, `cutKey_g`, `cutKey_rleaf`,
                  `cutKey_rnode`, `cutKey_others`: what it writes, kind by kind.
 `fb_number`      with `g_number`, `rleaf_number`, `rnode_number`, `numbers_differ`: the format's
                  number of a row's call, by the kind of the point.
 `rowKey_inj`     `rowKey` is one to one, if it is so within each of its four kinds, and no chain
                  query shares a call with a query for the slot value.
 `bitsOf_inj`     on the domain a call is known from the bits of its string.
 `cutKey_inj`     `cutKey` is one to one where it writes, if `rowKey` is, the three spellings
                  together are, and no string of a spelling is the string of a row's call.

What is not claimed. That any of the premises holds at any data. That the verifier's queries pass
the tests of fitness, or that their calls lie in the domain. That what it writes at a leaf or a
vertex is `codeJ`'s string there. No theorem here compares it with `codeJ` at any kind of point.
That the strings are those that the programs hash at a file. Nothing on the entry file's or the
proof file's queries. Nothing on any hash function; nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.Maker.Page.Frame
import OnBytes.TypedOracleCompiler.Run.CodingImpl
import Fmt.Rules23Laws
import Run.CodingBitsLaws
import Run.CodingPage166

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type}

/-! ## The format's numbers of the rows -/

/-- The format's number of the call that makes a chain's first value. -/
def nFirst : ℕ := 160
/-- Of a call of a round's row. -/
def nRow : ℕ := 162
/-- Of a vertex. -/
def nNode : ℕ := 166
/-- Of a leaf of the request tree. -/
def nRLeaf : ℕ := 173
/-- Of a vertex of the request tree. -/
def nRNode : ℕ := 178

/-- The bits of a digest. -/
def digBits : ℕ := 256

/-! ## The function -/

/-- The call lies in the domain of the format's hash, and its half is 0 or 1. -/
def inDom (c : Fmt.OQ) : Bool :=
  (c.half == 0 || c.half == 1) && Fmt.hDom c.number c.tree c.index c.start c.bytes

/-- **The data of the cut**: the page; which chain queries with a block, and which queries for the
slot value, under the key file's tag fit. -/
structure KeyCut (L : BatchProtocolWithLeafBody I X) (K : ℕ) where
  /-- the page of all three files -/
  P : PageJ L K
  /-- a chain query with a block fits -/
  fitFb : FbIn 256 L .test × Fin (K + 1) → Bool
  /-- a query for the slot value fits -/
  fitG : JoiningRoundQuery 256 L .test → Bool

/-- Both children of a vertex have a digest's bits. -/
def fitTree (q : Bits × Bits) : Bool := q.1.length == digBits && q.2.length == digBits

variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : KeyCut L K)

/-- **The call of a real point**, at the rows of the key file and of the request tree; nothing at
leaves and vertices, which are taken as they are, and nothing under the two other tags. -/
def rowKey : RealPts 256 K L → Option Fmt.OQ
  | .inl _ => none
  | .inr (.inl _) => none
  | .inr (.inr (.inl q)) => rleafCall C.P.cfg C.P.sR q
  | .inr (.inr (.inr (.inl q))) => if fitTree q = true then rnodeCall C.P.cfg q else none
  | .inr (.inr (.inr (.inr (.inl ⟨.test, x⟩)))) =>
    if C.fitFb x = true then fbCallJ C.P.key K x.1 x.2 else none
  | .inr (.inr (.inr (.inr (.inl ⟨.link, _⟩)))) => none
  | .inr (.inr (.inr (.inr (.inl ⟨.onl, _⟩)))) => none
  | .inr (.inr (.inr (.inr (.inr ⟨.test, q⟩)))) =>
    if C.fitG q = true then gCallJ C.P.key q else none
  | .inr (.inr (.inr (.inr (.inr ⟨.link, _⟩)))) => none
  | .inr (.inr (.inr (.inr (.inr ⟨.onl, _⟩)))) => none

/-- **What three spellings write** that are taken as they are: the page's leaves; the library's code
of vertices, at the page's digest; the page's field `seeds`, meant for the seeds' two queries. -/
def takenKey : RealPts 256 K L → Option (List Bool)
  | .inl q => C.P.leafX q
  | .inr (.inl q) => (pNode C.P.cfg).put q
  | .inr (.inr (.inr (.inr (.inl ⟨.test, x⟩)))) => C.P.seeds x
  | _ => none

/-- The bits of a call's string, if the call lies in the domain. -/
def bitsOf (c : Fmt.OQ) : Option (List Bool) :=
  if inDom c = true then some (bytesToBits (strOf c)) else none

/-- **The strings of the key file's part.** A spelling goes first, as in `codeJ`. At a leaf nothing
but the spelling `leafX` is written; `codeJ` falls back on the page's field `leaf` where `leafX`
does not write. -/
def cutKey (a : RealPts 256 K L) : Option (List Bool) :=
  match takenKey C a with
  | some s => some s
  | none => (rowKey C a).bind bitsOf

/-! ## What it writes, kind by kind -/

/-- At a leaf: what the page's spelling of leaves writes. -/
theorem cutKey_leaf (q : LeafIn L) : cutKey C (.inl q) = C.P.leafX q := by
  unfold cutKey
  show (match C.P.leafX q with
    | some s => some s
    | none => none) = _
  cases C.P.leafX q <;> rfl

/-- At a vertex: what the library's code of vertices writes. -/
theorem cutKey_node (q : Bits × Bits) : cutKey C (.inr (.inl q)) = (pNode C.P.cfg).put q := by
  unfold cutKey
  show (match (pNode C.P.cfg).put q with
    | some s => some s
    | none => none) = _
  cases (pNode C.P.cfg).put q <;> rfl

/-- At a chain query under the key file's tag at which the seeds' spelling writes: that string. -/
theorem cutKey_seeds (x : FbIn 256 L .test × Fin (K + 1)) (s : List Bool)
    (h : C.P.seeds x = some s) :
    cutKey C (.inr (.inr (.inr (.inr (.inl ⟨.test, x⟩))))) = some s := by
  unfold cutKey
  show (match C.P.seeds x with
    | some s => some s
    | none => _) = _
  rw [h]

/-- At a fitting chain query under the key file's tag at which the seeds' spelling does not write:
the bits of the string of the row's call. -/
theorem cutKey_fb (x : FbIn 256 L .test × Fin (K + 1)) (c : Fmt.OQ) (hs : C.P.seeds x = none)
    (hf : C.fitFb x = true) (hc : fbCallJ C.P.key K x.1 x.2 = some c) (hd : inDom c = true) :
    cutKey C (.inr (.inr (.inr (.inr (.inl ⟨.test, x⟩))))) = some (bytesToBits (strOf c)) := by
  unfold cutKey
  show (match C.P.seeds x with
    | some s => some s
    | none => (if C.fitFb x = true then fbCallJ C.P.key K x.1 x.2 else none).bind bitsOf) = _
  rw [hs, if_pos hf, hc]
  show bitsOf c = _
  unfold bitsOf
  rw [if_pos hd]

/-- At a fitting query for the slot value under the key file's tag. -/
theorem cutKey_g (q : JoiningRoundQuery 256 L .test) (c : Fmt.OQ) (hf : C.fitG q = true)
    (hc : gCallJ C.P.key q = some c) (hd : inDom c = true) :
    cutKey C (.inr (.inr (.inr (.inr (.inr ⟨.test, q⟩))))) = some (bytesToBits (strOf c)) := by
  show (if C.fitG q = true then gCallJ C.P.key q else none).bind bitsOf = _
  rw [if_pos hf, hc]
  show bitsOf c = _
  unfold bitsOf
  rw [if_pos hd]

/-- At a leaf of the request tree. -/
theorem cutKey_rleaf (q : Bits) (c : Fmt.OQ) (hc : rleafCall C.P.cfg C.P.sR q = some c)
    (hd : inDom c = true) :
    cutKey C (.inr (.inr (.inl q))) = some (bytesToBits (strOf c)) := by
  show (rleafCall C.P.cfg C.P.sR q).bind bitsOf = _
  rw [hc]
  show bitsOf c = _
  unfold bitsOf
  rw [if_pos hd]

/-- At a vertex of the request tree whose children have a digest's bits. -/
theorem cutKey_rnode (q : Bits × Bits) (c : Fmt.OQ) (hf : fitTree q = true)
    (hc : rnodeCall C.P.cfg q = some c) (hd : inDom c = true) :
    cutKey C (.inr (.inr (.inr (.inl q)))) = some (bytesToBits (strOf c)) := by
  show (if fitTree q = true then rnodeCall C.P.cfg q else none).bind bitsOf = _
  rw [if_pos hf, hc]
  show bitsOf c = _
  unfold bitsOf
  rw [if_pos hd]

/-- Nothing under the entry file's tag and nothing under the proof file's. -/
theorem cutKey_others :
    (∀ x, cutKey C (.inr (.inr (.inr (.inr (.inl ⟨.link, x⟩))))) = none) ∧
      (∀ x, cutKey C (.inr (.inr (.inr (.inr (.inl ⟨.onl, x⟩))))) = none) ∧
      (∀ q, cutKey C (.inr (.inr (.inr (.inr (.inr ⟨.link, q⟩))))) = none) ∧
      ∀ q, cutKey C (.inr (.inr (.inr (.inr (.inr ⟨.onl, q⟩))))) = none :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## The rows' numbers -/

/-- A chain query's call is a first call or a row's. -/
theorem fb_number {t : Tag} (F : FileJ L t) (q : FbIn 256 L t) (j : Fin (K + 1)) (c : Fmt.OQ)
    (h : fbCallJ F K q j = some c) : c.number = nFirst ∨ c.number = nRow := by
  unfold fbCallJ at h
  split at h <;> (repeat' split at h) <;>
    first
      | (obtain rfl := Option.some.inj h
         first
           | exact Or.inl rfl
           | exact Or.inr rfl)
      | cases h

/-- The call for the slot value is a row's. -/
theorem g_number {t : Tag} (F : FileJ L t) (q : JoiningRoundQuery 256 L t) (c : Fmt.OQ)
    (h : gCallJ F q = some c) : c.number = nRow := by
  unfold gCallJ at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- The number of a request leaf's call. -/
theorem rleaf_number (cfg : ByteArray) (sR : ℕ) (q : Bits) (c : Fmt.OQ)
    (h : rleafCall cfg sR q = some c) : c.number = nRLeaf := by
  unfold rleafCall at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- The number of a request vertex's call. -/
theorem rnode_number (cfg : ByteArray) (q : Bits × Bits) (c : Fmt.OQ)
    (h : rnodeCall cfg q = some c) : c.number = nRNode := by
  obtain rfl := Option.some.inj h
  rfl

/-- The four numbers of the rows differ where the kinds of points differ. -/
theorem numbers_differ :
    nRLeaf ≠ nRNode ∧ nRLeaf ≠ nFirst ∧ nRLeaf ≠ nRow ∧ nRNode ≠ nFirst ∧ nRNode ≠ nRow := by
  decide

/-! ## One to one -/

/-- **The rows' calls are one to one**, if they are so within each of the four kinds, and no chain
query shares a call with a query for the slot value. -/
theorem rowKey_inj
    (hrl : ∀ q q' c, rleafCall C.P.cfg C.P.sR q = some c → rleafCall C.P.cfg C.P.sR q' = some c →
      q = q')
    (hrn : ∀ q q' c, fitTree q = true → fitTree q' = true → rnodeCall C.P.cfg q = some c →
      rnodeCall C.P.cfg q' = some c → q = q')
    (hfb : ∀ x x' c, C.fitFb x = true → C.fitFb x' = true → fbCallJ C.P.key K x.1 x.2 = some c →
      fbCallJ C.P.key K x'.1 x'.2 = some c → x = x')
    (hg : ∀ q q' c, C.fitG q = true → C.fitG q' = true → gCallJ C.P.key q = some c →
      gCallJ C.P.key q' = some c → q = q')
    (hfg : ∀ x q c, C.fitFb x = true → C.fitG q = true → fbCallJ C.P.key K x.1 x.2 = some c →
      gCallJ C.P.key q ≠ some c) :
    ∀ a b c, rowKey C a = some c → rowKey C b = some c → a = b := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := numbers_differ
  -- what a row's call says of its point
  have key : ∀ a c, rowKey C a = some c →
      (∃ q, a = .inr (.inr (.inl q)) ∧ rleafCall C.P.cfg C.P.sR q = some c) ∨
      (∃ q, a = .inr (.inr (.inr (.inl q))) ∧ fitTree q = true ∧ rnodeCall C.P.cfg q = some c) ∨
      (∃ x, a = .inr (.inr (.inr (.inr (.inl ⟨.test, x⟩)))) ∧ C.fitFb x = true ∧
        fbCallJ C.P.key K x.1 x.2 = some c) ∨
      (∃ q, a = .inr (.inr (.inr (.inr (.inr ⟨.test, q⟩)))) ∧ C.fitG q = true ∧
        gCallJ C.P.key q = some c) := by
    intro a c h
    rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
    · cases h
    · cases h
    · exact Or.inl ⟨q, rfl, h⟩
    · have h' : (if fitTree q = true then rnodeCall C.P.cfg q else none) = some c := h
      by_cases f : fitTree q = true
      · rw [if_pos f] at h'
        exact Or.inr (Or.inl ⟨q, rfl, f, h'⟩)
      · rw [if_neg f] at h'
        cases h'
    · cases t
      · have h' : (if C.fitFb x = true then fbCallJ C.P.key K x.1 x.2 else none) = some c := h
        by_cases f : C.fitFb x = true
        · rw [if_pos f] at h'
          exact Or.inr (Or.inr (Or.inl ⟨x, rfl, f, h'⟩))
        · rw [if_neg f] at h'
          cases h'
      · cases h
      · cases h
    · cases t
      · have h' : (if C.fitG q = true then gCallJ C.P.key q else none) = some c := h
        by_cases f : C.fitG q = true
        · rw [if_pos f] at h'
          exact Or.inr (Or.inr (Or.inr ⟨q, rfl, f, h'⟩))
        · rw [if_neg f] at h'
          cases h'
      · cases h
      · cases h
  intro a b c ha hb
  rcases key a c ha with ⟨q, rfl, h1⟩ | ⟨q, rfl, f1, h1⟩ | ⟨x, rfl, f1, h1⟩ | ⟨q, rfl, f1, h1⟩ <;>
    rcases key b c hb with ⟨q', rfl, h2⟩ | ⟨q', rfl, f2, h2⟩ | ⟨x', rfl, f2, h2⟩ | ⟨q', rfl, f2, h2⟩
  · rw [hrl q q' c h1 h2]
  · exact absurd ((rleaf_number _ _ _ _ h1).symm.trans (rnode_number _ _ _ h2)) d1
  · rcases fb_number _ _ _ _ h2 with e | e
    · exact absurd ((rleaf_number _ _ _ _ h1).symm.trans e) d2
    · exact absurd ((rleaf_number _ _ _ _ h1).symm.trans e) d3
  · exact absurd ((rleaf_number _ _ _ _ h1).symm.trans (g_number _ _ _ h2)) d3
  · exact absurd ((rleaf_number _ _ _ _ h2).symm.trans (rnode_number _ _ _ h1)) d1
  · rw [hrn q q' c f1 f2 h1 h2]
  · rcases fb_number _ _ _ _ h2 with e | e
    · exact absurd ((rnode_number _ _ _ h1).symm.trans e) d4
    · exact absurd ((rnode_number _ _ _ h1).symm.trans e) d5
  · exact absurd ((rnode_number _ _ _ h1).symm.trans (g_number _ _ _ h2)) d5
  · rcases fb_number _ _ _ _ h1 with e | e
    · exact absurd ((rleaf_number _ _ _ _ h2).symm.trans e) d2
    · exact absurd ((rleaf_number _ _ _ _ h2).symm.trans e) d3
  · rcases fb_number _ _ _ _ h1 with e | e
    · exact absurd ((rnode_number _ _ _ h2).symm.trans e) d4
    · exact absurd ((rnode_number _ _ _ h2).symm.trans e) d5
  · rw [hfb x x' c f1 f2 h1 h2]
  · exact absurd h2 (hfg x q' c f1 f2 h1)
  · exact absurd ((rleaf_number _ _ _ _ h2).symm.trans (g_number _ _ _ h1)) d3
  · exact absurd ((rnode_number _ _ _ h2).symm.trans (g_number _ _ _ h1)) d5
  · exact absurd h1 (hfg x' q c f2 f1 h2)
  · rw [hg q q' c f1 f2 h1 h2]


/-- On the domain a call is known from the bits of its string. -/
theorem bitsOf_inj (c c' : Fmt.OQ) (s : List Bool) (h : bitsOf c = some s)
    (h' : bitsOf c' = some s) : c = c' := by
  unfold bitsOf at h h'
  by_cases d : inDom c = true
  · by_cases d' : inDom c' = true
    · rw [if_pos d] at h
      rw [if_pos d'] at h'
      have e : strOf c = strOf c' :=
        bytesToBits_inj ((Option.some.inj h).trans (Option.some.inj h').symm)
      unfold inDom at d d'
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at d d'
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Fmt.oStr_inj _ _ _ _ _ _ _ _ _ _ _ _ d.1 d'.1 d.2 d'.2 e
      cases c
      cases c'
      simp only at a1 a2 a3 a4 a5 a6
      subst a1 a2 a3 a4 a5 a6
      rfl
    · rw [if_neg d'] at h'
      cases h'
  · rw [if_neg d] at h
    cases h

/-- **The function is one to one where it writes**, if the rows' calls are, the three spellings
together are, and no string of a spelling is the string of a row's call. -/
theorem cutKey_inj
    (hR : ∀ a b c, rowKey C a = some c → rowKey C b = some c → a = b)
    (hX : ∀ a b s, takenKey C a = some s → takenKey C b = some s → a = b)
    (hXR : ∀ a b s c, takenKey C a = some s → rowKey C b = some c → bitsOf c ≠ some s) :
    ∀ a b s, cutKey C a = some s → cutKey C b = some s → a = b := by
  intro a b s ha hb
  unfold cutKey at ha hb
  cases ta : takenKey C a with
  | some u =>
    rw [ta] at ha
    obtain rfl : u = s := Option.some.inj ha
    cases tb : takenKey C b with
    | some v =>
      rw [tb] at hb
      obtain rfl : v = u := Option.some.inj hb
      exact hX a b v ta tb
    | none =>
      rw [tb] at hb
      obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 hb
      exact absurd hs (hXR a b u c ta hc)
  | none =>
    rw [ta] at ha
    obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 ha
    cases tb : takenKey C b with
    | some v =>
      rw [tb] at hb
      obtain rfl : v = s := Option.some.inj hb
      exact absurd hs (hXR b a v c tb hc)
    | none =>
      rw [tb] at hb
      obtain ⟨c', hc', hs'⟩ := Option.bind_eq_some_iff.1 hb
      obtain rfl := bitsOf_inj c c' s hs hs'
      exact hR a b c hc hc'

end OnBytes.K.Arm
