-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ProofCut.lean: the strings of the typed queries of a proof file's part of the compiled
verifier, cut out of the page of all three files (`codeJ`, OnBytes/Maker/Page/Frame.lean), as one
function on the real points; and what is enough for that function to be one to one where it writes.

The function writes at the request tree's leaves and vertices, and at the chain queries and the
queries for the slot value under the proof file's tag: there the string of the row's call, where the
query passes a test of fitness (a request leaf has none: its call's own test of length is all) and
the call lies in the domain of the format's hash with the half 0 or 1. And it writes what three
spellings write that are taken as they are (`takenProof`). The seeds' two queries are typed under
the key file's tag, whichever part of the verifier tests a seed: so here the seeds' spelling is
taken as it is, under that tag; of the key file's own rows nothing is written. `inDom`, `bitsOf`,
`bitsOf_inj`, `fitTree` and the rows' numbers are those of OnBytes/K/Arm/KeyCut.lean. For proofs
only; the program does not import this file.

Main definitions.
 `ProofCut`       the data: the page, and two tests of fitness, for chain queries with a block and
                  for queries for the slot value under the proof file's tag. They are letters here.
 `rowProof`       the call of a real point, at the rows of the proof file and of the request tree.
 `takenProof`     what three spellings write that are taken as they are: the page's leaves; the
                  library's code of vertices (`pNode`, Run/CodingPage166.lean); the page's field
                  `seeds` (meant: the seeds' two queries; the type does not bound it).
 `cutProof`       the function.
Main theorems.
 `cutProof_leaf`  with `cutProof_node`, `cutProof_seeds`, `cutProof_test`, `cutProof_fb`,
                  `cutProof_g`, `cutProof_rleaf`, `cutProof_rnode`, `cutProof_others`: what it
                  writes, kind by kind.
 `rowProof_inj`   `rowProof` is one to one, if it is so within each of its four kinds, and no chain
                  query shares a call with a query for the slot value.
 `cutProof_inj`   `cutProof` is one to one where it writes, if `rowProof` is, the three spellings
                  together are, and no string of a spelling is the string of a row's call.

What is not claimed. That any of the premises holds at any data. That the verifier's queries pass
the tests of fitness, or that their calls lie in the domain. That what it writes at a leaf or a
vertex is `codeJ`'s string there. No theorem here compares it with `codeJ` at any kind of point.
That the strings are those that the programs hash at a file. Nothing on the key file's own or the
entry file's queries. Nothing on any hash function; nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.KeyCut

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type}

/-- **The data of the cut**: the page; which chain queries with a block, and which queries for the
slot value, under the proof file's tag fit. -/
structure ProofCut (L : BatchProtocolWithLeafBody I X) (K : ℕ) where
  /-- the page of all three files -/
  P : PageJ L K
  /-- a chain query with a block fits -/
  fitFb : FbIn 256 L .onl × Fin (K + 1) → Bool
  /-- a query for the slot value fits -/
  fitG : JoiningRoundQuery 256 L .onl → Bool

variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : ProofCut L K)

/-- **The call of a real point**, at the rows of the proof file and of the request tree; nothing at
leaves and vertices, which are taken as they are, and nothing under the two other tags. -/
def rowProof : RealPts 256 K L → Option Fmt.OQ
  | .inl _ => none
  | .inr (.inl _) => none
  | .inr (.inr (.inl q)) => rleafCall C.P.cfg C.P.sR q
  | .inr (.inr (.inr (.inl q))) => if fitTree q = true then rnodeCall C.P.cfg q else none
  | .inr (.inr (.inr (.inr (.inl ⟨.onl, x⟩)))) =>
    if C.fitFb x = true then fbCallJ C.P.proof K x.1 x.2 else none
  | .inr (.inr (.inr (.inr (.inl ⟨.test, _⟩)))) => none
  | .inr (.inr (.inr (.inr (.inl ⟨.link, _⟩)))) => none
  | .inr (.inr (.inr (.inr (.inr ⟨.onl, q⟩)))) =>
    if C.fitG q = true then gCallJ C.P.proof q else none
  | .inr (.inr (.inr (.inr (.inr ⟨.test, _⟩)))) => none
  | .inr (.inr (.inr (.inr (.inr ⟨.link, _⟩)))) => none

/-- **What three spellings write** that are taken as they are: the page's leaves; the library's code
of vertices, at the page's digest; the seeds' two queries, under the key file's tag. -/
def takenProof : RealPts 256 K L → Option (List Bool)
  | .inl q => C.P.leafX q
  | .inr (.inl q) => (pNode C.P.cfg).put q
  | .inr (.inr (.inr (.inr (.inl ⟨.test, x⟩)))) => C.P.seeds x
  | _ => none

/-- **The strings of the proof file's part.** A spelling goes first, as in `codeJ`; here the
spellings and the rows write at different kinds of points, so the order decides nothing. At a leaf
nothing but the spelling `leafX` is written; `codeJ` falls back on the page's field `leaf` where
`leafX` does not write. -/
def cutProof (a : RealPts 256 K L) : Option (List Bool) :=
  match takenProof C a with
  | some s => some s
  | none => (rowProof C a).bind bitsOf

/-! ## What it writes, kind by kind -/

/-- At a leaf: what the page's spelling of leaves writes. -/
theorem cutProof_leaf (q : LeafIn L) : cutProof C (.inl q) = C.P.leafX q := by
  unfold cutProof
  show (match C.P.leafX q with
    | some s => some s
    | none => none) = _
  cases C.P.leafX q <;> rfl

/-- At a vertex: what the library's code of vertices writes. -/
theorem cutProof_node (q : Bits × Bits) :
    cutProof C (.inr (.inl q)) = (pNode C.P.cfg).put q := by
  unfold cutProof
  show (match (pNode C.P.cfg).put q with
    | some s => some s
    | none => none) = _
  cases (pNode C.P.cfg).put q <;> rfl

/-- At a chain query under the key file's tag: what the seeds' spelling writes, and nothing else. -/
theorem cutProof_test (x : FbIn 256 L .test × Fin (K + 1)) :
    cutProof C (.inr (.inr (.inr (.inr (.inl ⟨.test, x⟩))))) = C.P.seeds x := by
  unfold cutProof
  show (match C.P.seeds x with
    | some s => some s
    | none => none) = _
  cases C.P.seeds x <;> rfl

/-- Where the seeds' spelling writes: that string. -/
theorem cutProof_seeds (x : FbIn 256 L .test × Fin (K + 1)) (s : List Bool)
    (h : C.P.seeds x = some s) :
    cutProof C (.inr (.inr (.inr (.inr (.inl ⟨.test, x⟩))))) = some s :=
  (cutProof_test C x).trans h

/-- At a fitting chain query under the proof file's tag: the bits of the string of the row's
call. -/
theorem cutProof_fb (x : FbIn 256 L .onl × Fin (K + 1)) (c : Fmt.OQ) (hf : C.fitFb x = true)
    (hc : fbCallJ C.P.proof K x.1 x.2 = some c) (hd : inDom c = true) :
    cutProof C (.inr (.inr (.inr (.inr (.inl ⟨.onl, x⟩))))) = some (bytesToBits (strOf c)) := by
  show (if C.fitFb x = true then fbCallJ C.P.proof K x.1 x.2 else none).bind bitsOf = _
  rw [if_pos hf, hc]
  show bitsOf c = _
  unfold bitsOf
  rw [if_pos hd]

/-- At a fitting query for the slot value under the proof file's tag. -/
theorem cutProof_g (q : JoiningRoundQuery 256 L .onl) (c : Fmt.OQ) (hf : C.fitG q = true)
    (hc : gCallJ C.P.proof q = some c) (hd : inDom c = true) :
    cutProof C (.inr (.inr (.inr (.inr (.inr ⟨.onl, q⟩))))) = some (bytesToBits (strOf c)) := by
  show (if C.fitG q = true then gCallJ C.P.proof q else none).bind bitsOf = _
  rw [if_pos hf, hc]
  show bitsOf c = _
  unfold bitsOf
  rw [if_pos hd]

/-- At a leaf of the request tree. -/
theorem cutProof_rleaf (q : Bits) (c : Fmt.OQ) (hc : rleafCall C.P.cfg C.P.sR q = some c)
    (hd : inDom c = true) :
    cutProof C (.inr (.inr (.inl q))) = some (bytesToBits (strOf c)) := by
  show (rleafCall C.P.cfg C.P.sR q).bind bitsOf = _
  rw [hc]
  show bitsOf c = _
  unfold bitsOf
  rw [if_pos hd]

/-- At a vertex of the request tree whose children have a digest's bits. -/
theorem cutProof_rnode (q : Bits × Bits) (c : Fmt.OQ) (hf : fitTree q = true)
    (hc : rnodeCall C.P.cfg q = some c) (hd : inDom c = true) :
    cutProof C (.inr (.inr (.inr (.inl q)))) = some (bytesToBits (strOf c)) := by
  show (if fitTree q = true then rnodeCall C.P.cfg q else none).bind bitsOf = _
  rw [if_pos hf, hc]
  show bitsOf c = _
  unfold bitsOf
  rw [if_pos hd]

/-- Nothing under the entry file's tag, and nothing at a query for the slot value under the key
file's. -/
theorem cutProof_others :
    (∀ x, cutProof C (.inr (.inr (.inr (.inr (.inl ⟨.link, x⟩))))) = none) ∧
      (∀ q, cutProof C (.inr (.inr (.inr (.inr (.inr ⟨.test, q⟩))))) = none) ∧
      ∀ q, cutProof C (.inr (.inr (.inr (.inr (.inr ⟨.link, q⟩))))) = none :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## One to one -/

/-- What a row's call says of its point. -/
theorem rowProof_cases (a : RealPts 256 K L) (c : Fmt.OQ) (h : rowProof C a = some c) :
    (∃ q, a = .inr (.inr (.inl q)) ∧ rleafCall C.P.cfg C.P.sR q = some c) ∨
    (∃ q, a = .inr (.inr (.inr (.inl q))) ∧ fitTree q = true ∧ rnodeCall C.P.cfg q = some c) ∨
    (∃ x, a = .inr (.inr (.inr (.inr (.inl ⟨.onl, x⟩)))) ∧ C.fitFb x = true ∧
      fbCallJ C.P.proof K x.1 x.2 = some c) ∨
    (∃ q, a = .inr (.inr (.inr (.inr (.inr ⟨.onl, q⟩)))) ∧ C.fitG q = true ∧
      gCallJ C.P.proof q = some c) := by
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
    · cases h
    · cases h
    · have h' : (if C.fitFb x = true then fbCallJ C.P.proof K x.1 x.2 else none) = some c := h
      by_cases f : C.fitFb x = true
      · rw [if_pos f] at h'
        exact Or.inr (Or.inr (Or.inl ⟨x, rfl, f, h'⟩))
      · rw [if_neg f] at h'
        cases h'
  · cases t
    · cases h
    · cases h
    · have h' : (if C.fitG q = true then gCallJ C.P.proof q else none) = some c := h
      by_cases f : C.fitG q = true
      · rw [if_pos f] at h'
        exact Or.inr (Or.inr (Or.inr ⟨q, rfl, f, h'⟩))
      · rw [if_neg f] at h'
        cases h'

/-- **The rows' calls are one to one**, if they are so within each of the four kinds, and no chain
query shares a call with a query for the slot value. -/
theorem rowProof_inj
    (hrl : ∀ q q' c, rleafCall C.P.cfg C.P.sR q = some c → rleafCall C.P.cfg C.P.sR q' = some c →
      q = q')
    (hrn : ∀ q q' c, fitTree q = true → fitTree q' = true → rnodeCall C.P.cfg q = some c →
      rnodeCall C.P.cfg q' = some c → q = q')
    (hfb : ∀ x x' c, C.fitFb x = true → C.fitFb x' = true →
      fbCallJ C.P.proof K x.1 x.2 = some c → fbCallJ C.P.proof K x'.1 x'.2 = some c → x = x')
    (hg : ∀ q q' c, C.fitG q = true → C.fitG q' = true → gCallJ C.P.proof q = some c →
      gCallJ C.P.proof q' = some c → q = q')
    (hfg : ∀ x q c, C.fitFb x = true → C.fitG q = true → fbCallJ C.P.proof K x.1 x.2 = some c →
      gCallJ C.P.proof q ≠ some c) :
    ∀ a b c, rowProof C a = some c → rowProof C b = some c → a = b := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := numbers_differ
  intro a b c ha hb
  rcases rowProof_cases C a c ha with
      ⟨q, rfl, h1⟩ | ⟨q, rfl, f1, h1⟩ | ⟨x, rfl, f1, h1⟩ | ⟨q, rfl, f1, h1⟩ <;>
    rcases rowProof_cases C b c hb with
      ⟨q', rfl, h2⟩ | ⟨q', rfl, f2, h2⟩ | ⟨x', rfl, f2, h2⟩ | ⟨q', rfl, f2, h2⟩
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

/-- **The function is one to one where it writes**, if the rows' calls are, the three spellings
together are, and no string of a spelling is the string of a row's call. -/
theorem cutProof_inj
    (hR : ∀ a b c, rowProof C a = some c → rowProof C b = some c → a = b)
    (hX : ∀ a b s, takenProof C a = some s → takenProof C b = some s → a = b)
    (hXR : ∀ a b s c, takenProof C a = some s → rowProof C b = some c → bitsOf c ≠ some s) :
    ∀ a b s, cutProof C a = some s → cutProof C b = some s → a = b := by
  intro a b s ha hb
  unfold cutProof at ha hb
  cases ta : takenProof C a with
  | some u =>
    rw [ta] at ha
    obtain rfl : u = s := Option.some.inj ha
    cases tb : takenProof C b with
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
    cases tb : takenProof C b with
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
