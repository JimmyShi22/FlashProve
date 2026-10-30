-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPageX.lean: the encoding of the typed queries of the compiled scheme into the single
oracle's strings, with the stored tables' leaves among the queries that the format writes: the
assembly.

Definitions that compute, with their laws; the family over a single oracle (`OracleCoding`, Rom/Family.lean)
with its inverse and both laws.
Run/CodingPage.lean puts four partial codes together: a chain's first query (160), a round's query
(162), a leaf of a tree of a run (164), a vertex (166). A chain that opens stored tables also hashes
leaves under the number 174. Here a fifth partial code stands beside the four: a leaf query on a
symbol of an encoded index (`L.Symbol`: what a leaf of a stored table holds) is written as a call number
174 (Run/CodingPage174.lean). All else is Run/CodingPage.lean's: its data `PageC`, its codes of own
leaves, vertices and chain queries, its choice of the points that the format may write (`sel3`,
`mk3`), its two escape bytes, and `implA` (Run/CodingImpl.lean).

The data (`PageCX L K t`): those of `PageC L K t`, and
  `storedP`: a partial code of the symbols of an encoded index that writes label, column, fill;
    asked (`storedTag`): its strings begin with the 16 bits of the stored leaves' number.
The stored leaves take the start of a vertex (`cfg`) and the bits of a file's salt (`saltBits`) from
`PageC`'s fields.

Main names:
  `PCode.join p q`: two partial codes on one type that write no common string and no common
    point, as one partial code.
  `pLeaf2 C`: leaf queries of both kinds. `pAllX C`: all that the format writes, as a partial code
    of the real and the ghost points (`AllPts`, Run/CodingImpl.lean).
  `totalX C`: a point that the format writes: its string of the format; every other point: the byte
    2 and then its string under "back".
  `theImplX C`: `implA` at "totalX", with the byte 3 as the escape of the spare strings.
  `theImplX_own`, `theImplX_stored`, `theImplX_node`, `theImplX_fb`: the string of a typed query
    that the format writes is the partial code's string.
  `theImplX_spare`: a bit string that the total code does not write, and that does not begin with
    the byte 3, is written as itself as a point of the spare oracle. `theImplX_other`: so is a bit
    string that begins with neither escape and has none of the five tags (`Tag5`).
  `theImplX_leaf1`, `theImplX_node1`, `theImplX_rngLeaf`, `theImplX_rngNode`: a leaf's and a
    vertex's answer is one block, unchanged.

Limits: this file says nothing on the data at a protocol (at a description of a chain with stored
tables: Run/PageX.lean). That the strings are those of the functions by which Run/PlanQXRun.lean
spells typed queries (`famX`) is not shown in this file (Run/PageXFit.lean). "The format writes"
means here: one of the five partial codes of the data C writes; "the format" is this library's Lean
text of it (Fmt/Rules23.lean: `Fmt.oStr`), which is not compared here with the format page or with
any program. That a string written here lies in the format's domain (`Fmt.hDom`) is not asked and
not claimed. The partial codes that Run/CodingPage.lean puts together (Run/CodingPage160.lean, 162,
164, 166) were written against editions of the format page that are not the one that ships (their
heads say which); no rule was compared anew. Where `storedP` writes, `theImplX C` and `theImpl
C.toPageC` differ, among other points, at the stored leaves that it writes and at the spare oracle's
points with these leaves' two strings (the format's, and the one behind the byte 2); where it writes
nothing the two are one (Run/CodingPageXIs.lean [not in this library]; so here read: not proved in
this library). This file says nothing on a hash.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPage174

set_option autoImplicit false

namespace Run.PCode
variable {A : Type}

/-- Two partial codes on one type, as one. Asked: no string is written by both, and no point is
written by both. A point is written by whichever of the two writes it. -/
def join (p q : PCode A) (hs : ∀ a b s, p.put a = some s → q.put b ≠ some s)
    (hd : ∀ a s, p.put a = some s → q.put a = none) : PCode A where
  put := fun a => match p.put a with
    | some s => some s
    | none => q.put a
  parse := fun s => match p.parse s with
    | some a => some a
    | none => q.parse s
  parse_put := fun a s h => by
    cases hp : p.put a with
    | some u =>
        simp only [hp] at h
        rw [← Option.some.inj h, p.parse_put a u hp]
    | none =>
        simp only [hp] at h
        cases hq : p.parse s with
        | some b => exact absurd h (hs b a s (p.put_parse s b hq))
        | none => exact q.parse_put a s h
  put_parse := fun s a h => by
    cases hq : p.parse s with
    | some b =>
        simp only [hq] at h
        rw [← Option.some.inj h, p.put_parse s b hq]
    | none =>
        simp only [hq] at h
        have h1 := q.put_parse s a h
        cases hp : p.put a with
        | some u =>
            rw [hd a u hp] at h1
            cases h1
        | none => exact h1

/-- What the first code writes, the joined code writes. -/
theorem join_left (p q : PCode A) (hs : ∀ a b s, p.put a = some s → q.put b ≠ some s)
    (hd : ∀ a s, p.put a = some s → q.put a = none) {a : A} {s : List Bool}
    (h : p.put a = some s) : (p.join q hs hd).put a = some s := by
  show (match p.put a with
    | some s => some s
    | none => q.put a) = some s
  rw [h]

/-- What the second code writes, the joined code writes. -/
theorem join_right (p q : PCode A) (hs : ∀ a b s, p.put a = some s → q.put b ≠ some s)
    (hd : ∀ a s, p.put a = some s → q.put a = none) {a : A} {s : List Bool}
    (h : q.put a = some s) : (p.join q hs hd).put a = some s := by
  show (match p.put a with
    | some s => some s
    | none => q.put a) = some s
  cases hp : p.put a with
  | some u =>
      rw [hd a u hp] at h
      cases h
  | none => exact h

/-- What the joined code writes, one of the two writes. -/
theorem join_put (p q : PCode A) (hs : ∀ a b s, p.put a = some s → q.put b ≠ some s)
    (hd : ∀ a s, p.put a = some s → q.put a = none) (a : A) (s : List Bool)
    (h : (p.join q hs hd).put a = some s) : p.put a = some s ∨ q.put a = some s := by
  have h0 : (match p.put a with
    | some s => some s
    | none => q.put a) = some s := h
  cases hp : p.put a with
  | some u =>
      rw [hp] at h0
      exact Or.inl h0
  | none =>
      rw [hp] at h0
      exact Or.inr h0

end Run.PCode

namespace Run
open Rom Compile Compile.Batch Iop

variable {I X : Type}

/-- The data: those of Run/CodingPage.lean (`PageC`), and a partial code of the symbols of an
encoded index whose strings begin with the 16 bits of the number 174. The stored leaves take the
start of a vertex (`cfg`) and the bits of a file's salt (`saltBits`) from `PageC`'s fields. -/
structure PageCX (L : BatchProtocol I X) (K : ℕ) (t : Tag) extends PageC L K t where
  /-- the code of a stored table's symbol: label, column, fill -/
  storedP   : PCode L.Symbol
  /-- its strings begin with the 16 bits of 174 -/
  storedTag : ∀ y m, storedP.put y = some m → 16 ≤ m.length ∧ m.take 16 = t174

variable {L : BatchProtocol I X} {K : ℕ} {tg : Tag} (C : PageCX L K tg)

/-- The code of the stored tables' leaves, at the data. -/
def pStoredLeaf : PCode (LeafIn L) := pLeafS C.cfg C.saltBits C.storedP

/-- A string of a stored table's leaf: its tag, and its first byte. -/
theorem pStoredLeaf_facts (q : LeafIn L) (s : List Bool) (h : (pStoredLeaf C).put q = some s) :
    tag16 s = t174 ∧ ∀ e : UInt8, e ≠ 0 → ¬ bitsOfByte e <+: s :=
  pLeafS_facts C.cfg C.saltBits C.storedP C.storedTag q s h

/-- The code of own leaves (`pLeaf`) writes no query whose body is a symbol of an encoded index. -/
theorem pLeaf_not_stored (q : LeafIn L) (s : List Bool)
    (h : (pLeaf C.saltBits C.leafP).put q = some s) : (pStoredLeaf C).put q = none := by
  cases hq : (pStoredLeaf C).put q with
  | none => rfl
  | some u =>
      exfalso
      obtain ⟨y, m, hb, -⟩ := pLeafS_put C.cfg C.saltBits C.storedP q u hq
      have h0 : (leafSel q).bind (pSalted pre33 C.saltBits C.leafP).put = some s := h
      have h1 : leafSel (t := tg) q = none := by
        unfold leafSel
        rw [hb]
      rw [h1] at h0
      cases h0

/-- Leaf queries of both kinds: on a symbol of the protocol under the data's tag (call number
164), and on a symbol of an encoded index (call number 174). -/
def pLeaf2 : PCode (LeafIn L) :=
  (pLeaf C.saltBits C.leafP).join (pStoredLeaf C)
    (apart _ _ t164 t174 (Ne.symm t174_differs.2.2.1)
      (fun q s h => (pLeaf_facts C.toPageC q s h).1) (fun q s h => (pStoredLeaf_facts C q s h).1))
    (pLeaf_not_stored C)

/-- A string of a leaf query: its tag, and its first byte. -/
theorem pLeaf2_facts (q : LeafIn L) (s : List Bool) (h : (pLeaf2 C).put q = some s) :
    (tag16 s = t164 ∨ tag16 s = t174) ∧ ∀ e : UInt8, e ≠ 0 → ¬ bitsOfByte e <+: s := by
  rcases PCode.join_put _ _ _ _ q s h with h1 | h1
  · exact ⟨Or.inl (pLeaf_facts C.toPageC q s h1).1, (pLeaf_facts C.toPageC q s h1).2⟩
  · exact ⟨Or.inr (pStoredLeaf_facts C q s h1).1, (pStoredLeaf_facts C q s h1).2⟩

/-- The three kinds of queries side by side: leaves of both kinds, vertices, chain queries. -/
def p3X : PCode (LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1)))) :=
  (pLeaf2 C).sum
    ((pNode C.cfg).sum (pFb C.toPageC) fun a b s h1 h2 => by
      have e1 := (pNode_facts C.toPageC a s h1).1
      rcases (pFb_facts C.toPageC b s h2).1 with e2 | e2
      · exact tags_differ.2.2.1 (e2.symm.trans e1)
      · exact tags_differ.2.2.2.2.1 (e2.symm.trans e1))
    fun a b s h1 h2 => by
      rcases (pLeaf2_facts C a s h1).1 with e1 | e1
      · rcases b with b | b
        · exact tags_differ.2.2.2.2.2 (e1.symm.trans (pNode_facts C.toPageC b s h2).1)
        · rcases (pFb_facts C.toPageC b s h2).1 with e2 | e2
          · exact tags_differ.2.1 (e2.symm.trans e1)
          · exact tags_differ.2.2.2.1 (e2.symm.trans e1)
      · rcases b with b | b
        · exact t174_differs.2.2.2 (e1.symm.trans (pNode_facts C.toPageC b s h2).1)
        · rcases (pFb_facts C.toPageC b s h2).1 with e2 | e2
          · exact t174_differs.1 (e1.symm.trans e2)
          · exact t174_differs.2.1 (e1.symm.trans e2)

/-- The string's tag is one of the five. -/
def Tag5 (s : List Bool) : Prop :=
  tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t164 ∨ tag16 s = t166 ∨ tag16 s = t174

/-- A string of one of the three kinds has one of the five tags, and begins with the byte 0 or the
byte 1. -/
theorem p3X_facts (y : LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1))))
    (s : List Bool) (h : (p3X C).put y = some s) :
    Tag5 s ∧ ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s := by
  rcases y with q | q | q
  · exact ⟨(pLeaf2_facts C q s h).1.elim (fun e => Or.inr (Or.inr (Or.inl e)))
      fun e => Or.inr (Or.inr (Or.inr (Or.inr e))), fun e h0 _ => (pLeaf2_facts C q s h).2 e h0⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (pNode_facts C.toPageC q s h).1))),
      fun e h0 _ => (pNode_facts C.toPageC q s h).2 e h0⟩
  · exact ⟨(pFb_facts C.toPageC q s h).1.elim Or.inl fun e => Or.inr (Or.inl e),
      (pFb_facts C.toPageC q s h).2⟩

/-- All that the format writes, as a partial code of the real and the ghost points. -/
def pAllX : PCode (AllPts 256 K L) := (p3X C).via sel3 mk3 sel3_mk3 mk3_sel3

/-- A string that the format writes has one of the five tags, and begins with the byte 0 or the
byte 1. -/
theorem pAllX_facts (a : AllPts 256 K L) (s : List Bool) (h : (pAllX C).put a = some s) :
    Tag5 s ∧ ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s := by
  cases hy : sel3 (tg := tg) a with
  | none =>
      have h0 : (sel3 a).bind (p3X C).put = some s := h
      rw [hy] at h0
      cases h0
  | some y =>
      have h0 : (sel3 a).bind (p3X C).put = some s := h
      rw [hy] at h0
      exact p3X_facts C y s h0

/-- No string that the format writes begins with the byte 2. -/
theorem pAllX_no2 (a : AllPts 256 K L) (s : List Bool) (h : (pAllX C).put a = some s) :
    ¬ bitsOfByte 2 <+: s :=
  (pAllX_facts C a s h).2 2 (by decide) (by decide)

/-- The total code: a point that the format writes has its string of the format; every other
point the byte 2 and then its string under the data's total code `back`. -/
def totalX : StrCode (AllPts 256 K L) := (pAllX C).orElse C.back (bitsOfByte 2) (pAllX_no2 C)

/-- No string of the total code begins with the byte 3. -/
theorem totalX_esc (a : AllPts 256 K L) (t : List Bool) :
    (totalX C).put a ≠ bitsOfByte 3 ++ t := fun h =>
  PCode.orElse_not_prefix (pAllX C) C.back (bitsOfByte 2) (pAllX_no2 C) (bitsOfByte 3)
    (fun a s h => (pAllX_facts C a s h).2 3 (by decide) (by decide))
    (fun r => byte_prefix 3 2 (by decide) r) a ⟨t, h.symm⟩

/-- The family over one oracle: a bijection, with its inverse and both laws, between all points
(oracle, query, block) of the compiled scheme's oracles and all bit strings. A point of another
oracle than the spare one that the five partial codes do not write stands behind the byte 2, a spare
string that would clash behind the byte 3; every other spare string is written as itself. (By the
format page's R2.5 no hash of the format is the oracle on a string whose first byte is not 0 or 1.)
Which strings the format's calls have is not said here. No probability, nothing on any hash. -/
def theImplX : OracleCoding (spec 256 K L) 256 :=
  implA 256 K L (totalX C) (bitsOfByte 3) esc_ne (totalX_esc C)

/-- A leaf's answer is one block. -/
theorem theImplX_leaf1 : (theImplX C).blocks .leaf = 1 := rfl

/-- A vertex's answer is one block. -/
theorem theImplX_node1 : (theImplX C).blocks .node = 1 := rfl

/-- A leaf's answer is its one block, unchanged. -/
theorem theImplX_rngLeaf (f : Fin 1 → Fin 256 → Bool) : ((theImplX C).rng .leaf).symm f = f 0 := rfl

/-- A vertex's answer is its one block, unchanged. -/
theorem theImplX_rngNode (f : Fin 1 → Fin 256 → Bool) : ((theImplX C).rng .node).symm f = f 0 := rfl

/-- A chain query's answer has K + 1 blocks. -/
theorem theImplX_fbK (t : Tag) : (theImplX C).blocks (.fb t) = K + 1 := rfl

/-- The string of a leaf query that one of the two leaf codes writes is that code's string. -/
theorem theImplX_leaf (q : LeafIn L) (s : List Bool) (h : (pLeaf2 C).put q = some s) (j : Fin 1) :
    (theImplX C).code .leaf q j = s :=
  PCode.orElse_put_some (pAllX C) C.back (bitsOfByte 2) (pAllX_no2 C) (a := .inl (.inl q)) h

/-- The string of a leaf query on a symbol of the protocol, where `pLeaf` writes it. -/
theorem theImplX_own (q : LeafIn L) (s : List Bool)
    (h : (pLeaf C.saltBits C.leafP).put q = some s) (j : Fin 1) :
    (theImplX C).code .leaf q j = s :=
  theImplX_leaf C q s (PCode.join_left _ _ _ _ h) j

/-- The string of a leaf query on a symbol of an encoded index, where the fifth code writes
it. That this string is the format's is not said here. -/
theorem theImplX_stored (q : LeafIn L) (s : List Bool) (h : (pStoredLeaf C).put q = some s)
    (j : Fin 1) : (theImplX C).code .leaf q j = s :=
  theImplX_leaf C q s (PCode.join_right _ _ _ _ h) j

/-- The string of a vertex's query, where `pNode` writes it. -/
theorem theImplX_node (q : Bits × Bits) (s : List Bool)
    (h : (pNode C.cfg).put q = some s) (j : Fin 1) :
    (theImplX C).code .node q j = s :=
  PCode.orElse_put_some (pAllX C) C.back (bitsOfByte 2) (pAllX_no2 C)
    (a := .inl (.inr (.inl q))) h

/-- The string of a block of a chain query under the data's tag, where `pFb` writes it. -/
theorem theImplX_fb (q : FbIn 256 L tg) (j : Fin (K + 1))
    (s : List Bool) (h : (pFb C.toPageC).put (q, j) = some s) :
    (theImplX C).code (.fb tg) q j = s :=
  PCode.orElse_put_some (pAllX C) C.back (bitsOfByte 2) (pAllX_no2 C)
    (a := .inl (.inr (.inr (.inr (.inr (.inl ⟨tg, q, j⟩)))))) (by
      show (sel3 _).bind (p3X C).put = some s
      rw [sel3_fb]
      exact h)

/-- A string that the total code does not write, and that does not begin with the byte 3, is a
point of the spare oracle, written as itself. Among them: a string with one of the five tags that
the partial codes do not write, if it does not begin with the byte 2. -/
theorem theImplX_spare (s : List Bool) (j : Fin 1) (hp : (totalX C).parse s = none)
    (h3 : ¬ bitsOfByte 3 <+: s) : (theImplX C).code .other s j = s := by
  refine codeA_other 256 K L (totalX C) (bitsOfByte 3) esc_ne (totalX_esc C) s j
    (freeE_of 256 K L (totalX C) (bitsOfByte 3) esc_ne s hp ?_)
  cases hs : StrCode.strip (bitsOfByte 3) s with
  | none => rfl
  | some t => exact absurd ⟨t, (StrCode.strip_some hs).symm⟩ h3

/-- A string with none of the five tags, and with neither escape in front, is a point of the spare
oracle, written as itself. -/
theorem theImplX_other (s : List Bool) (j : Fin 1) (ht : ¬ Tag5 s)
    (h2 : ¬ bitsOfByte 2 <+: s) (h3 : ¬ bitsOfByte 3 <+: s) :
    (theImplX C).code .other s j = s := by
  refine theImplX_spare C s j ?_ h3
  cases hp : (totalX C).parse s with
  | none => rfl
  | some a =>
      exfalso
      have hs := (totalX C).put_parse s a hp
      cases ha : (pAllX C).put a with
      | some u =>
          have e : u = s :=
            (PCode.orElse_put_some (pAllX C) C.back (bitsOfByte 2) (pAllX_no2 C) ha).symm.trans hs
          rw [e] at ha
          exact ht (pAllX_facts C a s ha).1
      | none =>
        exact h2 ⟨_, (PCode.orElse_put_none (pAllX C) C.back (bitsOfByte 2)
          (pAllX_no2 C) ha).symm.trans hs⟩

end Run
