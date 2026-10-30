-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingPage.lean.
In OnBytes/TypedOracleCompiler the page is widened to stored leaves. In the head below, where it says "the 16
bits of the leaves' number" read "of 164 or of 174"; where "none of the four tags", "none of the
five" (Tag5).

Run/CodingPage.lean: the encoding of the typed queries of the compiled scheme into the single
oracle's strings by the rules of the programs' format: the assembly. Definitions that compute, with
their laws; the family over a single oracle (Rom.OracleCoding) with its inverse and both laws. After the
format page, not held against the page as it ships: the chain's label stands in a round's call; a
vertex starts from a constant of the instance; rule
R2.5 (strings whose first byte is not 0 or 1 are left to the formal side) gives the two escapes.
The data (PageC L K t; the protocol's tag t is a parameter; where none is written it is "test").
   cfg  the start of a vertex: a constant of the instance, 32 bytes
   chain  the chain's label, the plan's kinds and work, and the code of each round's message
       (Run/CodingPage162.lean: ChainD); asked: the word with the label has the rounds' number in
       its low 16 bits
   first  a partial code of the chain query of round 0, whose string is the call for the chain's
       first value; asked of it: its strings have the tag of that call and begin with the byte 0
   saltBits, leafP  the bits of a file's salt; a partial code of the symbols with their positions
       that writes label, column, fill; asked: its strings begin with the 16 bits of the leaves'
       number
   back  any total code of the real and the ghost points: it writes, behind an escape, all points
       that the format does not write
What is built.
   pFb C  chain queries with a block: round 0 at the block of the chain value alone (first); rounds
       1, 2, .. (p162)
   pAll C  leaf queries, node queries, chain queries under the data's tag, as a partial code of all
       real and ghost points
   total C : StrCode (AllPts 256 K L)  a point that the format writes: its string of the format;
       every other point: the byte 2 and then its string under "back"
   theImpl C : OracleCoding (typedOracleFamily 256 K L) 256  Run/CodingImpl.lean: implA at "total", with the byte 3 as
       the escape of the spare strings
   theImpl_leaf, theImpl_node, theImpl_fb  the string of a typed query that the format writes is the
       partial codes' string
   theImpl_other  a bit string that begins with neither escape and has none of the four tags is
       written as itself as a point of the spare oracle: so the calls of the hash that the
       verifier's typed queries do not make (the digests of parameters, a run's value) are queries
       to the spare oracle at the format's own strings
What is not said. The data at a protocol. That the strings are those of the functions of
Run/CodingFn.lean is not shown in this file: for a node: Run/CodingPage166.lean (pNode_put); round
0: Run/CodingPage160.lean (pFirst0_put); later rounds and leaves: Run/CodingPut.lean; together, and
that the typed oracle functions agree with what this encoding reads out of the single oracle:
Run/CodingAgree.lean. No bound is asked of the chain's label (Run/CodingPage162.lean's head).
Nothing on a hash.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPage
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage162
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
import OnBytes.TypedOracleCompiler.Run.Tag174
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingImpl
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import OnBytes.TypedOracleCompiler.Run.CodingTag
import OnBytes.TypedOracleCompiler.Run.CodingFn

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type}

/-- The data. -/
structure PageC (L : BatchProtocolWithLeafBody I X) (K : ℕ) (t : Tag := .test) where
  cfg      : ByteArray
  hcfg     : cfg.size = 32
  chain    : ChainD L t
  chainTag : (bytesToBits (_root_.Fmt.u64n (162 + 65536 * chain.label))).take 16 = t162
  first    : PCode (FbIn 256 L t)
  firstTag : ∀ q s, first.put q = some s → tag16 s = t160
  firstHd  : ∀ q s, first.put q = some s → ∀ e : UInt8, e ≠ 0 → ¬ bitsOfByte e <+: s
  saltBits : ℕ
  /-- TWO: the code of a leaf's body (in the library: of a symbol with its position, under the tag
  t) -/
  leafP    : PCode L.Bd
  /-- Widened in OnBytes/TypedOracleCompiler (stored leaves): the leaves' number 164 or the stored leaves' number
  174 (the library: 164 alone; PageCX: a second code storedP under 174, joined) -/
  leafTag  : ∀ y m, leafP.put y = some m → 16 ≤ m.length ∧ (m.take 16 = t164 ∨ m.take 16 = t174)
  /-- Widened in OnBytes/TypedOracleCompiler: a test on body and salt together: which leaf queries the page writes
  at all (a stored leaf's start, the first 256 bits of the typed salt, must be cfg: startIs).
  A trap: it is one test for all bodies: at an own leaf (164) it must be true whatever the salt's
  first 256 bits are (the start there is the run's value): so it must look at the body: "stored →
  the start is cfg; else true". Nothing in this structure ties the tag to the test: at the default a
  page may write 174 under any start: lawful, one-to-one, and no page of the format. What PageCX's
  join of two codes proved (no common string, no common point) is a duty of whoever gives leafP:
  it lies in "leafP is a PCode". -/
  leafOK   : LeafIn L → Bool := fun _ => true
  back     : StrCode (AllPts 256 K L)

variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} {tg : Tag} (C : PageC L K tg)

/-- a chain query with the block of the chain value -/
def selK (x : FbIn 256 L tg × Fin (K + 1)) : Option (FbIn 256 L tg) :=
  if x.2.val = K then some x.1 else none

def mkK (q : FbIn 256 L tg) : Option (FbIn 256 L tg × Fin (K + 1)) := some (q, Fin.last K)

theorem mkK_selK (x : FbIn 256 L tg × Fin (K + 1)) (q : FbIn 256 L tg) (h : selK x = some q) :
    mkK q = some x := by
  unfold selK at h
  unfold mkK
  by_cases hx : x.2.val = K
  · rw [if_pos hx] at h
    rw [← Option.some.inj h]
    exact congrArg some (Prod.ext rfl (Fin.ext hx.symm))
  · rw [if_neg hx] at h
    cases h

theorem selK_mkK (q : FbIn 256 L tg) (x : FbIn 256 L tg × Fin (K + 1)) (h : mkK q = some x) :
    selK x = some q := by
  unfold mkK at h
  rw [← Option.some.inj h]
  exact if_pos rfl

/-- round 0: the block of the chain value alone -/
def pFirstJ : PCode (FbIn 256 L tg × Fin (K + 1)) := C.first.pull selK mkK mkK_selK selK_mkK

theorem pFirstJ_put (x : FbIn 256 L tg × Fin (K + 1))
    (s : List Bool) (h : (pFirstJ C).put x = some s) : C.first.put x.1 = some s := by
  obtain ⟨q, hq, hs⟩ := PCode.pull_put _ _ _ _ _ x s h
  unfold selK at hq
  by_cases hx : x.2.val = K
  · rw [if_pos hx] at hq
    rw [Option.some.inj hq]
    exact hs
  · rw [if_neg hx] at hq
    cases hq

/-- the two codes of chain queries, side by side -/
def pFb2 : PCode ((FbIn 256 L tg × Fin (K + 1)) ⊕ (FbIn 256 L tg × Fin (K + 1))) :=
  (pFirstJ C).sum (p162 C.chain K)
    (apart _ _ t160 t162 tags_differ.1 (fun x s h => C.firstTag _ s (pFirstJ_put C x s h))
      (p162_tag C.chain C.chainTag K))

/-- by the round: 0, or later -/
def selR (x : FbIn 256 L tg × Fin (K + 1)) :
    Option ((FbIn 256 L tg × Fin (K + 1)) ⊕ (FbIn 256 L tg × Fin (K + 1))) :=
  if x.1.round = 0 then some (.inl x) else some (.inr x)

def mkR :
    (FbIn 256 L tg × Fin (K + 1)) ⊕ (FbIn 256 L tg × Fin (K + 1)) →
    Option (FbIn 256 L tg × Fin (K + 1))
  | .inl x => if x.1.round = 0 then some x else none
  | .inr x => if x.1.round = 0 then none else some x

theorem mkR_selR (x : FbIn 256 L tg × Fin (K + 1))
    (y : (FbIn 256 L tg × Fin (K + 1)) ⊕ (FbIn 256 L tg × Fin (K + 1))) (h : selR x = some y) :
    mkR y = some x := by
  unfold selR at h
  by_cases hx : x.1.round = 0
  · rw [if_pos hx] at h
    rw [← Option.some.inj h]
    exact if_pos hx
  · rw [if_neg hx] at h
    rw [← Option.some.inj h]
    exact if_neg hx

theorem selR_mkR (y : (FbIn 256 L tg × Fin (K + 1)) ⊕ (FbIn 256 L tg × Fin (K + 1)))
    (x : FbIn 256 L tg × Fin (K + 1)) (h : mkR y = some x) : selR x = some y := by
  rcases y with y | y
  · have h0 : (if y.1.round = 0 then some y else none) = some x := h
    by_cases hy : y.1.round = 0
    · rw [if_pos hy] at h0
      rw [← Option.some.inj h0]
      exact if_pos hy
    · rw [if_neg hy] at h0
      cases h0
  · have h0 : (if y.1.round = 0 then none else some y) = some x := h
    by_cases hy : y.1.round = 0
    · rw [if_pos hy] at h0
      cases h0
    · rw [if_neg hy] at h0
      rw [← Option.some.inj h0]
      exact if_neg hy

/-- Chain queries with a block. -/
def pFb : PCode (FbIn 256 L tg × Fin (K + 1)) := (pFb2 C).pull selR mkR mkR_selR selR_mkR

/-- a string of a chain query: its tag, and its first byte -/
theorem pFb_facts (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool) (h : (pFb C).put x = some s) :
    (tag16 s = t160 ∨ tag16 s = t162) ∧ ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s := by
  obtain ⟨y, -, hy⟩ := PCode.pull_put _ _ _ _ _ x s h
  rcases y with y | y
  · have h1 : (pFirstJ C).put y = some s := hy
    exact ⟨Or.inl (C.firstTag _ s (pFirstJ_put C y s h1)),
      fun e h0 _ => C.firstHd _ s (pFirstJ_put C y s h1) e h0⟩
  · have h1 : (p162 C.chain K).put y = some s := hy
    exact ⟨Or.inr (p162_tag C.chain C.chainTag K y s h1),
      fun e h0 h1' => p162_head C.chain K y s h1 e h0 h1'⟩

/-- TWO, WIDENED: the page's code of leaf queries: of both kinds, under the page's test -/
def pLeafC : PCode (LeafIn L) := (pLeaf C.saltBits C.leafP).sub C.leafOK

theorem pLeafC_put (q : LeafIn L) (s : List Bool) (h : (pLeafC C).put q = some s) :
    C.leafOK q = true ∧ (pLeaf C.saltBits C.leafP).put q = some s := by
  have h0 : (if C.leafOK q = true then (pLeaf C.saltBits C.leafP).put q else none) = some s := h
  by_cases hk : C.leafOK q = true
  · rw [if_pos hk] at h0
    exact ⟨hk, h0⟩
  · rw [if_neg hk] at h0
    cases h0

theorem pLeaf_facts (q : LeafIn L) (s : List Bool) (h' : (pLeafC C).put q = some s) :
    (tag16 s = t164 ∨ tag16 s = t174) ∧ ∀ e : UInt8, e ≠ 0 → ¬ bitsOfByte e <+: s := by
  have h := (pLeafC_put C q s h').2
  cases hq : leafSel q with
  | none =>
      have h0 : (leafSel q).bind (pSalted pre33 C.saltBits C.leafP).put = some s := h
      rw [hq] at h0
      cases h0
  | some x =>
      have h0 : (leafSel q).bind (pSalted pre33 C.saltBits C.leafP).put = some s := h
      rw [hq] at h0
      obtain ⟨st, m, r, hst, hm, rfl⟩ := pSalted_shape pre33 C.saltBits C.leafP x s h0
      exact ⟨(C.leafTag _ m hm).2.imp (tag16_pre33 st m r hst (C.leafTag _ m hm).1).trans
          (tag16_pre33 st m r hst (C.leafTag _ m hm).1).trans,
        fun e he => pre33_not_prefix e he _⟩

theorem pNode_facts (q : List Bool × List Bool) (s : List Bool) (h : (pNode C.cfg).put q = some s) :
    tag16 s = t166 ∧ ∀ e : UInt8, e ≠ 0 → ¬ bitsOfByte e <+: s := by
  refine ⟨pNode_tag C.cfg C.hcfg q s h, fun e he => ?_⟩
  obtain ⟨x, rfl⟩ := pNode_hdr C.cfg q s h
  exact hdr_not_prefix e 0 he 166 0 0 C.cfg x

/-- the three kinds side by side -/
def p3 : PCode (LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1)))) :=
  (pLeafC C).sum
    ((pNode C.cfg).sum (pFb C) fun a b s h1 h2 => by
      have e1 := (pNode_facts C a s h1).1
      rcases (pFb_facts C b s h2).1 with e2 | e2
      · exact tags_differ.2.2.1 (e2.symm.trans e1)
      · exact tags_differ.2.2.2.2.1 (e2.symm.trans e1))
    fun a b s h1 h2 => by
      rcases (pLeaf_facts C a s h1).1 with e1 | e1
      · rcases b with b | b
        · exact tags_differ.2.2.2.2.2 (e1.symm.trans (pNode_facts C b s h2).1)
        · rcases (pFb_facts C b s h2).1 with e2 | e2
          · exact tags_differ.2.1 (e2.symm.trans e1)
          · exact tags_differ.2.2.2.1 (e2.symm.trans e1)
      · rcases b with b | b
        · exact t174_differs.2.2.2 (e1.symm.trans (pNode_facts C b s h2).1)
        · rcases (pFb_facts C b s h2).1 with e2 | e2
          · exact t174_differs.1 (e1.symm.trans e2)
          · exact t174_differs.2.1 (e1.symm.trans e2)

/-- Widened in OnBytes/TypedOracleCompiler: one of the five tags -/
def Tag5 (s : List Bool) : Prop :=
  tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t164 ∨ tag16 s = t166 ∨ tag16 s = t174

theorem p3_facts (y : LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1))))
    (s : List Bool) (h : (p3 C).put y = some s) :
    Tag5 s ∧
    ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s := by
  rcases y with q | q | q
  · exact ⟨(pLeaf_facts C q s h).1.elim (fun e => Or.inr (Or.inr (Or.inl e)))
        (fun e => Or.inr (Or.inr (Or.inr (Or.inr e)))),
      fun e h0 _ => (pLeaf_facts C q s h).2 e h0⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (pNode_facts C q s h).1))),
      fun e h0 _ => (pNode_facts C q s h).2 e h0⟩
  · exact ⟨(pFb_facts C q s h).1.elim Or.inl fun e => Or.inr (Or.inl e), (pFb_facts C q s h).2⟩

/-- which points the format may write -/
def sel3 :
    AllPts 256 K L → Option (LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1))))
  | .inl (.inl q) => some (.inl q)
  | .inl (.inr (.inl q)) => some (.inr (.inl q))
  | .inl (.inr (.inr (.inr (.inr (.inl ⟨t', q, j⟩))))) =>
    (castTag (F := fun t => FbIn 256 L t) tg t' q).map fun q => .inr (.inr (q, j))
  | _ => none

def mk3 : LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1))) → AllPts 256 K L
  | .inl q => .inl (.inl q)
  | .inr (.inl q) => .inl (.inr (.inl q))
  | .inr (.inr x) => .inl (.inr (.inr (.inr (.inr (.inl ⟨tg, x.1, x.2⟩)))))

theorem sel3_fb (q : FbIn 256 L tg) (j : Fin (K + 1)) :
    sel3 (K := K) (.inl (.inr (.inr (.inr (.inr (.inl ⟨tg, q, j⟩)))))) =
      some (.inr (.inr (q, j))) := by
  show (castTag (F := fun t => FbIn 256 L t) tg tg q).map (fun q => Sum.inr (Sum.inr (q, j))) = _
  rw [castTag_self]
  rfl

theorem sel3_mk3 (y : LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1)))) :
    sel3 (mk3 y) = some y := by
  rcases y with q | q | ⟨q, j⟩
  · rfl
  · rfl
  · exact sel3_fb q j

theorem mk3_sel3 (b : AllPts 256 K L)
    (y : LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1))))
    (h : sel3 b = some y) : mk3 y = b := by
  rcases b with ((q | (q | (q | (q | (⟨t, q, j⟩ | q))))) | q)
  · rw [← Option.some.inj h]; rfl
  · rw [← Option.some.inj h]; rfl
  · cases h
  · cases h
  · have h0 : (castTag (F := fun t => FbIn 256 L t) tg t q).map
          (fun q => Sum.inr (Sum.inr (q, j))) = some y := h
    by_cases ht : t = tg
    · subst ht
      rw [castTag_self] at h0
      rw [← Option.some.inj h0]
      rfl
    · rw [castTag_ne ht] at h0
      cases h0
  · cases h
  · cases h

/-- All that the format writes, as a partial code of the real and the ghost points. -/
def pAll : PCode (AllPts 256 K L) := (p3 C).via sel3 mk3 sel3_mk3 mk3_sel3

theorem pAll_facts (a : AllPts 256 K L) (s : List Bool) (h : (pAll C).put a = some s) :
    Tag5 s ∧
    ∀ e : UInt8, e ≠ 0 → e ≠ 1 → ¬ bitsOfByte e <+: s := by
  cases hy : sel3 (tg := tg) a with
  | none =>
      have h0 : (sel3 a).bind (p3 C).put = some s := h
      rw [hy] at h0
      cases h0
  | some y =>
      have h0 : (sel3 a).bind (p3 C).put = some s := h
      rw [hy] at h0
      exact p3_facts C y s h0

theorem pAll_no2 (a : AllPts 256 K L) (s : List Bool) (h : (pAll C).put a = some s) :
    ¬ bitsOfByte 2 <+: s :=
  (pAll_facts C a s h).2 2 (by decide) (by decide)

/-- The total code. -/
def total : StrCode (AllPts 256 K L) := (pAll C).orElse C.back (bitsOfByte 2) (pAll_no2 C)

theorem total_esc (a : AllPts 256 K L) (t : List Bool) :
    (total C).put a ≠ bitsOfByte 3 ++ t := fun h =>
  PCode.orElse_not_prefix (pAll C) C.back (bitsOfByte 2) (pAll_no2 C) (bitsOfByte 3)
    (fun a s h => (pAll_facts C a s h).2 3 (by decide) (by decide))
    (fun r => byte_prefix 3 2 (by decide) r) a ⟨t, h.symm⟩

/-- THE FAMILY OVER ONE ORACLE. -/
def theImpl : OracleCoding (typedOracleFamily 256 K L) 256 := implA 256 K L (total C) (bitsOfByte 3) esc_ne (total_esc C)

theorem theImpl_leaf (q : LeafIn L) (s : List Bool)
    (h : (pLeafC C).put q = some s) (j : Fin 1) :
    (theImpl C).code .leaf q j = s :=
  PCode.orElse_put_some (pAll C) C.back (bitsOfByte 2) (pAll_no2 C) (a := .inl (.inl q)) h

theorem theImpl_node (q : Bits × Bits) (s : List Bool)
    (h : (pNode C.cfg).put q = some s) (j : Fin 1) :
    (theImpl C).code .node q j = s :=
  PCode.orElse_put_some (pAll C) C.back (bitsOfByte 2) (pAll_no2 C) (a := .inl (.inr (.inl q))) h

theorem theImpl_fb (q : FbIn 256 L tg) (j : Fin (K + 1))
    (s : List Bool) (h : (pFb C).put (q, j) = some s) :
    (theImpl C).code (.fb tg) q j = s :=
  PCode.orElse_put_some (pAll C) C.back (bitsOfByte 2) (pAll_no2 C)
      (a := .inl (.inr (.inr (.inr (.inr (.inl ⟨tg, q, j⟩)))))) (by
    show (sel3 _).bind (p3 C).put = some s
    rw [sel3_fb]
    exact h)

/-- A string with another tag, and with neither escape in front, is a point of the spare oracle,
written as itself. -/
theorem theImpl_other (s : List Bool) (j : Fin 1) (h160 : tag16 s ≠ t160)
    (h162 : tag16 s ≠ t162) (h164 : tag16 s ≠ t164) (h166 : tag16 s ≠ t166) (h174 : tag16 s ≠ t174)
    (h2 : ¬ bitsOfByte 2 <+: s) (h3 : ¬ bitsOfByte 3 <+: s) :
    (theImpl C).code .other s j = s := by
  refine codeA_other 256 K L (total C) (bitsOfByte 3) esc_ne (total_esc C) s j
    (freeE_of 256 K L (total C) (bitsOfByte 3) esc_ne s ?_ ?_)
  · cases hp : (total C).parse s with
    | none => rfl
    | some a =>
        exfalso
        have hs := (total C).put_parse s a hp
        cases ha : (pAll C).put a with
        | some u =>
            have e : u = s :=
              (PCode.orElse_put_some (pAll C) C.back (bitsOfByte 2) (pAll_no2 C) ha).symm.trans hs
            rw [e] at ha
            rcases (pAll_facts C a s ha).1 with t | t | t | t | t
            · exact h160 t
            · exact h162 t
            · exact h164 t
            · exact h166 t
            · exact h174 t
        | none =>
          exact h2 ⟨_,
              (PCode.orElse_put_none (pAll C) C.back (bitsOfByte 2) (pAll_no2 C) ha).symm.trans hs⟩
  · cases hs : StrCode.strip (bitsOfByte 3) s with
    | none => rfl
    | some t => exact absurd ⟨t, (StrCode.strip_some hs).symm⟩ h3

end TypedOracleCompiler.Run
