-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingAgreeX.lean: for every function on bit strings, the typed oracle functions written
directly from the format's calls are those that the encoding of Run/CodingPageX.lean reads out of
that function, at the queries that the encoding writes in the format.

Definitions that compute, theorems. Generic in the protocol's data and in its tag.

Why: two ways lead from a typed query to an answer. (1) A plain map sends the query (and the number
of a block of its answer) to a call of the format, or to none; the answer is the function's value at
the call's string, and zeros where there is no call. (2) The bijection `theImplX C` between typed
points and all bit strings; the answer is read block by block (`Rom.readBlocks`; `Rom.readSome`
where only marked blocks are read). Run/CodingAgree.lean ties the two for four kinds of calls, at
the format's own hash. Here the tie is stated with the fifth kind (a leaf of a stored table, call
number 174), and for every family g over the one oracle on bit strings.

Main names:
  `CallsX L K t`: the three plain maps: leaf queries, vertices, chain queries with a block.
  `famT T O`: the typed oracle functions that a function O on byte strings induces through T.
  `FitX C T` is the hypothesis that what the partial codes of C write are the bits of the strings
    of T's calls, and that at round 0 T has a call at the block of the chain value alone.
  `fitsCX C o q` is a test that can be run: the typed query is one that the encoding writes in the
    format (a chain query of round 0: at the block of the chain value; of a later round: at every
    block).
  `needCX C` says which blocks are marked: of a chain query under the data's tag those that the
    format writes, and all blocks of every other oracle.
  All that follow stand under `FitX C T` and for every g.
  `leafT_agree`, `nodeT_agree`: where the code writes the query, the two answers are one.
  `fb_block`: the same for one block of a chain query's answer.
  `fb_agree_last`, `fb_agree_all`: so the chain values are one if that block is written, and the
    whole answers are one if every block is written.
  `agreeX`: fitsCX C o q = true →
    famT T (oB (g ())) o q = readSome (theImplX C) (needCX C) g o q.

Limits: this file says nothing on soundness, and no probability; nothing on BLAKE2b or on any other
hash. Elsewhere than at the queries that pass the test nothing is said, and the two can differ. At
the K blocks of the verifier's message of round 0, and at the oracles `OracleName.rleaf`, `OracleName.rnode`,
`OracleName.g`, `OracleName.fbw` and `OracleName.fb` under another tag (Compile/Batch/Oracles.lean), `famT` answers zeros
and `Rom.readBlocks` reads g behind an escape. At the spare oracle (`OracleName.other`) `famT` answers
zeros, and `Rom.readBlocks` reads g at the string itself where that string is free
(`theImplX_spare`). The oracle `OracleName.ann` has no block. At a query that the encoding writes behind an
escape `famT` answers zeros if its map has no call there; if it has one (the hypothesis `FitX` goes
one way only), it answers g at that call's string, which can be the string of another typed point.
That a verifier asks only queries that pass the test is not said here. That `FitX` holds at a
description of a chain with stored tables, and that `Run.PQ.famX` (Run/PlanQXRun.lean) is a `famT`,
is shown in Run/PageXFit.lean.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPageX
import Run.CodingAgree
import Run.OCompM
import Run.Toy1TieTree

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch

variable {I X : Type}

/-- The three plain maps from a typed query to a call of the format, or to none. -/
structure CallsX (L : BatchProtocol I X) (K : ℕ) (t : Tag) where
  /-- the call of a leaf query -/
  leaf : LeafIn L → Option _root_.Fmt.OQ
  /-- the call of a vertex's query -/
  node : Bits × Bits → Option _root_.Fmt.OQ
  /-- the call of a chain query at a block of its answer -/
  fb   : FbIn 256 L t → Fin (K + 1) → Option _root_.Fmt.OQ

variable {L : BatchProtocol I X} {K : ℕ} {tg : Tag}

/-- The typed oracle functions that a function on byte strings induces through the plain maps.
Zeros where there is no call, and at every oracle other than leaves, vertices and the chain of the
maps' tag; but at `OracleName.ann`, whose answers have one value, that value. -/
def famT (T : CallsX L K tg) (O : ByteArray → ByteArray) : Fam (spec 256 K L)
  | .leaf, q => ansOf O (T.leaf q)
  | .node, q => ansOf O (T.node q)
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 L t) tg t' q with
      | some q => (fun k => ansOf O (T.fb q k.castSucc), ansOf O (T.fb q (Fin.last K)))
      | none => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- `famT` at a chain query under the maps' own tag. -/
theorem famT_fb_self (T : CallsX L K tg) (O : ByteArray → ByteArray) (q : FbIn 256 L tg) :
    famT T O (.fb tg) q =
      ((fun k : Fin K => ansOf O (T.fb q k.castSucc),
        ansOf O (T.fb q (Fin.last K))) : (Fin K → Dig 256) × Dig 256) := by
  simp only [famT, castTag_self]

/-- What the partial codes write are the bits of the strings of the calls; and at round 0 only
the block of the chain value has a call. -/
structure FitX (C : PageCX L K tg) (T : CallsX L K tg) : Prop where
  /-- leaf queries of both kinds -/
  leaf : ∀ q s, (pLeaf2 C).put q = some s → ∃ c, T.leaf q = some c ∧ s = bytesToBits (strOf c)
  /-- vertices -/
  node : ∀ q s, (pNode C.cfg).put q = some s → ∃ c, T.node q = some c ∧ s = bytesToBits (strOf c)
  /-- chain queries, block by block -/
  fb   : ∀ q j s, (pFb C.toPageC).put (q, j) = some s →
    ∃ c, T.fb q j = some c ∧ s = bytesToBits (strOf c)
  /-- at round 0 no block but the chain value's has a call -/
  zero : ∀ q (j : Fin (K + 1)), q.round = 0 → j.val ≠ K → T.fb q j = none

/-- The answer at a call, of the function on byte strings that a function f on bit strings induces:
f at the bits of the call's string. -/
theorem ansOf_oB (f : ZKCP.Oracle 256) (c : _root_.Fmt.OQ) :
    ansOf (oB f) (some c) = f (bytesToBits (strOf c)) :=
  TieTree.bytes_dig _

variable {C : PageCX L K tg} {T : CallsX L K tg}

/-- A leaf query of either kind that the encoding writes in the format: the answer through the
plain map is the answer read out of g. -/
theorem leafT_agree (F : FitX C T) (g : Fam (rom 256)) (q : LeafIn L)
    (h : ((pLeaf2 C).put q).isSome = true) :
    ansOf (oB (g ())) (T.leaf q) = readBlocks (theImplX C) g .leaf q := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨c, hc, e⟩ := F.leaf q s hs
  show _ = g () ((theImplX C).code .leaf q (0 : Fin 1))
  rw [theImplX_leaf C q s hs, hc, e, ansOf_oB]

/-- A vertex's query that the encoding writes in the format: the two answers are one. -/
theorem nodeT_agree (F : FitX C T) (g : Fam (rom 256)) (q : Bits × Bits)
    (h : ((pNode C.cfg).put q).isSome = true) :
    ansOf (oB (g ())) (T.node q) = readBlocks (theImplX C) g .node q := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨c, hc, e⟩ := F.node q s hs
  show _ = g () ((theImplX C).code .node q (0 : Fin 1))
  rw [theImplX_node C q s hs, hc, e, ansOf_oB]

/-- One block of a chain query's answer, where the encoding writes it in the format. -/
theorem fb_block (F : FitX C T) (g : Fam (rom 256)) (q : FbIn 256 L tg) (j : Fin (K + 1))
    (h : ((pFb C.toPageC).put (q, j)).isSome = true) :
    ansOf (oB (g ())) (T.fb q j) = g () ((theImplX C).code (.fb tg) q j) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨c, hc, e⟩ := F.fb q j s hs
  rw [theImplX_fb C q j s hs, hc, e, ansOf_oB]

/-- The chain value: if the encoding writes the block of the chain value in the format, the
chain value through the plain map is the one read out of g. -/
theorem fb_agree_last (F : FitX C T) (g : Fam (rom 256)) (q : FbIn 256 L tg)
    (h : ((pFb C.toPageC).put (q, Fin.last K)).isSome = true) :
    ansOf (oB (g ())) (T.fb q (Fin.last K)) =
      (readBlocks (theImplX C) g (.fb tg) q : (Fin K → Dig 256) × Dig 256).2 :=
  fb_block F g q (Fin.last K) h

/-- The whole answer: if the encoding writes every block in the format, the answer through the
plain map is the answer read out of g. -/
theorem fb_agree_all (F : FitX C T) (g : Fam (rom 256)) (q : FbIn 256 L tg)
    (h : ∀ j, ((pFb C.toPageC).put (q, j)).isSome = true) :
    ((fun k : Fin K => ansOf (oB (g ())) (T.fb q k.castSucc),
      ansOf (oB (g ())) (T.fb q (Fin.last K))) : (Fin K → Dig 256) × Dig 256) =
      readBlocks (theImplX C) g (.fb tg) q := by
  show _ = ((fun k : Fin K => g () ((theImplX C).code (.fb tg) q k.castSucc)),
    g () ((theImplX C).code (.fb tg) q (Fin.last K)))
  rw [fb_block F g q (Fin.last K) (h _)]
  congr 1
  funext k
  exact fb_block F g q k.castSucc (h _)

/-! ## In the form of Run/CodingAgree.lean: a test on queries, marked blocks -/

variable (C)

/-- The typed query fits: a test that can be run. A leaf of either kind, a vertex, a chain query
under the data's tag that the encoding writes in the format (round 0: at the block of the chain
value; later rounds: at every block). -/
def fitsCX : (o : Batch.OracleName) → Batch.domOf 256 L o → Bool
  | .leaf, q => ((pLeaf2 C).put q).isSome
  | .node, q => ((pNode C.cfg).put q).isSome
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 L t) tg t' q with
      | some q =>
        if q.round = 0 then (C.first.put q).isSome
        else (List.finRange (K + 1)).all fun j => ((p162 C.chain K).put (q, j)).isSome
      | none => false
  | _, _ => false

/-- Which blocks are marked: of a chain query under the data's tag those that the format writes;
all blocks of every other oracle. -/
def needCX : Need (theImplX C)
  | .fb t', q, j =>
      match castTag (F := fun t => FbIn 256 L t) tg t' q with
      | some q => ((pFb C.toPageC).put (q, (j : Fin (K + 1)))).isSome
      | none => true
  | _, _, _ => true

/-- The test at a chain query under the data's own tag. -/
theorem fitsCX_fb (q : FbIn 256 L tg) :
    fitsCX C (.fb tg) q =
      if q.round = 0 then (C.first.put q).isSome
      else (List.finRange (K + 1)).all fun j => ((p162 C.chain K).put (q, j)).isSome := by
  simp only [fitsCX, castTag_self]

/-- A chain query under another tag does not pass the test. -/
theorem fitsCX_fb_ne {t' : Tag} (h : t' ≠ tg) (q : FbIn 256 L t') :
    fitsCX C (.fb t') q = false := by
  simp only [fitsCX, castTag_ne h]

/-- The marks at a chain query under the data's own tag. -/
theorem needCX_fb (q : FbIn 256 L tg) (j : Fin (K + 1)) :
    needCX C (.fb tg) q j = ((pFb C.toPageC).put (q, j)).isSome := by
  simp only [needCX, castTag_self]

/-- A chain query that fits: the block of the chain value is written. -/
theorem fits_last (q : FbIn 256 L tg) (h : fitsCX C (.fb tg) q = true) :
    ((pFb C.toPageC).put (q, Fin.last K)).isSome = true := by
  rw [fitsCX_fb] at h
  by_cases h0 : q.round = 0
  · rw [if_pos h0] at h
    rw [pFb_zero C.toPageC q _ h0, if_pos (Fin.val_last K)]
    exact h
  · rw [if_neg h0] at h
    rw [pFb_succ C.toPageC q _ h0]
    exact List.all_eq_true.1 h _ (List.mem_finRange _)

/-- A chain query of a round other than 0 that fits: every block is written. -/
theorem fits_all (q : FbIn 256 L tg) (h : fitsCX C (.fb tg) q = true) (h0 : q.round ≠ 0)
    (j : Fin (K + 1)) : ((pFb C.toPageC).put (q, j)).isSome = true := by
  rw [fitsCX_fb, if_neg h0] at h
  rw [pFb_succ C.toPageC q _ h0]
  exact List.all_eq_true.1 h _ (List.mem_finRange _)

variable {C}

/-- One block of the answer to a chain query that fits: read out of g if it is marked, zeros if
not. -/
theorem agreeX_block (F : FitX C T) (g : Fam (rom 256)) (q : FbIn 256 L tg)
    (hq : fitsCX C (.fb tg) q = true) (j : Fin (K + 1)) :
    ansOf (oB (g ())) (T.fb q j) =
      if needCX C (.fb tg) q j = true then g () ((theImplX C).code (.fb tg) q j)
      else dig0 256 := by
  cases hp : ((pFb C.toPageC).put (q, j)).isSome with
  | true =>
      rw [if_pos (by rw [needCX_fb, hp]), fb_block F g q j hp]
  | false =>
      rw [if_neg (by rw [needCX_fb, hp]; exact Bool.false_ne_true)]
      by_cases h0 : q.round = 0
      · by_cases hj : j.val = K
        · have hl : j = Fin.last K := Fin.ext hj
          rw [hl, fits_last C q hq] at hp
          cases hp
        · rw [F.zero q j h0 hj]
          rfl
      · rw [fits_all C q hq h0 j] at hp
        cases hp

/-- On the queries that fit, the two families agree, for every g: the typed oracle functions
through the plain maps, at the function on byte strings that g induces, are those that the encoding
reads out of g when the marked blocks are read and zeros stand at the others. Of a query that does
not pass the test nothing is said. That a verifier asks only such queries is not said. Nothing on
soundness, no probability, nothing on any hash. -/
theorem agreeX (F : FitX C T) (g : Fam (rom 256)) :
    ∀ (o : Batch.OracleName) (q : Batch.domOf 256 L o), fitsCX C o q = true →
      famT T (oB (g ())) o q = readSome (theImplX C) (needCX C) g o q
  | .leaf, q, h => leafT_agree F g q h
  | .node, q, h => nodeT_agree F g q h
  | .fb t', q, h => by
      by_cases ht : t' = tg
      · subst ht
        rw [famT_fb_self]
        show _ = ((fun k : Fin K =>
              if needCX C (.fb t') q k.castSucc = true then
                g () ((theImplX C).code (.fb t') q k.castSucc)
              else dig0 256),
            if needCX C (.fb t') q (Fin.last K) = true then
              g () ((theImplX C).code (.fb t') q (Fin.last K))
            else dig0 256)
        rw [agreeX_block F g q h (Fin.last K)]
        congr 1
        funext k
        exact agreeX_block F g q h k.castSucc
      · rw [fitsCX_fb_ne C ht] at h
        cases h
  | .fbw _ _, _, h => by cases h
  | .rleaf, _, h => by cases h
  | .rnode, _, h => by cases h
  | .g _, _, h => by cases h
  | .ann, _, h => by cases h
  | .other, _, h => by cases h

end Run
