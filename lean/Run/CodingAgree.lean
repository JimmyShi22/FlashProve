-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingAgree.lean: under the hypothesis `PageFit C D`, two runs of an algorithm are the same, as
long as the algorithm asks only queries that fit the plan. The two are the run over a single oracle
through the encoding of the queries, and the run over the typed oracle functions written directly
from the format.

Definitions that compute, theorems. Generic in the protocol's data and in its tag (a parameter of
the two records; where none is written: "test"). ("test": the default `t : Tag := .test` of `PageD`,
Run/CodingFn.lean, and `PageC`, Run/CodingPage.lean.) Written against an edition of the format page
that is not the one that ships (docs/format/FORMAT.md; this file is not held against the page that
ships).
A run is the value of an algorithm with oracles under fixed oracle functions, every coin toss read
as 0 (`OComp.det`, Rom/Cache.lean).

Why: two ways from a typed query to a hash stand in this folder. (1) `famOf O D K`
(Run/CodingFn.lean): each typed query is sent to its call of the format by a plain function, and
what has no call is answered by zeros. (2) `theImpl C` (Run/CodingPage.lean): a bijection between
typed points and all bit strings, with its inverse and both laws, which is what the exit to a single
oracle asks for (Rom/Family.lean). Here the two are tied.

Main names:
  `PageFit C D` is the hypothesis that what the four partial codes of C write are the bits of the
    strings of D's calls (for leaves, nodes, rounds 1, 2, .., and round 0, whose code writes at
    round 0 alone).
  `PageFit.of` gives that hypothesis from the ties of Run/CodingPut.lean and Run/CodingPage166.lean.
    It asks: the chain's and the leaves' data fit (`F`, `fit`), the file's salt has a whole number
    of bytes (`hn`), the two records have one start of the vertices (`hc`), K > 0 (`hK`). Round 0's
    tie stays a hypothesis (`first`): Run/CodingPage160.lean's `pFirst0_put` gives the format's
    string at its own data, not the tie to `fbCall`.
  `fitsC C o q` is a test that can be run: the typed query fits. That is: it is a leaf, a node or a
    chain query under the data's tag, and the format writes it (round 0: at the block of the chain
    value; later rounds: at every block).
  `needC C` says which blocks are asked over the single oracle: of a chain query under the data's
    tag those that the format writes, and all blocks of every other query.
  `agree` (on the queries that fit the two families, `famOf` and `readSome`, agree), `run_agree`
    (the title's statement): under `PageFit C D`, at the format's oracle (`Fmt.oracle`; on bit
    strings `oBits`, Run/OracleBits.lean).
So, under `PageFit C D`, on a given input, the run with typed oracle functions and the run over a
single oracle on bit strings have one answer as soon as the test "askedOK" (Run/DetAlong.lean) says
yes there: a computation on that input.

Why `needC` and not all blocks: the call that makes a chain's first value has one block. The typed
answer of round 0 has K more; over the single oracle these stand behind the encoding's escape. famOf
answers them by zeros; the single oracle would not. They are not asked (Rom/OverOneN.lean), and the
fixed digest that then stands for them is zeros too.

Limits: this file does not say: that a verifier asks only fitting queries on every input; that its
answer does not hang on the blocks that are not asked; anything on soundness or privacy.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingPage
import Run.CodingPut
import Run.DetOverOne
import Run.DetAlong
import Run.OracleBits

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

variable {I X : Type} {L : BatchProtocol I X} {K : ℕ} {tg : Tag}

/-- What the partial codes write are the bits of the strings of the calls. -/
structure PageFit (C : PageC L K tg) (D : PageD L tg) : Prop where
  leaf  : ∀ q s, (pLeaf C.saltBits C.leafP).put q = some s →
    ∃ c, leafCall D q = some c ∧ s = bytesToBits (strOf c)
  node  : ∀ q s,
    (pNode C.cfg).put q = some s → ∃ c, nodeCallC D.cfg q = some c ∧ s = bytesToBits (strOf c)
  round : ∀ x s,
    (p162 C.chain K).put x = some s → ∃ c, fbCall D K x.1 x.2 = some c ∧ s = bytesToBits (strOf c)
  first : ∀ q s, C.first.put q = some s →
    q.round = 0 ∧ ∃ c, fbCall D K q (Fin.last K) = some c ∧ s = bytesToBits (strOf c)

theorem node_tie (cfg : ByteArray) (q : List Bool × List Bool)
    (s : List Bool) (h : (pNode cfg).put q = some s) :
    ∃ c, nodeCallC cfg q = some c ∧ s = bytesToBits (strOf c) := by
  have h' : (if q.1.length = 256 ∧ q.2.length = 256 then some (hdr 0 166 0 0 cfg ++ (q.1 ++ q.2))
        else none) = some s := h
  by_cases hq : q.1.length = 256 ∧ q.2.length = 256
  · refine ⟨_, rfl, ?_⟩
    have h2 := pNode_put cfg q.1 q.2 hq.1 hq.2
    exact Option.some.inj (h.symm.trans h2)
  · rw [if_neg hq] at h'
    cases h'

/-- The hypothesis from the ties that are proved, under `hK`, `F`, `hc`, `hn`, `fit`; round 0's tie
stays a hypothesis (`first`). -/
theorem PageFit.of (C : PageC L K tg) (D : PageD L tg) (hK : 0 < K) (F : ChainFit C.chain D)
    (hc : C.cfg = D.cfg) (k : ℕ) (hn : C.saltBits = 8 * k)
    (fit : ∀ y m, C.leafP.put y = some m →
      m = bytesToBits (_root_.Fmt.label 164 (D.leaf y).1 (D.leaf y).2.1) ++
          bytesToBits (D.leaf y).2.2)
    (first : ∀ q s, C.first.put q = some s →
      q.round = 0 ∧ ∃ c, fbCall D K q (Fin.last K) = some c ∧ s = bytesToBits (strOf c)) :
    PageFit C D where
  leaf := pLeaf_put D C.saltBits k hn C.leafP fit
  node := fun q s h => hc ▸ node_tie C.cfg q s h
  round := p162_put C.chain D K hK F
  first := first

/-- The single oracle on bits at the bits of a call's string is the format's oracle at that string,
if the string does not begin with the byte 4 (`h4`). -/
theorem oBits_call (c : _root_.Fmt.OQ) (h4 : ¬ bitsOfByte 4 <+: bytesToBits (strOf c)) :
    oBits () (bytesToBits (strOf c)) = bytesToDig (_root_.Fmt.oracle (strOf c)) := by
  refine oBits_bytes _ ?_
  unfold plainB
  rw [whole_bytesToBits, Bool.true_and, Bool.not_eq_true', beq_eq_false_iff_ne]
  intro h8
  exact h4 (h8 ▸ List.take_prefix 8 _)

/-- At round 0 a block other than the chain value's has no call. -/
theorem fbCall_zero (D : PageD L tg) (q : FbIn 256 L tg) (j : Fin (K + 1))
    (h0 : q.round = 0) (hj : j.val ≠ K) : fbCall D K q j = none := by
  obtain ⟨round, head, rt, plain⟩ := q
  have h0' : round = 0 := h0
  subst h0'
  cases head with
  | f1 cms x salt =>
      cases cms with
      | nil => rfl
      | cons pd tl =>
          cases tl with
          | nil => exact if_neg hj
          | cons _ _ => rfl
  | f2 _ _ => rfl
  | f3 _ _ => rfl
  | f4 _ _ => rfl
  | f5 _ => rfl

variable (C : PageC L K tg)

theorem pFb_zero (q : FbIn 256 L tg) (j : Fin (K + 1)) (h0 : q.round = 0) :
    (pFb C).put (q, j) = if j.val = K then C.first.put q else none := by
  show (selR (q, j)).bind (pFb2 C).put = _
  unfold selR
  rw [if_pos h0]
  show (selK (q, j)).bind C.first.put = _
  unfold selK
  by_cases hj : j.val = K
  · rw [if_pos hj, if_pos hj]
    rfl
  · rw [if_neg hj, if_neg hj]
    rfl

theorem pFb_succ (q : FbIn 256 L tg) (j : Fin (K + 1)) (h0 : q.round ≠ 0) :
    (pFb C).put (q, j) = (p162 C.chain K).put (q, j) := by
  show (selR (q, j)).bind (pFb2 C).put = _
  unfold selR
  rw [if_neg h0]
  rfl

/-- The typed query fits: a test that can be run. -/
def fitsC : (o : Batch.OracleName) → Batch.domOf 256 L o → Bool
  | .leaf, q => ((pLeaf C.saltBits C.leafP).put q).isSome
  | .node, q => ((pNode C.cfg).put q).isSome
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 L t) tg t' q with
      | some q =>
        if q.round = 0 then (C.first.put q).isSome
        else (List.finRange (K + 1)).all fun j => ((p162 C.chain K).put (q, j)).isSome
      | none => false
  | _, _ => false

/-- Which blocks are asked over the single oracle. -/
def needC : Need (theImpl C)
  | .fb t', q, j =>
      match castTag (F := fun t => FbIn 256 L t) tg t' q with
      | some q => ((pFb C).put (q, (j : Fin (K + 1)))).isSome
      | none => true
  | _, _, _ => true

theorem fitsC_fb (q : FbIn 256 L tg) :
    fitsC C (.fb tg) q =
      if q.round = 0 then (C.first.put q).isSome
      else (List.finRange (K + 1)).all fun j => ((p162 C.chain K).put (q, j)).isSome := by
  simp only [fitsC, castTag_self]

theorem fitsC_fb_ne {t' : Tag} (h : t' ≠ tg) (q : FbIn 256 L t') : fitsC C (.fb t') q = false := by
  simp only [fitsC, castTag_ne h]

theorem needC_fb (q : FbIn 256 L tg) (j : Fin (K + 1)) :
    needC C (.fb tg) q j = ((pFb C).put (q, j)).isSome := by
  simp only [needC, castTag_self]

variable {C} {D : PageD L tg}

/-- One block of a chain answer, under `F` and for a query that fits (`hq`). -/
theorem agree_block (F : PageFit C D) (q : FbIn 256 L tg)
    (hq : fitsC C (.fb tg) q = true) (j : Fin (K + 1)) :
    ansOf _root_.Fmt.oracle (fbCall D K q j) =
      if needC C (.fb tg) q j = true then oBits () ((theImpl C).code (.fb tg) q j)
      else dig0 256 := by
  have hq' : (if q.round = 0 then (C.first.put q).isSome
        else (List.finRange (K + 1)).all fun j => ((p162 C.chain K).put (q, j)).isSome) = true :=
    (fitsC_fb C q).symm.trans hq
  cases hp : (pFb C).put (q, j) with
  | some s =>
      have hn : needC C (.fb tg) q j = true := by
        rw [needC_fb, hp]
        rfl
      rw [if_pos hn, theImpl_fb C q j s hp]
      have h4 : ¬ bitsOfByte 4 <+: s := (pFb_facts C (q, j) s hp).2 4 (by decide) (by decide)
      have tie : ∃ c, fbCall D K q j = some c ∧ s = bytesToBits (strOf c) := by
        by_cases h0 : q.round = 0
        · rw [pFb_zero C q j h0] at hp
          by_cases hj : j.val = K
          · rw [if_pos hj] at hp
            have hl : j = Fin.last K := Fin.ext hj
            rw [hl]
            exact (F.first q s hp).2
          · rw [if_neg hj] at hp
            cases hp
        · rw [pFb_succ C q j h0] at hp
          exact F.round (q, j) s hp
      obtain ⟨c, hc, rfl⟩ := tie
      rw [hc, oBits_call c h4]
      rfl
  | none =>
      have hn : ¬ needC C (.fb tg) q j = true := by
        rw [needC_fb, hp]
        exact Bool.false_ne_true
      rw [if_neg hn]
      by_cases h0 : q.round = 0
      · rw [pFb_zero C q j h0] at hp
        rw [if_pos h0] at hq'
        by_cases hj : j.val = K
        · rw [if_pos hj] at hp
          rw [hp] at hq'
          cases hq'
        · rw [fbCall_zero D q j h0 hj]
          rfl
      · rw [pFb_succ C q j h0] at hp
        rw [if_neg h0] at hq'
        have := List.all_eq_true.1 hq' j (List.mem_finRange j)
        rw [hp] at this
        cases this

/-- Under `PageFit C D` (`F`), on the queries that fit the two families agree. -/
theorem agree (F : PageFit C D) :
    ∀ (o : Batch.OracleName) (q : Batch.domOf 256 L o), fitsC C o q = true →
      famOf _root_.Fmt.oracle D K o q = readSome (theImpl C) (needC C) oBits o q
  | .leaf, q, h => by
      cases hp : (pLeaf C.saltBits C.leafP).put q with
      | none =>
          have h' : ((pLeaf C.saltBits C.leafP).put q).isSome = true := h
          rw [hp] at h'
          cases h'
      | some s =>
          obtain ⟨c, hc, hs⟩ := F.leaf q s hp
          have h4 : ¬ bitsOfByte 4 <+: s := (pLeaf_facts C q s hp).2 4 (by decide)
          show ansOf _root_.Fmt.oracle (leafCall D q) =
            oBits () ((theImpl C).code .leaf q (0 : Fin 1))
          rw [theImpl_leaf C q s hp, hc, hs, oBits_call c (hs ▸ h4)]
          rfl
  | .node, q, h => by
      cases hp : (pNode C.cfg).put q with
      | none =>
          have h' : ((pNode C.cfg).put q).isSome = true := h
          rw [hp] at h'
          cases h'
      | some s =>
          obtain ⟨c, hc, hs⟩ := F.node q s hp
          have h4 : ¬ bitsOfByte 4 <+: s := (pNode_facts C q s hp).2 4 (by decide)
          show ansOf _root_.Fmt.oracle (nodeCallC D.cfg q) =
            oBits () ((theImpl C).code .node q (0 : Fin 1))
          rw [theImpl_node C q s hp, hc, hs, oBits_call c (hs ▸ h4)]
          rfl
  | .fb t', q, h => by
      by_cases ht : t' = tg
      · subst ht
        rw [famOf_fb_self]
        show ((fun k : Fin K => ansOf _root_.Fmt.oracle (fbCall D K q k.castSucc)),
            ansOf _root_.Fmt.oracle (fbCall D K q (Fin.last K))) =
          ((fun k : Fin K =>
              if needC C (.fb t') q k.castSucc = true then
                oBits () ((theImpl C).code (.fb t') q k.castSucc)
              else dig0 256),
            if needC C (.fb t') q (Fin.last K) = true then
              oBits () ((theImpl C).code (.fb t') q (Fin.last K))
            else dig0 256)
        rw [agree_block F q h (Fin.last K)]
        congr 1
        funext k
        exact agree_block F q h k.castSucc
      · rw [fitsC_fb_ne C ht] at h
        cases h
  | .fbw _ _, _, h => by cases h
  | .rleaf, _, h => by cases h
  | .rnode, _, h => by cases h
  | .g _, _, h => by cases h
  | .ann, _, h => by cases h
  | .other, _, h => by cases h

/-- Under `PageFit C D` (`F`), the two runs have one answer, if the run under the typed family asks
only queries that fit (`h`). -/
theorem run_agree {α : Type} (F : PageFit C D) (c : OComp (spec 256 K L) α)
    (h : c.askedOK (famOf _root_.Fmt.oracle D K) (fitsC C) = true) :
    (c.overOneN (theImpl C) (needC C)).det oBits = c.det (famOf _root_.Fmt.oracle D K) := by
  rw [det_overOneN]
  exact (det_congr_asked _ _ (fitsC C) (agree F) c h).symm

end Run
