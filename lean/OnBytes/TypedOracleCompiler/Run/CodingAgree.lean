-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingAgree.lean.
In OnBytes/TypedOracleCompiler, after the widening of Run/CodingPage.lean to stored leaves: PageFit, PageFit.of,
agree, run_agree serve only pages that write no stored body: PageFit.leaf asks a leafCall (number
164) of every written string: one written string under 174 makes PageFit C D false; PageFit.of's
"fit" asks 164 of all that leafP writes, also of what leafOK then cuts off. For pages with stored
leaves: Run/PageXAgree.lean (CallsX, FitX, agreeX). The statements of agree | run_agree are
unchanged as text; fitsC, needC, theImpl changed under them. The head below is older.

Run/CodingAgree.lean: the run over a single oracle through the encoding of the queries is the run
over the typed oracle functions written directly from the format, as long as the algorithm asks only
queries that fit the plan. Definitions that compute, theorems. Generic in the protocol's data and in
its tag (a parameter of the two records; where none is written: "test"). Written against the
format page (FORMAT.md, which comes with the programs); not held against the page as it ships.
Two ways from a typed query to a hash stand in this folder. (1) Run/CodingFn.lean: famOf O D K: each
typed query is sent to its call of the format by a plain function, and what has no call is answered
by zeros. (2) Run/CodingPage.lean: theImpl C: a bijection between typed points and all bit strings,
with its inverse and both laws: what the exit to a single oracle asks for (Rom/Family.lean). Here
the two are tied.
    PageFit C D  the hypothesis: what the four partial codes of C write are the bits of the strings
        of D's calls (for leaves, nodes, rounds 1, 2, .., and round 0, whose code writes at round 0
        alone)
    PageFit.of  that hypothesis from the ties of Run/CodingPut.lean and Run/CodingPage166.lean: the
        chain's and the leaves' data fit, the two records have one start of the vertices, K > 0;
        round 0's tie stays a hypothesis (Run/CodingPage160.lean has it at its own data)
    fitsC C o q  a test that can be run: the typed query fits: a leaf, a node, a chain query under
        the data's tag that the format writes (round 0: at the block of the chain value; later
        rounds: at every block)
    needC C  which blocks are asked over the single oracle: of a chain query those that the format
        writes; all blocks of the other oracles
    agree  fitsC C o q = true → famOf Fmt.oracle D K o q = readSome (theImpl C) (needC C) oBits o q
    run_agree  if every query that c asks in its run under famOf fits, then (c.overOneN (theImpl C)
        (needC C)).det oBits = c.det (famOf Fmt.oracle D K)
So, on a given input, the run with typed oracle functions and the run over a single oracle on bit
strings have one answer as soon as the test "askedOK" (Run/DetAlong.lean) says yes there: a
computation on that input.
Why "needC" and not all blocks. The call that makes a chain's first value has one block. The typed
answer of round 0 has K more; over the single oracle these stand behind the encoding's escape. famOf
answers them by zeros; the single oracle would not. They are not asked (Rom/OverOneN.lean), and the
fixed digest that then stands for them is zeros too.
What is not said. That a verifier asks only fitting queries on every input. That its answer does not
hang on the blocks that are not asked. Anything on soundness or privacy.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingAgree
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage162
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingImpl
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
import OnBytes.TypedOracleCompiler.Run.CodingPage
import OnBytes.TypedOracleCompiler.Run.CodingPut
import Run.DetOverOne
import Run.DetAlong
import Run.OracleBits

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} {tg : Tag}

/-- What the partial codes write are the bits of the strings of the calls. -/
structure PageFit (C : PageC L K tg) (D : PageD L tg) : Prop where
  leaf  : ∀ q s, (pLeafC C).put q = some s →
    ∃ c, leafCall D q = some c ∧ s = bytesToBits (strOf c)
  node  : ∀ q s,
    (pNode C.cfg).put q = some s → ∃ c, nodeCallC D.cfg q = some c ∧ s = bytesToBits (strOf c)
  round : ∀ x s,
    (p162 C.chain K).put x = some s → ∃ c, fbCall D K x.1 x.2 = some c ∧ s = bytesToBits (strOf c)
  first : ∀ q s, C.first.put q = some s →
    q.round = 0 ∧ ∃ c, fbCall D K q (Fin.last K) = some c ∧ s = bytesToBits (strOf c)

/-- the hypothesis from the ties that are proved -/
theorem PageFit.of (C : PageC L K tg) (D : PageD L tg) (hK : 0 < K) (F : ChainFit C.chain D)
    (hc : C.cfg = D.cfg) (k : ℕ) (hn : C.saltBits = 8 * k)
    (fit : ∀ y m, C.leafP.put y = some m → ∃ z, D.leaf y = some z ∧
      m = bytesToBits (_root_.Fmt.label 164 z.1 z.2.1) ++ bytesToBits z.2.2)
    (first : ∀ q s, C.first.put q = some s →
      q.round = 0 ∧ ∃ c, fbCall D K q (Fin.last K) = some c ∧ s = bytesToBits (strOf c)) :
    PageFit C D where
  leaf := fun q s h => pLeaf_put D C.saltBits k hn C.leafP fit q s (pLeafC_put C q s h).2
  node := fun q s h => hc ▸ node_tie C.cfg q s h
  round := p162_put C.chain D K hK F
  first := first

/-- at round 0 a block other than the chain value's has no call -/
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
def fitsC : (o : TypedOracleCompiler.Compile.Batch.OracleName) → TypedOracleCompiler.Compile.Batch.domOf 256 L o → Bool
  | .leaf, q => ((pLeafC C).put q).isSome
  | .node, q => ((pNode C.cfg).put q).isSome
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 L t) tg t' q with
      | some q =>
        if q.round = 0 then (C.first.put q).isSome
        else (List.finRange (K + 1)).all fun j => ((p162 C.chain K).put (q, j)).isSome
      | none => false
  | _, _ => false

/-- Which blocks are asked over the one oracle. -/
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

/-- one block of a chain answer -/
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

/-- ON THE QUERIES THAT FIT THE TWO FAMILIES AGREE. -/
theorem agree (F : PageFit C D) :
    ∀ (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : TypedOracleCompiler.Compile.Batch.domOf 256 L o),
        fitsC C o q = true →
      famOf _root_.Fmt.oracle D K o q = readSome (theImpl C) (needC C) oBits o q
  | .leaf, q, h => by
      cases hp : (pLeafC C).put q with
      | none =>
          have h' : ((pLeafC C).put q).isSome = true := h
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

/-- THE TWO RUNS HAVE ONE ANSWER, if the run under the typed family asks only queries that fit. -/
theorem run_agree {α : Type} (F : PageFit C D) (c : OComp (typedOracleFamily 256 K L) α)
    (h : c.askedOK (famOf _root_.Fmt.oracle D K) (fitsC C) = true) :
    (c.overOneN (theImpl C) (needC C)).det oBits = c.det (famOf _root_.Fmt.oracle D K) := by
  rw [det_overOneN]
  exact (det_congr_asked _ _ (fitsC C) (agree F) c h).symm

end TypedOracleCompiler.Run
