-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageXAgree.lean: ON THE QUERIES THAT FIT, THE TYPED ORACLE FUNCTIONS THROUGH THREE
PLAIN MAPS "QUERY ↦ CALL OF THE FORMAT" ARE THOSE THAT THE ENCODING READS OUT OF THE ONE ORACLE:
WITH STORED LEAVES AMONG THE QUERIES. After OnBytes/Tie/PageXAgree.lean, with parts left out and
names changed, over the sibling's widened page (Run/CodingPage.lean: leafTag "164 or 174"; leafOK).
  AS TEXT BUT FOR NAMES (PageCX → PageC; pLeaf2 C → pLeafC C; C.toPageC → C; theImplX → theImpl;
        fitsCX | needCX → fitsC | needC) CallsX, famT, famT_fb_self, FitX, ansOf_oB, leafT_agree,
        nodeT_agree, fb_block, fb_agree_last, fb_agree_all, fits_last, fits_all, agreeX_block,
        agreeX
  NOT SAID (they ARE the sibling's own, after the widening: Run/CodingAgree.lean) fitsCX, needCX,
  fitsCX_fb, fitsCX_fb_ne, needCX_fb
  NO COUNTERPART (a leaf's body a parameter)   PCode.join and its three lemmas, PageCX's second code
                                               storedP | storedTag, pStoredLeaf, pLeaf_not_stored,
                                               pLeaf2, leafSelS | leafMkS, pLeafS
WHAT IS NOT SAID. "ELSEWHERE NOTHING IS SAID, AND THE TWO CAN DIFFER": at a query that does not fit
the family through the maps answers zeros if the query has no call; "if it has one (the hypothesis
FitX goes one way only), it answers g at that call's string, WHICH CAN BE THE STRING OF ANOTHER
TYPED POINT". No run_agreeX: agreeX is point by point, for every g, at oB (g ()). That FitX holds at
a description: Run/PageXFit.lean (pageXPd_fit); that the verifier asks only queries that fit:
Run/PageXAsked.lean. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.CodingAgree
import Run.OCompM
import OnBytes.TypedOracleCompiler.Run.Toy1TieTree

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type}

/-- The three plain maps from a typed query to a call of the format, or to none. -/
structure CallsX (L : BatchProtocolWithLeafBody I X) (K : ℕ) (t : Tag) where
  /-- the call of a leaf query -/
  leaf : LeafIn L → Option _root_.Fmt.OQ
  /-- the call of a vertex's query -/
  node : Bits × Bits → Option _root_.Fmt.OQ
  /-- the call of a chain query at a block of its answer -/
  fb   : FbIn 256 L t → Fin (K + 1) → Option _root_.Fmt.OQ

variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} {tg : Tag}

/-- The typed oracle functions that a function on byte strings induces through the plain maps.
Zeros where there is no call, and at every oracle other than leaves, vertices and the chain of the
maps' tag. -/
def famT (T : CallsX L K tg) (O : ByteArray → ByteArray) : Fam (typedOracleFamily 256 K L)
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
structure FitX (C : PageC L K tg) (T : CallsX L K tg) : Prop where
  /-- leaf queries of both kinds -/
  leaf : ∀ q s, (pLeafC C).put q = some s → ∃ c, T.leaf q = some c ∧ s = bytesToBits (strOf c)
  /-- vertices -/
  node : ∀ q s, (pNode C.cfg).put q = some s → ∃ c, T.node q = some c ∧ s = bytesToBits (strOf c)
  /-- chain queries, block by block -/
  fb   : ∀ q j s, (pFb C).put (q, j) = some s →
    ∃ c, T.fb q j = some c ∧ s = bytesToBits (strOf c)
  /-- at round 0 no block but the chain value's has a call -/
  zero : ∀ q (j : Fin (K + 1)), q.round = 0 → j.val ≠ K → T.fb q j = none

/-- The answer at a call, of the function on byte strings that a function f on bit strings induces:
f at the bits of the call's string. -/
theorem ansOf_oB (f : ZKCP.Oracle 256) (c : _root_.Fmt.OQ) :
    ansOf (oB f) (some c) = f (bytesToBits (strOf c)) :=
  TieTree.bytes_dig _

variable {C : PageC L K tg} {T : CallsX L K tg}

/-- A leaf query of either kind that the encoding writes in the format: the answer through the
plain map is the answer read out of g. -/
theorem leafT_agree (F : FitX C T) (g : Fam (rom 256)) (q : LeafIn L)
    (h : ((pLeafC C).put q).isSome = true) :
    ansOf (oB (g ())) (T.leaf q) = readBlocks (theImpl C) g .leaf q := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨c, hc, e⟩ := F.leaf q s hs
  show _ = g () ((theImpl C).code .leaf q (0 : Fin 1))
  rw [theImpl_leaf C q s hs, hc, e, ansOf_oB]

/-- A vertex's query that the encoding writes in the format: the two answers are one. -/
theorem nodeT_agree (F : FitX C T) (g : Fam (rom 256)) (q : Bits × Bits)
    (h : ((pNode C.cfg).put q).isSome = true) :
    ansOf (oB (g ())) (T.node q) = readBlocks (theImpl C) g .node q := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨c, hc, e⟩ := F.node q s hs
  show _ = g () ((theImpl C).code .node q (0 : Fin 1))
  rw [theImpl_node C q s hs, hc, e, ansOf_oB]

/-- One block of a chain query's answer, where the encoding writes it in the format. -/
theorem fb_block (F : FitX C T) (g : Fam (rom 256)) (q : FbIn 256 L tg) (j : Fin (K + 1))
    (h : ((pFb C).put (q, j)).isSome = true) :
    ansOf (oB (g ())) (T.fb q j) = g () ((theImpl C).code (.fb tg) q j) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨c, hc, e⟩ := F.fb q j s hs
  rw [theImpl_fb C q j s hs, hc, e, ansOf_oB]

/-- The chain value: if the encoding writes the block of the chain value in the format, the
chain value through the plain map is the one read out of g. -/
theorem fb_agree_last (F : FitX C T) (g : Fam (rom 256)) (q : FbIn 256 L tg)
    (h : ((pFb C).put (q, Fin.last K)).isSome = true) :
    ansOf (oB (g ())) (T.fb q (Fin.last K)) =
      (readBlocks (theImpl C) g (.fb tg) q : (Fin K → Dig 256) × Dig 256).2 :=
  fb_block F g q (Fin.last K) h

/-- The whole answer: if the encoding writes every block in the format, the answer through the
plain map is the answer read out of g. -/
theorem fb_agree_all (F : FitX C T) (g : Fam (rom 256)) (q : FbIn 256 L tg)
    (h : ∀ j, ((pFb C).put (q, j)).isSome = true) :
    ((fun k : Fin K => ansOf (oB (g ())) (T.fb q k.castSucc),
      ansOf (oB (g ())) (T.fb q (Fin.last K))) : (Fin K → Dig 256) × Dig 256) =
      readBlocks (theImpl C) g (.fb tg) q := by
  show _ = ((fun k : Fin K => g () ((theImpl C).code (.fb tg) q k.castSucc)),
    g () ((theImpl C).code (.fb tg) q (Fin.last K)))
  rw [fb_block F g q (Fin.last K) (h _)]
  congr 1
  funext k
  exact fb_block F g q k.castSucc (h _)

/-! ## The library's form: a test on queries, marked blocks -/

variable (C)

/-- A chain query that fits: the block of the chain value is written. -/
theorem fits_last (q : FbIn 256 L tg) (h : fitsC C (.fb tg) q = true) :
    ((pFb C).put (q, Fin.last K)).isSome = true := by
  rw [fitsC_fb] at h
  by_cases h0 : q.round = 0
  · rw [if_pos h0] at h
    rw [pFb_zero C q _ h0, if_pos (Fin.val_last K)]
    exact h
  · rw [if_neg h0] at h
    rw [pFb_succ C q _ h0]
    exact List.all_eq_true.1 h _ (List.mem_finRange _)

/-- A chain query of a round other than 0 that fits: every block is written. -/
theorem fits_all (q : FbIn 256 L tg) (h : fitsC C (.fb tg) q = true) (h0 : q.round ≠ 0)
    (j : Fin (K + 1)) : ((pFb C).put (q, j)).isSome = true := by
  rw [fitsC_fb, if_neg h0] at h
  rw [pFb_succ C q _ h0]
  exact List.all_eq_true.1 h _ (List.mem_finRange _)

variable {C}

/-- One block of the answer to a chain query that fits: read out of g if it is marked, zeros if
not. -/
theorem agreeX_block (F : FitX C T) (g : Fam (rom 256)) (q : FbIn 256 L tg)
    (hq : fitsC C (.fb tg) q = true) (j : Fin (K + 1)) :
    ansOf (oB (g ())) (T.fb q j) =
      if needC C (.fb tg) q j = true then g () ((theImpl C).code (.fb tg) q j)
      else dig0 256 := by
  cases hp : ((pFb C).put (q, j)).isSome with
  | true =>
      rw [if_pos (by rw [needC_fb, hp]), fb_block F g q j hp]
  | false =>
      rw [if_neg (by rw [needC_fb, hp]; exact Bool.false_ne_true)]
      by_cases h0 : q.round = 0
      · by_cases hj : j.val = K
        · have hl : j = Fin.last K := Fin.ext hj
          rw [hl, fits_last C q hq] at hp
          cases hp
        · rw [F.zero q j h0 hj]
          rfl
      · rw [fits_all C q hq h0 j] at hp
        cases hp

/-- ON THE QUERIES THAT FIT, THE TWO FAMILIES AGREE, FOR EVERY g: the typed oracle functions
through the plain maps, at the function on byte strings that g induces, are those that the encoding
reads out of g when the marked blocks are read and zeros stand at the others. Of a query that does
not pass the test nothing is said. That a verifier asks only such queries is not said. Nothing on
soundness, no probability, nothing on any hash. -/
theorem agreeX (F : FitX C T) (g : Fam (rom 256)) :
    ∀ (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : TypedOracleCompiler.Compile.Batch.domOf 256 L o),
        fitsC C o q = true →
      famT T (oB (g ())) o q = readSome (theImpl C) (needC C) g o q
  | .leaf, q, h => leafT_agree F g q h
  | .node, q, h => nodeT_agree F g q h
  | .fb t', q, h => by
      by_cases ht : t' = tg
      · subst ht
        rw [famT_fb_self]
        show _ = ((fun k : Fin K =>
              if needC C (.fb t') q k.castSucc = true then
                g () ((theImpl C).code (.fb t') q k.castSucc)
              else dig0 256),
            if needC C (.fb t') q (Fin.last K) = true then
              g () ((theImpl C).code (.fb t') q (Fin.last K))
            else dig0 256)
        rw [agreeX_block F g q h (Fin.last K)]
        congr 1
        funext k
        exact agreeX_block F g q h k.castSucc
      · rw [fitsC_fb_ne C ht] at h
        cases h
  | .fbw _ _, _, h => by cases h
  | .rleaf, _, h => by cases h
  | .rnode, _, h => by cases h
  | .g _, _, h => by cases h
  | .ann, _, h => by cases h
  | .other, _, h => by cases h

end TypedOracleCompiler.Run
