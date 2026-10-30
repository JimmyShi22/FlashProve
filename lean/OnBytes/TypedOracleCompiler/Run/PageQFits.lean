-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageQFits.lean.
TWO: CUT BY PROGRAM out of the library's Run/PageQFits.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), then turned by hand where it had to be. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
pMsgO_some, toRoots_isSome, okRound, pRound_some, okL, rcL_some, fitsQ, fitsQ_put.

Run/PageQFits.lean: A TEST, WHICH WRITES NO STRING, THAT A CHAIN QUERY OF A ROUND 1, 2, .. IS ONE
THAT THE ENCODING OF THE QUERIES OF Run/PageQ.lean WRITES IN THE PROGRAMS' FORMAT, AT EVERY BLOCK;
WITH ITS LAW. Definitions that compute; theorems.
WHY. At a long message (tens of thousands of bytes) the encoding's string of each block of a chain
answer is long, and there are many blocks. A faster family may answer such a query from the format's
hash directly; its tie to the family read out of the single oracle holds at the queries that the
encoding writes. To choose the fast form one must know that WITHOUT writing the strings.
   okRound w l rt p     "root or none" fits the items;  the nonce is below 2^64
   okL C ds i rt q      the plain part is the slot part of the round with the number i, and okRound
                        there
   fitsQ Bd S C dec K q      a round i + 1; the later-round head with no late field and a chain
                             value of 256 bits; round, kind, work, the blocks' calls within their
                             words' bounds; okL. Parameters: the description, the choice of
                             challenge types, the decision, a number: no interface as a value
   pMsg_some, pRound_some, rcL_some      where the tests hold the partial codes write
   fitsQ_put        fitsQ Bd S C dec K q = true → ∀ j, ((p162 (chainQ Bd S C dec) K).put (q,
                    j)).isSome
WHAT IS NOT SAID.  The converse.  What an evaluator builds.

Terms: lean/GLOSSARY.md.

-/
import Run.PageQFits
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PageQChain
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PageQMsg
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
import OnBytes.TypedOracleCompiler.Run.CodingPage160
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
import OnBytes.TypedOracleCompiler.Run.PlanQS   -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.ThinTie  -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDet  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDetProofs
import OnBytes.TypedOracleCompiler.Run.TwinTie  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage
import OnBytes.TypedOracleCompiler.Run.SerThin  -- TWO: reached in the library through files that are not said again
import Run.PageQ
import OnBytes.TypedOracleCompiler.Run.PlanQSpell

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Fmt (Item)

theorem pMsgO_some (l : List Item) (rt : List (Dig 256))
    (x : PlainOf l) (h : (toRoots l rt).isSome = true) :
    ((pMsgO l).put (rt, x)).isSome = true := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h
  show (((toRoots l rt).map fun y => (y, x)).bind (pMsg l).1.put).isSome = true
  rw [hy]
  exact pMsg_some l y x

/-- TWO: as many roots as the items have: then they fit -/
theorem toRoots_isSome : ∀ (l : List Item) (rt : List (Dig 256)),
    rt.length = _root_.Fmt.countItem .root l → (toRoots l rt).isSome = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [_root_.Fmt.countItem] at h
  | .root :: l, r :: rt, h => by
      show ((toRoots l rt).map _).isSome = true
      rw [Option.isSome_map]
      exact toRoots_isSome l rt (by simpa [_root_.Fmt.countItem] using h)
  | .root :: _, [], h => by simp [_root_.Fmt.countItem] at h
  | .f :: l, rt, h => toRoots_isSome l rt (by simpa [_root_.Fmt.countItem] using h)
  | .word :: l, rt, h => toRoots_isSome l rt (by simpa [_root_.Fmt.countItem] using h)
  | .e :: l, rt, h => toRoots_isSome l rt (by simpa [_root_.Fmt.countItem] using h)
  | .answer :: l, rt, h => toRoots_isSome l rt (by simpa [_root_.Fmt.countItem] using h)

/-- the roots fit the items; the nonce fits its word -/
def okRound : (w : ℕ) → (l : List Item) → List (Dig 256) → GPlain ℕ w (PlainOf l) → Bool
  | 0, l, rt, _ => (toRoots l rt).isSome
  | _ + 1, l, rt, (p : PlainOf l × ℕ) => (toRoots l rt).isSome && decide (p.2 < 2 ^ 64)

theorem pRound_some :
    ∀ (w : ℕ) (l : List Item) (rt : List (Dig 256)) (p : GPlain ℕ w (PlainOf l)),
      okRound w l rt p = true → ((pRound w l).put (rt, p)).isSome = true
  | 0, l, rt, p, h =>
    PCode.cons_some (pMsgO l) (msgBits l) (pMsgO_len l) (fun _ => pUnit word0) ((rt, p), ())
      (pMsgO_some l rt p h) rfl
  | w + 1, l, rt, (p : PlainOf l × ℕ), h => by
      have h' : ((toRoots l rt).isSome && decide (p.2 < 2 ^ 64)) = true := h
      rw [Bool.and_eq_true, decide_eq_true_iff] at h'
      exact PCode.cons_some (pMsgO l) (msgBits l) (pMsgO_len l) (fun _ => pWord) ((rt, p.1), p.2)
        (pMsgO_some l rt p.1 h'.1) (by rw [pWord_put _ h'.2]; rfl)

/-- the plain part is the slot part of the round with the number i, and fits there -/
def okL (C : CK) : (ds : List RD) → ℕ → List (Dig 256) → PBL C ds → Bool
  | [], _, _, _ => false
  | d :: _, 0, rt, .inl (.inr p) => okRound d.entry.work d.items rt p
  | _ :: _, 0, _, .inl (.inl _) => false
  | _ :: _, 0, _, .inr _ => false
  | _ :: ds, i + 1, rt, .inr q => okL C ds i rt q
  | _ :: _, _ + 1, _, .inl _ => false

theorem rcL_some (C : CK) :
    ∀ (ds : List RD) (i : ℕ) (rt : List (Dig 256)) (q : PBL C ds),
      okL C ds i rt q = true → ((rcL C ds i).put (rt, q)).isSome = true
  | [], _, _, _, h => by cases h
  | d :: _, 0, rt, .inl (.inr p), h => pRound_some d.entry.work d.items rt p h
  | _ :: _, 0, _, .inl (.inl _), h => by cases h
  | _ :: _, 0, _, .inr _, h => by cases h
  | _ :: ds, i + 1, rt, .inr q, h => rcL_some C ds i rt q h
  | _ :: _, _ + 1, _, .inl _, h => by cases h

variable (Bd : Type) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

/-- The test. -/
def fitsQ (K : ℕ) (q : FbIn 256 (LbS Bd C (rds S) dec) .onl) : Bool :=
  match q.round, q.head, q.plain with
  | i + 1, .f2 none ρ, .inr pl =>
      decide (ρ.length = 256) && decide (i + 1 < 2 ^ 64) &&
        decide ((chainQ Bd S C dec).kind (i + 1) < 256) &&
        decide ((chainQ Bd S C dec).work (i + 1) < 256) &&
        decide (K < 2 ^ 48) && okL C (rds S) i q.rt pl
  | _, _, _ => false

/-- Where the test holds, the coding writes the query in the format, at every block. -/
theorem fitsQ_put (K : ℕ) (q : FbIn 256 (LbS Bd C (rds S) dec) .onl)
    (h : fitsQ Bd S C dec K q = true) (j : Fin (K + 1)) :
    ((p162 (chainQ Bd S C dec) K).put (q, j)).isSome = true := by
  obtain ⟨round, head, rt, plain⟩ := q
  cases round with
  | zero => cases h
  | succ i =>
      cases head with
      | f2 xl ρ =>
          cases xl with
          | some _ => cases h
          | none =>
              rcases plain with _ | pl
              · cases h
              · have h' : (decide (ρ.length = 256) && decide (i + 1 < 2 ^ 64) &&
                      decide ((chainQ Bd S C dec).kind (i + 1) < 256) &&
                      decide ((chainQ Bd S C dec).work (i + 1) < 256) &&
                      decide (K < 2 ^ 48) && okL C (rds S) i rt pl) = true := h
                simp only [Bool.and_eq_true, decide_eq_true_iff] at h'
                obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h'
                have hb := (blockTo (decide ((chainQ Bd S C dec).work (i + 1) ≠ 0)) K j).isLt
                show ((pTup (chainQ Bd S C dec)).put
                    (decide
                        ((blockTo (decide ((chainQ Bd S C dec).work (i + 1) ≠ 0)) K j).val % 2 = 1),
                      ρ, i + 1,
                      ((rt, Sum.inr pl),
                        (blockTo (decide ((chainQ Bd S C dec).work (i + 1) ≠ 0)) K j).val /
                          2))).isSome = true
                refine PCode.cons_some _ _ _ _ _ rfl
                  (PCode.pre_some _ _ _
                    (PCode.cons_some _ _ _ _ _ ?_
                      (PCode.pre_some _ _ _
                        (PCode.cons_some _ _ _ _ _ ?_ (PCode.ins_some _ _ _ _ _ _ _ ?_ ?_)))))
                · show (if ρ.length = 256 then some ρ else none).isSome = true
                  rw [if_pos h1]
                  rfl
                · show (pWord.put (i + 1)).isSome = true
                  rw [pWord_put _ h2]
                  rfl
                · exact rcL_some C (rds S) i rt pl h6
                · show ((kwcTo ((chainQ Bd S C dec).kind (i + 1)) ((chainQ Bd S C dec).work (i + 1))
                        ((blockTo (decide ((chainQ Bd S C dec).work (i + 1) ≠ 0)) K
                            j).val / 2)).bind
                      pWord.put).isSome = true
                  unfold kwcTo
                  rw [if_pos ⟨h3, h4, by omega⟩]
                  show (pWord.put _).isSome = true
                  rw [pWord_put _ (by omega)]
                  rfl
      | f1 _ _ _ => cases h
      | f3 _ _ => cases h
      | f4 _ _ => cases h
      | f5 _ => cases h

end TypedOracleCompiler.Run.PQ
