-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQFits.lean: a test, which writes no string, that a chain query of a round 1, 2, .. is one
that the encoding of the queries of Run/PageQ.lean writes in the programs' format, at every block;
with its law.

The compiled verifier asks typed oracles (`OracleName`, Compile/Batch/Oracles.lean), among them those for
chain queries and for the leaves and nodes of hash trees. To run it over one hash function, every
typed query, with the number of a block of its answer, is written as a bit string by a one-to-one
encoding with a parser (a coding: `Rom.OracleCoding`, Rom/Family.lean). Run/CodingPage.lean builds such an
encoding from a record of data, `PageC`.
Definitions that compute; theorems.

Why: at a long message (tens of thousands of bytes) the encoding's string of each block of a chain
answer is long, and there are many blocks. A faster family may answer such a query from the
format's hash directly; its tie to the family read out of the single oracle holds at the queries
that the encoding writes. To choose the fast form one must know that without writing the strings.

Main names:
  `okRound w l rt p`: "root or none" fits the items; the nonce is below 2^64.
  `okL C ds i rt q`: the plain part is the slot part of the round with the number i, and `okRound`
    there.
  `fitsQ S C dec K q`: a round i + 1; the later-round head with no late field and a chain value of
    256 bits; round, kind, work, the blocks' calls within their words' bounds; `okL`. Parameters:
    the description, the choice of challenge types, the decision, a number: no interface as a
    value.
  `fitsQ_put`: `fitsQ S C dec K q = true → ∀ j, ((p162 (chainQ S C dec) K).put (q, j)).isSome`.

Limits: this file says nothing on the converse. It says nothing on what an evaluator builds.

Terms: lean/GLOSSARY.md.
-/
import Run.PageQ

set_option autoImplicit false

namespace Run.PCode
variable {A B : Type}

theorem cons_some (a : PCode A) (n : ℕ) (ha : a.Len n) (p : A → PCode B) (x : A × B)
    (h1 : (a.put x.1).isSome = true) (h2 : ((p x.1).put x.2).isSome = true) :
    ((a.cons n ha p).put x).isSome = true := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h2
  show ((a.put x.1).bind fun u => ((p x.1).put x.2).map (u ++ ·)).isSome = true
  rw [hu, hv]
  rfl

theorem pre_some (c : List Bool) (p : PCode A) (a : A) (h : (p.put a).isSome = true) :
    ((p.pre c).put a).isSome = true := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h
  show ((p.put a).map (c ++ ·)).isSome = true
  rw [hu]
  rfl

theorem ins_some (p : PCode B) (a : PCode A) (k n : ℕ) (ha : a.Len n)
    (hp : ∀ y s, p.put y = some s → k ≤ s.length) (x : B × A)
    (h1 : (p.put x.1).isSome = true) (h2 : (a.put x.2).isSome = true) :
    ((p.ins a k n ha hp).put x).isSome = true := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h2
  show ((p.put x.1).bind fun s =>
      (a.put x.2).map fun w => s.take (s.length - k) ++ (w ++ s.drop (s.length - k))).isSome = true
  rw [hu, hv]
  rfl

end Run.PCode

namespace Run.PQ
open Rom Iop Compile Compile.Batch
open _root_.Fmt (Item)

theorem pDig_some (r : Dig 256) : (pDig.put r).isSome = true := by
  show ((digTo r).bind (pBits 256).put).isSome = true
  show (if (List.ofFn r).length = 256 then some (List.ofFn r) else none).isSome = true
  rw [if_pos List.length_ofFn]
  rfl

theorem pU64_some (x : UInt64) : (pU64.put x).isSome = true := by rw [pU64_put]; rfl

theorem pE3_some (e : _root_.Fmt.Ext) : (pE3.put e).isSome = true :=
  PCode.cons_some _ _ _ _ e (pU64_some _) (PCode.cons_some _ _ _ _ e.2 (pU64_some _) (pU64_some _))

theorem pMsg_some :
    ∀ (l : List Item) (y : RootOf l) (x : PlainOf l), ((pMsg l).1.put (y, x)).isSome = true
  | [], _, _ => rfl
  | .root :: l, (y : Dig 256 × RootOf l), x =>
    PCode.cons_some pDig 256 pDig_len (fun _ => (pMsg l).1) (y.1, (y.2, x))
      (pDig_some _) (pMsg_some l y.2 x)
  | .f :: l, y, (x : UInt64 × PlainOf l) =>
    PCode.cons_some pU64 64 pU64_len (fun _ => (pMsg l).1) (x.1, (y, x.2))
      (pU64_some _) (pMsg_some l y x.2)
  | .word :: l, y, (x : UInt64 × PlainOf l) =>
    PCode.cons_some pU64 64 pU64_len (fun _ => (pMsg l).1) (x.1, (y, x.2))
      (pU64_some _) (pMsg_some l y x.2)
  | .e :: l, y, (x : _root_.Fmt.Ext × PlainOf l) =>
    PCode.cons_some pE3 192 pE3_len (fun _ => (pMsg l).1) (x.1, (y, x.2))
      (pE3_some _) (pMsg_some l y x.2)
  | .answer :: l, y, (x : _root_.Fmt.Ext × PlainOf l) =>
    PCode.cons_some pE3 192 pE3_len (fun _ => (pMsg l).1) (x.1, (y, x.2))
      (pE3_some _) (pMsg_some l y x.2)

theorem pMsgO_some (l : List Item) (rt : Option (Dig 256))
    (x : PlainOf l) (h : (toRoots l rt).isSome = true) :
    ((pMsgO l).put (rt, x)).isSome = true := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h
  show (((toRoots l rt).map fun y => (y, x)).bind (pMsg l).1.put).isSome = true
  rw [hy]
  exact pMsg_some l y x

/-- "root or none" fits the items; the nonce fits its word -/
def okRound : (w : ℕ) → (l : List Item) → Option (Dig 256) → GPlain ℕ w (PlainOf l) → Bool
  | 0, l, rt, _ => (toRoots l rt).isSome
  | _ + 1, l, rt, (p : PlainOf l × ℕ) => (toRoots l rt).isSome && decide (p.2 < 2 ^ 64)

theorem pRound_some :
    ∀ (w : ℕ) (l : List Item) (rt : Option (Dig 256)) (p : GPlain ℕ w (PlainOf l)),
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
def okL (C : CK) : (ds : List RD) → ℕ → Option (Dig 256) → PBL C ds → Bool
  | [], _, _, _ => false
  | d :: _, 0, rt, .inl (.inr p) => okRound d.entry.work d.items rt p
  | _ :: _, 0, _, .inl (.inl _) => false
  | _ :: _, 0, _, .inr _ => false
  | _ :: ds, i + 1, rt, .inr q => okL C ds i rt q
  | _ :: _, _ + 1, _, .inl _ => false

theorem rcL_some (C : CK) :
    ∀ (ds : List RD) (i : ℕ) (rt : Option (Dig 256)) (q : PBL C ds),
      okL C ds i rt q = true → ((rcL C ds i).put (rt, q)).isSome = true
  | [], _, _, _, h => by cases h
  | d :: _, 0, rt, .inl (.inr p), h => pRound_some d.entry.work d.items rt p h
  | _ :: _, 0, _, .inl (.inl _), h => by cases h
  | _ :: _, 0, _, .inr _, h => by cases h
  | _ :: ds, i + 1, rt, .inr q, h => rcL_some C ds i rt q h
  | _ :: _, _ + 1, _, .inl _, h => by cases h

variable (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

/-- The test. -/
def fitsQ (K : ℕ) (q : FbIn 256 (LfQ S C dec ()) .onl) : Bool :=
  match q.round, q.head, q.plain with
  | i + 1, .f2 none ρ, .inr pl =>
      decide (ρ.length = 256) && decide (i + 1 < 2 ^ 64) &&
        decide ((chainQ S C dec).kind (i + 1) < 256) &&
        decide ((chainQ S C dec).work (i + 1) < 256) &&
        decide (K < 2 ^ 48) && okL C (rds S) i q.rt pl
  | _, _, _ => false

/-- Where the test holds, the coding writes the query in the format, at every block. -/
theorem fitsQ_put (K : ℕ) (q : FbIn 256 (LfQ S C dec ()) .onl)
    (h : fitsQ S C dec K q = true) (j : Fin (K + 1)) :
    ((p162 (chainQ S C dec) K).put (q, j)).isSome = true := by
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
                      decide ((chainQ S C dec).kind (i + 1) < 256) &&
                      decide ((chainQ S C dec).work (i + 1) < 256) &&
                      decide (K < 2 ^ 48) && okL C (rds S) i rt pl) = true := h
                simp only [Bool.and_eq_true, decide_eq_true_iff] at h'
                obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h'
                have hb := (blockTo (decide ((chainQ S C dec).work (i + 1) ≠ 0)) K j).isLt
                show ((pTup (chainQ S C dec)).put
                    (decide
                        ((blockTo (decide ((chainQ S C dec).work (i + 1) ≠ 0)) K j).val % 2 = 1),
                      ρ, i + 1,
                      ((rt, Sum.inr pl),
                        (blockTo (decide ((chainQ S C dec).work (i + 1) ≠ 0)) K j).val /
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
                · show ((kwcTo ((chainQ S C dec).kind (i + 1)) ((chainQ S C dec).work (i + 1))
                        ((blockTo (decide ((chainQ S C dec).work (i + 1) ≠ 0)) K j).val / 2)).bind
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

end Run.PQ
