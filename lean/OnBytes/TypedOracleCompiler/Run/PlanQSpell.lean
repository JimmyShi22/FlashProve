-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQSpell.lean: HOW A CHAIN QUERY OF THE GENERIC PROTOCOL IS SPELLED AS THE
FORMAT's HASH CALL, WITH A LIST OF ROOTS; AND THAT THE PARTIAL CODE OF A ROUND's MESSAGE WRITES THAT
SPELLING. After the library's Run/PlanQTypes.lean (PlainOf.bytes), Run/PlanQS.lean:300-344 (embPL,
msgSL, nonceSL, PDS), Run/PageQ.lean:91-113 (PBQ, rcQ, rcQ_ge, chainQ) and Run/PageQFit.lean:32-165
(pMsg_fit, pMsgO_fit, pRound_fit, rcL_fit, chainQ_fit), declaration for declaration.
  TURNED BY MATTER   bytesL (after PlainOf.bytes: THE k-TH ROOT AT THE k-TH ITEM "root"; the library
                     writes one root at
                     every such item), pMsg_fit (its statement is without the side condition on
                     b), pMsgO_fit, pRound_fit, rcL_fit, msgSL (a list of roots' bytes), PDS (msg:
                     the list as it stands, where the library has "rt.getD empty"; leaf: A
                     PARAMETER: of bodies), LbS (a body beside the library's interface)
  TURNED BY TYPE     rcQ, rcQ_ge ("Option" → "List", and the parameter Bd)
  TURNED BY A PARAMETER MORE (Bd; leaf)   PBQ, chainQ, chainQ_fit: else the library's text
  AS TEXT (by the program that compares)   embPL, nonceSL
  NEW                chain_put (p162_put at chainQ_fit)
  LEFT TO THE LIBRARY  pDig_put, inL_put', inR_put', pU64_put, Toy1.pE3_put, bytesToBits_append, Lb
  NOT SAID           leafSL, the leaves' fit (pVec_fit … leafQ_fit), firstQ(_fit), pageQ(_fit): they
                     want a body and its code
                     (strings), and the first query

Terms: lean/GLOSSARY.md.

-/
import Run.PageQFit
import OnBytes.TypedOracleCompiler.Run.PageQChain
import OnBytes.TypedOracleCompiler.Run.CodingPut

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Fmt (Item)

/-! ## The message's bytes -/

/-- the message's bytes: the items in their order, THE ROOTS IN THEIR ORDER, each at the place of
its own item "root" (nothing where the list has run out) -/
def bytesL : List ByteArray → (l : List Item) → PlainOf l → ByteArray
  | _, [], _ => ByteArray.empty
  | [], .root :: l, x => bytesL [] l x
  | r :: rts, .root :: l, x => r ++ bytesL rts l x
  | rts, .f :: l, (x : UInt64 × PlainOf l) => _root_.Fmt.u64 x.1 ++ bytesL rts l x.2
  | rts, .word :: l, (x : UInt64 × PlainOf l) => _root_.Fmt.u64 x.1 ++ bytesL rts l x.2
  | rts, .e :: l, (x : _root_.Fmt.Ext × PlainOf l) => _root_.Fmt.ext x.1 ++ bytesL rts l x.2
  | rts, .answer :: l, (x : _root_.Fmt.Ext × PlainOf l) => _root_.Fmt.ext x.1 ++ bytesL rts l x.2

/-- The message. -/
theorem pMsg_fit :
    ∀ (l : List Item) (rt : List (Dig 256)) (y : RootOf l), toRoots l rt = some y →
      ∀ (x : PlainOf l) (s : List Bool), (pMsg l).1.put (y, x) = some s →
        s = bytesToBits (bytesL (rt.map digToBytes) l x)
  | [], [], _, _, _, s, h => by
      rw [← Option.some.inj h]
      rfl
  | [], _ :: _, _, hy, _, _, _ => by cases hy
  | .root :: l, r :: rt, y, hy, x, s, h => by
      have h0 : (toRoots l rt).map (fun y => ((r, y) : Dig 256 × RootOf l)) = some y := hy
      cases hy' : toRoots l rt with
      | none => rw [hy'] at h0; cases h0
      | some y' =>
          rw [hy'] at h0
          have ey : y = ((r, y') : Dig 256 × RootOf l) := (Option.some.inj h0).symm
          subst ey
          obtain ⟨u, v, hu, hv, rfl⟩ :=
            PCode.cons_put pDig 256 pDig_len (fun _ => (pMsg l).1) (r, (y', x)) s h
          rw [pDig_put r u hu, pMsg_fit l rt y' hy' x v hv]
          exact (bytesToBits_append _ _).symm
  | .root :: _, [], _, hy, _, _, _ => by cases hy
  | .f :: l, rt, y, hy, (x : UInt64 × PlainOf l), s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pU64 64 pU64_len (fun _ => (pMsg l).1) (x.1, (y, x.2)) s h
      rw [pU64_put] at hu
      rw [← Option.some.inj hu, pMsg_fit l rt y hy x.2 v hv]
      exact (bytesToBits_append _ _).symm.trans (by cases rt <;> rfl)
  | .word :: l, rt, y, hy, (x : UInt64 × PlainOf l), s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pU64 64 pU64_len (fun _ => (pMsg l).1) (x.1, (y, x.2)) s h
      rw [pU64_put] at hu
      rw [← Option.some.inj hu, pMsg_fit l rt y hy x.2 v hv]
      exact (bytesToBits_append _ _).symm.trans (by cases rt <;> rfl)
  | .e :: l, rt, y, hy, (x : _root_.Fmt.Ext × PlainOf l), s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pE3 192 pE3_len (fun _ => (pMsg l).1) (x.1, (y, x.2)) s h
      rw [Toy1.pE3_put] at hu
      rw [← Option.some.inj hu, pMsg_fit l rt y hy x.2 v hv]
      exact (bytesToBits_append _ _).symm.trans (by cases rt <;> rfl)
  | .answer :: l, rt, y, hy, (x : _root_.Fmt.Ext × PlainOf l), s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put pE3 192 pE3_len (fun _ => (pMsg l).1) (x.1, (y, x.2)) s h
      rw [Toy1.pE3_put] at hu
      rw [← Option.some.inj hu, pMsg_fit l rt y hy x.2 v hv]
      exact (bytesToBits_append _ _).symm.trans (by cases rt <;> rfl)

theorem pMsgO_fit (l : List Item) (rt : List (Dig 256)) (x : PlainOf l)
    (s : List Bool) (h : (pMsgO l).put (rt, x) = some s) :
    s = bytesToBits (bytesL (rt.map digToBytes) l x) := by
  obtain ⟨a, ha, hs⟩ := PCode.pull_put _ _ _ _ _ (rt, x) s h
  have ha' : (toRoots l rt).map (fun y => (y, x)) = some a := ha
  cases hy : toRoots l rt with
  | none => rw [hy] at ha'; cases ha'
  | some y =>
      rw [hy] at ha'
      rw [← Option.some.inj ha'] at hs
      exact pMsg_fit l rt y hy x s hs

/-- The message and the nonce's word. -/
theorem pRound_fit :
    ∀ (w : ℕ) (l : List Item) (rt : List (Dig 256)) (p : GPlain ℕ w (PlainOf l)) (s : List Bool),
      (pRound w l).put (rt, p) = some s →
      s = bytesToBits (bytesL (rt.map digToBytes) l (GPlain.old (b := w) p)) ++
          bytesToBits (_root_.Fmt.u64n (GPlain.nonce (b := w) p))
  | 0, l, rt, p, s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put (pMsgO l) (msgBits l) (pMsgO_len l) (fun _ => pUnit word0) ((rt, p), ()) s h
      rw [pMsgO_fit l rt p u hu, ← Option.some.inj hv]
      rfl
  | w + 1, l, rt, (p : PlainOf l × ℕ), s, h => by
      obtain ⟨u, v, hu, hv, rfl⟩ :=
        PCode.cons_put (pMsgO l) (msgBits l) (pMsgO_len l) (fun _ => pWord) ((rt, p.1), p.2) s h
      have hv' : v = bytesToBits (_root_.Fmt.u64n p.2) := by
        have h0 : (if p.2 < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n p.2)) else none) =
            some v := hv
        by_cases hn : p.2 < 2 ^ 64
        · rw [if_pos hn] at h0
          exact (Option.some.inj h0).symm
        · rw [if_neg hn] at h0
          cases h0
      rw [pMsgO_fit l rt p.1 u hu, hv']
      rfl

/-! ## The spellings -/

/-- a plain part under the skeleton's annotation as one under the library's annotation of a shape -/
def embPL (C : CK) :
    (ds : List RD) → PlainPart (uL C ds) (Twin.allLo (SL C ds)) → PlainPart (uL C ds) (RoundSplits.allLocal (uL C ds))
  | [], p => p.elim
  | _ :: _, .inl x => .inl x
  | _ :: ds, .inr q => .inr (embPL C ds q)

def msgSL (C : CK) (rt : List ByteArray) :
    (ds : List RD) → PlainPart (uL C ds) (RoundSplits.allLocal (uL C ds)) → ByteArray
  | [], p => p.elim
  | d :: _, .inl (.inr p) => bytesL rt d.items (GPlain.old (b := d.entry.work) p)
  | _ :: _, .inl (.inl _) => ByteArray.empty
  | _ :: ds, .inr q => msgSL C rt ds q

def nonceSL (C : CK) : (ds : List RD) → PlainPart (uL C ds) (RoundSplits.allLocal (uL C ds)) → Nat
  | [], p => p.elim
  | d :: _, .inl (.inr p) => GPlain.nonce (b := d.entry.work) p
  | _ :: _, .inl (.inl _) => 0
  | _ :: ds, .inr q => nonceSL C ds q

theorem rcL_fit (C : CK) :
    ∀ (ds : List RD) (i : ℕ) (rt : List (Dig 256)) (q : PBL C ds) (s : List Bool),
      (rcL C ds i).put (rt, q) = some s →
      s = bytesToBits (msgSL C (rt.map digToBytes) ds q) ++
          bytesToBits (_root_.Fmt.u64n (nonceSL C ds q))
  | [], _, _, _, _, h => by cases h
  | d :: _, 0, rt, q, s, h => by
      obtain ⟨a, rfl, h1⟩ := inL_put' _ rt q s h
      obtain ⟨p, rfl, h2⟩ := inR_put' _ rt a s h1
      exact pRound_fit d.entry.work d.items rt p s h2
  | _ :: ds, i + 1, rt, q, s, h => by
      obtain ⟨b, rfl, h1⟩ := inR_put' _ rt q s h
      exact rcL_fit C ds i rt b s h1

/-! ## One chain at an interface whose Batch is the protocol -/

/-- The interface whose Batch is the protocol, with a body Bd beside the library's interface. -/
@[reducible] def LbS (Bd : Type) (C : CK) (ds : List RD) (dec : View → Bool) : BatchProtocolWithLeafBody Unit Unit :=
  { Lb (BatchInteractiveOracleProof.ofProto (PSof C ds dec).up.loc) with
    Bd := Bd, annT := RoundSplits.allLocal _, annL := RoundSplits.allLocal _ }

variable (Bd : Type) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

abbrev PBQ : Type :=
  PlainPart (Compile.Batch.shapeOf (LbS Bd C (rds S) dec) .onl)
      (Compile.Batch.annOf (LbS Bd C (rds S) dec) .onl)

/-- a round's message: round 0: nothing; round i + 1: the round with the number i, under the trivial
round -/
def rcQ : ℕ → PCode (List (Dig 256) × PBQ Bd S C dec)
  | 0 => PCode.empty _
  | i + 1 => inR (rcL C (rds S) i)

theorem rcQ_ge :
    ∀ (i : ℕ) (y : List (Dig 256) × PBQ Bd S C dec) (s : List Bool),
      (rcQ Bd S C dec i).put y = some s → 64 ≤ s.length
  | 0, _, _, h => by cases h
  | i + 1, y, s, h => by
      obtain ⟨y1, h1⟩ := inR_put _ y s h
      exact rcL_ge C (rds S) i y1 s h1

/-- The chain's data. -/
def chainQ : ChainD (LbS Bd C (rds S) dec) .onl where
  label := S.label
  kind := fun i => if i = 0 then 7 else ((S.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((S.rounds[i - 1]?).map (·.entry.work)).getD 0
  rc := rcQ Bd S C dec
  hrc := rcQ_ge Bd S C dec

/-- The spellings. (leaf: how a body is spelled: a parameter.) -/
def PDS (leaf : Bd → Option (Nat × Nat × ByteArray)) : PageD (LbS Bd C (rds S) dec) .onl where
  label := S.label
  kind := fun i => if i = 0 then 7 else ((S.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((S.rounds[i - 1]?).map (·.entry.work)).getD 0
  stm := fun _ => S.statement
  msg := fun _ rt pl => match pl with
    | .inl _ => ByteArray.empty
    | .inr q => msgSL C rt (rds S) q
  nonce := fun _ pl => match pl with
    | .inl _ => 0
    | .inr q => nonceSL C (rds S) q
  leaf := leaf
  cfg := S.cfg

/-- The chain's data fit the spellings. -/
theorem chainQ_fit (leaf : Bd → Option (Nat × Nat × ByteArray)) :
    ChainFit (chainQ Bd S C dec) (PDS Bd S C dec leaf) where
  label := rfl
  kind := fun _ => rfl
  work := fun _ => rfl
  rc := fun i rt pl s h => by
    match i, h with
    | 0, h => cases h
    | i + 1, h =>
        obtain ⟨b, rfl, h1⟩ := inR_put' _ rt pl s h
        exact rcL_fit C (rds S) i rt b s h1

/-- WHAT THE CODE OF A LATER ROUND's CHAIN QUERY WRITES IS THE FORMAT's STRING OF THE CALL, at the
generic chain with a list of trees a round and a list of roots a query: Run/CodingPut.lean's
p162_put (as text over OnBytes/TypedOracleCompiler) at chainQ_fit. -/
theorem chain_put (leaf : Bd → Option (Nat × Nat × ByteArray)) (K : ℕ) (hK : 0 < K)
    (x : FbIn 256 (LbS Bd C (rds S) dec) .onl × Fin (K + 1)) (s : List Bool)
    (h : (p162 (chainQ Bd S C dec) K).put x = some s) :
    ∃ c, fbCall (PDS Bd S C dec leaf) K x.1 x.2 = some c ∧ s = bytesToBits (strOf c) :=
  p162_put _ _ K hK (chainQ_fit Bd S C dec leaf) x s h

/-- TWO: a message with two roots and a word between them: each root at its own place. -/
example (r1 r2 : ByteArray) (w : UInt64) :
    bytesL [r1, r2] [.root, .word, .root] ((w, ()) : UInt64 × Unit) =
      r1 ++ (_root_.Fmt.u64 w ++ (r2 ++ ByteArray.empty)) := rfl

end TypedOracleCompiler.Run.PQ
