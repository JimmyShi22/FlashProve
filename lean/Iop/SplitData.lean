-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SplitData.lean: the compiler's further data, carried along a plan of splits.

Beside a record of protocols L : `BatchProtocol` (words of this library: lean/GLOSSARY.md) with its
properties, the compiler (Compile/) asks of an instantiation: that the oracles of the three lists of
rounds are strings, as data; numberings of positions and coins, decision procedures for the abort
sets and the depth of a request tree (`BatchProtocol.Aux`); serializers (`SerLHB`); three numbers of opened
positions (`OpenNums`) with `BatchProtocol.Opens`. The plans are those of Iop/Split.lean and
Iop/BatchSplit.lean.
What needs no new data: the numberings of the coins and of the encoder's randomness; the decision
procedures; the depth of a request tree; the numbers of opened positions (the verifier reads the
same positions: `BatchProtocol.Opens.split`); the tag and the serializers of requests and of symbols of
encodings.
What is new data: for each split, for each of its two parts, a record `RKit`: that the part's oracle
is a string, a numbering of its positions, serializers of its pairs (position, symbol) and of its
plain part. In Batch also `AKit`: the numberings of the positions of the two components and the
serializers of their plain parts; for parts that are sent whole by the slots or whole in the shared
component these are computed from the `RKit` (`AKit.ofSlot`, `AKit.ofShared`).
A remainder that is split again also has an `RKit`, of which only the field `pt` is used.
  `SPlan.Kits`, `APlan.Kits`: one record for each part of each split
Notation:
  `Round.IsPoint` (Iop/Shape.lean): a round whose oracle part is a string that is read symbol by
    symbol, over a finite set of positions: this head's "the oracle is a string".
  `pt`, `np`, `ser` (fields of `RKit`): in the order of this head's words: that the part's oracle is
    a string; a numbering of its positions; the serializers (`SerR`).
  `RAnn r` (Iop/Batch.lean): the annotation of one round r of the local shape: its kind, and the
    splitting of a prover message of the local transcript into (m_0, m_j); `own` says to which part
    an oracle position belongs, and `P0`, `Pj` are the plain strings of the parts. `RoundSplits s`: the
    annotation of a shape.
  `Kind` (Iop/Batch.lean): a round is called shared (sh) or local (lo) after its verifier message.
  `card0`, `cardJ` (Iop/BatchWireOf.lean): the number of positions of the shared component m_0 of a
    round; of a slot's component m_j. `n0`, `nJ` (fields of `AKit`): the numberings of these
    positions.
  `SPlan s` (Iop/Split.lean): a plan of splits; `APlan P A` (Iop/BatchSplit.lean): for each split of
    the plan, its annotation (`ACut`); `ann1`, `ann2`: the annotations of the round of the first
    part and of the remainder.
  `BatchProtocol` (Iop/Batch.lean): the five algorithms (I, D, Test, Link, Batch), with the honest sides; the
    three lists of rounds: `L.offline.shape`, `L.link.shape`, `L.onlineBatch.loc.shape`.
  `K : P.Kits`: for each split an `RKit` of the first part and one of the remainder.
Not in this file: widths and lists of opened positions round by round (`BitsS`, `OpenList`,
Iop/SerS.lean; Iop/Sizes.lean; `SizeNums`, Compile/Batch/Size.lean). They are needed for the
statements on sizes only, not for the theorem.
-/
import Iop.SplitKit
import Iop.BatchWireOf
import Iop.SerB

namespace Iop

/-! ## 1. Further data -/

/-- What the compiler asks of one round of an ordinary IOP. -/
structure RKit (r : Round) where
  pt  : r.IsPoint
  np  : r.Pos ≃ Fin (@Fintype.card r.Pos pt.finPos)
  ser : SerR r

/-- For each split an `RKit` of the first part and one of the remainder. -/
def SPlan.Kits : {s : Shape} → SPlan s → Type
  | _, .nil => Unit
  | _, .keep _ P => P.Kits
  | _, .cut c P => RKit c.fst × RKit c.snd × P.Kits

/-- What the compiler asks in addition of one round of a protocol with slots. -/
structure AKit {r : Round} (a : RAnn r) (pt : r.IsPoint) where
  n0  : {p : r.Pos // a.own p = false} ≃ Fin (a.card0 pt)
  nJ  : {p : r.Pos // a.own p = true} ≃ Fin (a.cardJ pt)
  ser : Ser a.P0 × Ser a.Pj

def AKit.ofSlot (k : Kind) {r : Round} (K : RKit r) : AKit (RAnn.ofSlot k r) K.pt :=
  ⟨(RAnn.numOfSlot k r K.pt K.np).1, (RAnn.numOfSlot k r K.pt K.np).2, SerR.ofSlot k K.ser⟩

def AKit.ofShared (k : Kind) {r : Round} (K : RKit r) : AKit (RAnn.ofShared k r) K.pt :=
  ⟨(RAnn.numOfShared k r K.pt K.np).1, (RAnn.numOfShared k r K.pt K.np).2, SerR.ofShared k K.ser⟩

def APlan.Kits : {s : Shape} → (P : SPlan s) → P.Kits → (A : RoundSplits s) → APlan P A → Type
  | _, .nil => fun _ _ _ => Unit
  | _, .keep r P => fun K (A : RAnn r × RoundSplits _) Z => APlan.Kits P K A.2 Z
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      AKit Z.1.ann1 K.1.pt × AKit Z.1.ann2 K.2.1.pt ×
        APlan.Kits P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2

/-! ## 2. The plan of one round -/


/-- the further data of the plan of one round -/
def RPlan.Kits : {r : Round} → RPlan r → Type
  | _, .keep _ => Unit
  | _, .cut c rest => RKit c.fst × RKit c.snd × rest.Kits





/-! ## 3. A serializer of a type without elements -/

/-- a serializer of a type without elements -/
def Ser.ofIsEmpty (α : Type) [IsEmpty α] : Ser α where
  put a := isEmptyElim a
  get _ := none
  get_put a _ := isEmptyElim a
  put_get _ a _ _ := isEmptyElim a

/-! ## 4. The data of all rounds

Five recursions on a plan P of splits of the list of rounds s: `Shape.IsPoint.splitK`,
`Shape.NumPos.splitK`, `SerS.splitK`, and, with annotations, `Shape.NumPosB.splitK`, `SerA.splitK`.
Each takes the records K of the plan (`P.Kits`; with annotations also `APlan.Kits`) and one kind of
data of s, and gives that kind of data of `P.shape`: a round that is kept keeps its data; at a split
the first part has the data of its record, and the recursion goes on with the remainder's record. -/


def Shape.IsPoint.splitK : {s : Shape} → (P : SPlan s) → P.Kits → s.IsPoint → P.shape.IsPoint
  | _, .nil => fun _ _ => ()
  | _, .keep r P => fun K (h : r.IsPoint × Shape.IsPoint _) => (h.1, Shape.IsPoint.splitK P K h.2)
  | _, .cut (r := r) (s := s) c P => fun (K : RKit c.fst × RKit c.snd × P.Kits) (h : r.IsPoint × s.IsPoint) =>
      (K.1.pt, Shape.IsPoint.splitK P K.2.2 (show Shape.IsPoint (c.snd :: s) from (K.2.1.pt, h.2)))

def Shape.NumPos.splitK :
    {s : Shape} → (P : SPlan s) → (K : P.Kits) → (h : s.IsPoint) →
    s.NumPos h → P.shape.NumPos (h.splitK P K)
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
      fun K (h : r.IsPoint × Shape.IsPoint _)
          (n : (r.Pos ≃ Fin (@Fintype.card r.Pos h.1.finPos)) × Shape.NumPos _ h.2) =>
      (n.1, Shape.NumPos.splitK P K h.2 n.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (h : r.IsPoint × s.IsPoint)
          (n : (r.Pos ≃ Fin (@Fintype.card r.Pos h.1.finPos)) × s.NumPos h.2) =>
      (K.1.np, Shape.NumPos.splitK
          P K.2.2 (show Shape.IsPoint (c.snd :: s) from (K.2.1.pt, h.2)) (K.2.1.np, n.2))

def SerS.splitK : {s : Shape} → (P : SPlan s) → P.Kits → SerS s → SerS P.shape
  | _, .nil => fun _ _ => ()
  | _, .keep r P => fun K (e : SerR r × SerS _) => (e.1, SerS.splitK P K e.2)
  | _, .cut (r := r) (s := s) c P => fun (K : RKit c.fst × RKit c.snd × P.Kits) (e : SerR r × SerS s) =>
      (K.1.ser, SerS.splitK P K.2.2 (show SerS (c.snd :: s) from (K.2.1.ser, e.2)))

def Shape.NumPosB.splitK :
    {s : Shape} → (P : SPlan s) → (K : P.Kits) → (A : RoundSplits s) →
    (Z : APlan P A) → APlan.Kits P K A Z → (h : s.IsPoint) →
    s.NumPosB A h → P.shape.NumPosB (A.split P Z) (h.splitK P K)
  | _, .nil => fun _ _ _ _ _ _ => ()
  | _, .keep r P =>
      fun K (A : RAnn r × RoundSplits _) Z KA (h : r.IsPoint × Shape.IsPoint _)
          (n : ({p : r.Pos // A.1.own p = false} ≃ Fin (A.1.card0 h.1)) ×
            ({p : r.Pos // A.1.own p = true} ≃ Fin (A.1.cardJ h.1)) × Shape.NumPosB _ A.2 h.2) =>
      (n.1, n.2.1, Shape.NumPosB.splitK P K A.2 Z KA h.2 n.2.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (KA : AKit Z.1.ann1 K.1.pt × AKit Z.1.ann2 K.2.1.pt ×
            APlan.Kits P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)
          (h : r.IsPoint × s.IsPoint)
          (n : ({p : r.Pos // A.1.own p = false} ≃ Fin (A.1.card0 h.1)) ×
            ({p : r.Pos // A.1.own p = true} ≃ Fin (A.1.cardJ h.1)) × s.NumPosB A.2 h.2) =>
      (KA.1.n0, KA.1.nJ,
        Shape.NumPosB.splitK P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 KA.2.2
          (show Shape.IsPoint (c.snd :: s) from (K.2.1.pt, h.2)) (KA.2.1.n0, KA.2.1.nJ, n.2.2))

def SerA.splitK :
    {s : Shape} → (P : SPlan s) → (K : P.Kits) → (A : RoundSplits s) → (Z : APlan P A) →
    APlan.Kits P K A Z → SerA s A → SerA P.shape (A.split P Z)
  | _, .nil => fun _ _ _ _ _ => ()
  | _, .keep r P =>
    fun K (A : RAnn r × RoundSplits _) Z KA (e : (Ser A.1.P0 × Ser A.1.Pj) × SerA _ A.2) =>
      (e.1, SerA.splitK P K A.2 Z KA e.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × APlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (KA : AKit Z.1.ann1 K.1.pt × AKit Z.1.ann2 K.2.1.pt ×
            APlan.Kits P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)
          (e : (Ser A.1.P0 × Ser A.1.Pj) × SerA s A.2) =>
      (KA.1.ser,
        SerA.splitK P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2))
          Z.2 KA.2.2 (KA.2.1.ser, e.2))

/-! ## 5. The data of an `BatchProtocol` -/

variable {I X : Type}

/-- All new data of a split of an `BatchProtocol`. -/
structure BatchProtocol.SplitKits (L : BatchProtocol I X) (PT : SPlan L.offline.shape) (PL : SPlan L.link.shape)
    (PB : SPlan L.onlineBatch.loc.shape) (ZB : APlan PB L.onlineBatch.ann) where
  T  : PT.Kits
  Lk : PL.Kits
  B  : PB.Kits
  A  : APlan.Kits PB B L.onlineBatch.ann ZB

variable {L : BatchProtocol I X} {PT : SPlan L.offline.shape} {PL : SPlan L.link.shape}
  {PB : SPlan L.onlineBatch.loc.shape} {ZB : APlan PB L.onlineBatch.ann}

def BatchProtocol.Aux.split {pT : L.offline.shape.IsPoint} {pL : L.link.shape.IsPoint}
    {pB : L.onlineBatch.loc.shape.IsPoint} (ax : L.Aux pT pL pB) (K : L.SplitKits PT PL PB ZB) :
    (L.split PT PL PB ZB).Aux (pT.splitK PT K.T) (pL.splitK PL K.Lk) (pB.splitK PB K.B) where
  posT := ax.posT.splitK PT K.T pT
  posL := ax.posL.splitK PL K.Lk pL
  posB := ax.posB.splitK PB K.B L.onlineBatch.ann ZB K.A pB
  numRI := ax.numRI
  numT := ax.numT
  numL := ax.numL
  numB0 := ax.numB0
  numB := ax.numB
  decT := fun w x ρ => ax.decT w x (Rho.merge PT ρ)
  decL := fun w x ρ => ax.decL w x (Rho.merge PL ρ)
  decB := fun w x ρ => ax.decB w x (RhoLo.merge PB L.onlineBatch.ann ZB ρ)
  depthReq := ax.depthReq

theorem BatchProtocol.Aux.split_depthReq {pT : L.offline.shape.IsPoint} {pL : L.link.shape.IsPoint}
    {pB : L.onlineBatch.loc.shape.IsPoint} (ax : L.Aux pT pL pB) (K : L.SplitKits PT PL PB ZB) :
    (ax.split K).depthReq = ax.depthReq := rfl

def SerLHB.split (D : SerLHB L) (K : L.SplitKits PT PL PB ZB) : SerLHB (L.split PT PL PB ZB) where
  tag := D.tag
  x := D.x
  sg := D.sg
  T := D.T.splitK PT K.T
  Lk := D.Lk.splitK PL K.Lk
  O := D.O.splitK PB K.B
  A := D.A.splitK PB K.B L.onlineBatch.ann ZB K.A

/-- The bounds `no` on opened positions still hold. -/
theorem BatchProtocol.Opens.split {no : OpenNums} (h : L.Opens no) (PT : SPlan L.offline.shape)
    (PL : SPlan L.link.shape) (PB : SPlan L.onlineBatch.loc.shape) (ZB : APlan PB L.onlineBatch.ann) :
    (L.split PT PL PB ZB).Opens no :=
  ⟨fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_split PT x ρ pl)).le.trans (h.opT x _ _),
   fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_split PL x ρ pl)).le.trans (h.opL x _ _),
   fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_split PB x ρ pl)).le.trans (h.opB x _ _)⟩

end Iop
