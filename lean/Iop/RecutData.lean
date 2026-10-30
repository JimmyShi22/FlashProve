-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/RecutData.lean: the compiler's further data, carried along a plan of splits and merges.

Beside a record of protocols (`BatchProtocol`, Iop/Batch.lean) the compiler (Compile/) needs further data:
that each oracle is a string, numberings, decision procedures, serializers, numbers of opened
positions. The plans are those of Iop/Recut.lean and Iop/BatchRecut.lean. At a split the data of the
two parts are new data (`RKit`, `AKit`; for the cases in which an `AKit` is computed from the
`RKit`: Iop/SplitData.lean); at a merge all data are computed from the old ones, by the one-round
terms of Iop/JoinData.lean and Iop/JoinProofs.lean (in `SerA.recutK`: by `Ser.prod`, Iop/Ser.lean;
the decision procedures: by `Rho.old`, Iop/Recut.lean, and `RhoLo.old`, Iop/BatchRecut.lean).
Widths and numbers of opened positions round by round are not in this file.

Notation: `s.IsPoint : Type` (Iop/Shape.lean): every round's oracle part is a string;
`s.NumPos h : Type` (Iop/Num.lean): for each round a numbering of its oracle positions;
`s.NumPosB A h : Type` (Iop/BatchWireOf.lean): for each round of a protocol with slots two
numberings: of the positions of the shared component, and of those of a slot's component;
`SerS s : Type` (Iop/SerS.lean): for each round of a list its two serializers; `SerA s A : Type`
(Iop/SerB.lean): for each round of an annotated list: serializers of the plain parts of the shared
component and of a slot's component; `L.Aux pT pL pB` (a structure, Iop/BatchWireOf.lean): what else
the compiled scheme needs as data; `SerLHB L` (a structure, Iop/SerB.lean): what the serialization
of the queries needs of the record of protocols; `OpenNums` (a structure, Iop/WireOf.lean): bounds
on the numbers of positions that the three verifiers open, external ones included; `RoundSplits s : Type 1`
(Iop/Batch.lean): the annotation of a shape; `AXPlan P A : Type 1` (Iop/BatchRecut.lean): for each
split of the plan, its annotation; `AXPlan.Kits P K A Z : Type`: for each split an `AKit`
(Iop/SplitData.lean) of the first part and one of the remainder; a name that ends in `recutK` takes
K : `P.Kits` (`Shape.NumPosB.recutK`, `SerA.recutK` also Z and KA : `AXPlan.Kits P K A Z`) and gives
the datum of `P.shape` from that of s.
-/
import Iop.BatchRecut
import Iop.RecutProofs
import Iop.SplitData
import Iop.JoinData

namespace Iop

/-! ## 1. The further data of the new rounds -/

/-- For each split the further data of the first part and of the remainder. -/
def XPlan.Kits : {s : Shape} → XPlan s → Type
  | _, .nil => Unit
  | _, .keep _ P => P.Kits
  | _, .cut c P => RKit c.fst × RKit c.snd × P.Kits
  | _, .msg _ _ _ P => P.Kits
  | _, .chal _ _ _ P => P.Kits

def AXPlan.Kits : {s : Shape} → (P : XPlan s) → P.Kits → (A : RoundSplits s) → AXPlan P A → Type
  | _, .nil => fun _ _ _ => Unit
  | _, .keep r P => fun K (A : RAnn r × RoundSplits _) Z => AXPlan.Kits P K A.2 Z
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      AKit Z.1.ann1 K.1.pt × AKit Z.1.ann2 K.2.1.pt ×
        AXPlan.Kits P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2
  | _, .msg r1 r2 (s := s) _ P =>
    fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.Kits P K (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z
  | _, .chal r1 r2 (s := s) _ P =>
    fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.Kits P K (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z

def XPlan.Kits.keepAll : (s : Shape) → (XPlan.keepAll s).Kits
  | [] => ()
  | _ :: s => XPlan.Kits.keepAll s

def AXPlan.Kits.keepAll :
    (s : Shape) → (A : RoundSplits s) →
    AXPlan.Kits (XPlan.keepAll s) (XPlan.Kits.keepAll s) A (AXPlan.keepAll s A)
  | [], _ => ()
  | _ :: s, A => AXPlan.Kits.keepAll s A.2

/-! ## 2. The data of a list of rounds -/

def Shape.IsPoint.recutK : {s : Shape} → (P : XPlan s) → P.Kits → s.IsPoint → P.shape.IsPoint
  | _, .nil => fun _ _ => ()
  | _, .keep r P => fun K (h : r.IsPoint × Shape.IsPoint _) => (h.1, Shape.IsPoint.recutK P K h.2)
  | _, .cut (r := r) (s := s) c P => fun (K : RKit c.fst × RKit c.snd × P.Kits) (h : r.IsPoint × s.IsPoint) =>
      (K.1.pt, Shape.IsPoint.recutK P K.2.2 (show Shape.IsPoint (c.snd :: s) from (K.2.1.pt, h.2)))
  | _, .msg r1 r2 (s := s) _ P => fun K (h : r1.IsPoint × r2.IsPoint × s.IsPoint) =>
      Shape.IsPoint.recutK P K
        (show Shape.IsPoint (r1.joinMsg r2 :: s) from (h.1.joinMsg h.2.1, h.2.2))
  | _, .chal r1 r2 (s := s) _ P => fun K (h : r1.IsPoint × r2.IsPoint × s.IsPoint) =>
      Shape.IsPoint.recutK P K
        (show Shape.IsPoint (r1.joinChal r2 :: s) from (h.1.joinChal r2, h.2.2))

def Shape.NumPos.recutK :
    {s : Shape} → (P : XPlan s) → (K : P.Kits) → (h : s.IsPoint) →
    s.NumPos h → P.shape.NumPos (h.recutK P K)
  | _, .nil => fun _ _ _ => ()
  | _, .keep r P =>
    fun K (h : r.IsPoint × Shape.IsPoint _)
      (n : (r.Pos ≃ Fin (@Fintype.card r.Pos h.1.finPos)) × Shape.NumPos _ h.2) =>
        (n.1, Shape.NumPos.recutK P K h.2 n.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (h : r.IsPoint × s.IsPoint)
          (n : (r.Pos ≃ Fin (@Fintype.card r.Pos h.1.finPos)) × s.NumPos h.2) =>
      (K.1.np, Shape.NumPos.recutK
          P K.2.2 (show Shape.IsPoint (c.snd :: s) from (K.2.1.pt, h.2)) (K.2.1.np, n.2))
  | _, .msg r1 r2 (s := s) _ P =>
      fun K (h : r1.IsPoint × r2.IsPoint × s.IsPoint)
          (n : (r1.Pos ≃ Fin (@Fintype.card r1.Pos h.1.finPos)) ×
            (r2.Pos ≃ Fin (@Fintype.card r2.Pos h.2.1.finPos)) × s.NumPos h.2.2) =>
      Shape.NumPos.recutK P K
        (show Shape.IsPoint (r1.joinMsg r2 :: s) from (h.1.joinMsg h.2.1, h.2.2))
        (numSum h.1.finPos h.2.1.finPos n.1 n.2.1, n.2.2)
  | _, .chal r1 r2 (s := s) _ P =>
      fun K (h : r1.IsPoint × r2.IsPoint × s.IsPoint)
          (n : (r1.Pos ≃ Fin (@Fintype.card r1.Pos h.1.finPos)) ×
            (r2.Pos ≃ Fin (@Fintype.card r2.Pos h.2.1.finPos)) × s.NumPos h.2.2) =>
      Shape.NumPos.recutK P K
        (show Shape.IsPoint (r1.joinChal r2 :: s) from (h.1.joinChal r2, h.2.2)) (n.1, n.2.2)

def SerS.recutK : {s : Shape} → (P : XPlan s) → P.Kits → SerS s → SerS P.shape
  | _, .nil => fun _ _ => ()
  | _, .keep r P => fun K (e : SerR r × SerS _) => (e.1, SerS.recutK P K e.2)
  | _, .cut (r := r) (s := s) c P =>
    fun (K : RKit c.fst × RKit c.snd × P.Kits) (e : SerR r × SerS s) =>
      (K.1.ser, SerS.recutK P K.2.2 (show SerS (c.snd :: s) from (K.2.1.ser, e.2)))
  | _, .msg r1 r2 (s := s) _ P =>
    fun K (e : SerR r1 × SerR r2 × SerS s) =>
      SerS.recutK P K (show SerS (r1.joinMsg r2 :: s) from (SerR.joinMsg e.1 e.2.1, e.2.2))
  | _, .chal r1 r2 (s := s) _ P =>
    fun K (e : SerR r1 × SerR r2 × SerS s) =>
      SerS.recutK P K (show SerS (r1.joinChal r2 :: s) from (e.1, e.2.2))

def Shape.NumPosB.recutK :
    {s : Shape} → (P : XPlan s) → (K : P.Kits) → (A : RoundSplits s) →
    (Z : AXPlan P A) → AXPlan.Kits P K A Z → (h : s.IsPoint) →
    s.NumPosB A h → P.shape.NumPosB (A.recut P Z) (h.recutK P K)
  | _, .nil => fun _ _ _ _ _ _ => ()
  | _, .keep r P =>
      fun K (A : RAnn r × RoundSplits _) Z KA (h : r.IsPoint × Shape.IsPoint _)
          (n : ({p : r.Pos // A.1.own p = false} ≃ Fin (A.1.card0 h.1)) ×
            ({p : r.Pos // A.1.own p = true} ≃ Fin (A.1.cardJ h.1)) × Shape.NumPosB _ A.2 h.2) =>
      (n.1, n.2.1, Shape.NumPosB.recutK P K A.2 Z KA h.2 n.2.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (KA : AKit Z.1.ann1 K.1.pt × AKit Z.1.ann2 K.2.1.pt ×
            AXPlan.Kits P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)
          (h : r.IsPoint × s.IsPoint)
          (n : ({p : r.Pos // A.1.own p = false} ≃ Fin (A.1.card0 h.1)) ×
            ({p : r.Pos // A.1.own p = true} ≃ Fin (A.1.cardJ h.1)) × s.NumPosB A.2 h.2) =>
      (KA.1.n0, KA.1.nJ,
        Shape.NumPosB.recutK P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2 KA.2.2
          (show Shape.IsPoint (c.snd :: s) from (K.2.1.pt, h.2)) (KA.2.1.n0, KA.2.1.nJ, n.2.2))
  | _, .msg r1 r2 (s := s) _ P =>
      fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z KA (h : r1.IsPoint × r2.IsPoint × s.IsPoint)
          (n : ({p : r1.Pos // A.1.own p = false} ≃ Fin (A.1.card0 h.1)) ×
            ({p : r1.Pos // A.1.own p = true} ≃ Fin (A.1.cardJ h.1)) ×
            ({p : r2.Pos // A.2.1.own p = false} ≃ Fin (A.2.1.card0 h.2.1)) ×
            ({p : r2.Pos // A.2.1.own p = true} ≃ Fin (A.2.1.cardJ h.2.1)) ×
            s.NumPosB A.2.2 h.2.2) =>
      Shape.NumPosB.recutK P K (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z KA
        (show Shape.IsPoint (r1.joinMsg r2 :: s) from (h.1.joinMsg h.2.1, h.2.2))
        ((NumRB.joinMsg (a1 := A.1) (a2 := A.2.1) (n.1, n.2.1) (n.2.2.1, n.2.2.2.1)).1,
          (NumRB.joinMsg (a1 := A.1) (a2 := A.2.1) (n.1, n.2.1) (n.2.2.1, n.2.2.2.1)).2,
          n.2.2.2.2)
  | _, .chal r1 r2 (s := s) _ P =>
      fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z KA (h : r1.IsPoint × r2.IsPoint × s.IsPoint)
          (n : ({p : r1.Pos // A.1.own p = false} ≃ Fin (A.1.card0 h.1)) ×
            ({p : r1.Pos // A.1.own p = true} ≃ Fin (A.1.cardJ h.1)) ×
            ({p : r2.Pos // A.2.1.own p = false} ≃ Fin (A.2.1.card0 h.2.1)) ×
            ({p : r2.Pos // A.2.1.own p = true} ≃ Fin (A.2.1.cardJ h.2.1)) ×
            s.NumPosB A.2.2 h.2.2) =>
      Shape.NumPosB.recutK P K (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z KA
        (show Shape.IsPoint (r1.joinChal r2 :: s) from (h.1.joinChal r2, h.2.2))
        (n.1, n.2.1, n.2.2.2.2)

def SerA.recutK :
    {s : Shape} → (P : XPlan s) → (K : P.Kits) → (A : RoundSplits s) → (Z : AXPlan P A) →
    AXPlan.Kits P K A Z → SerA s A → SerA P.shape (A.recut P Z)
  | _, .nil => fun _ _ _ _ _ => ()
  | _, .keep r P =>
    fun K (A : RAnn r × RoundSplits _) Z KA (e : (Ser A.1.P0 × Ser A.1.Pj) × SerA _ A.2) =>
      (e.1, SerA.recutK P K A.2 Z KA e.2)
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2)))
          (KA : AKit Z.1.ann1 K.1.pt × AKit Z.1.ann2 K.2.1.pt ×
            AXPlan.Kits P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2)
          (e : (Ser A.1.P0 × Ser A.1.Pj) × SerA s A.2) =>
      (KA.1.ser,
        SerA.recutK P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2))
          Z.2 KA.2.2 (KA.2.1.ser, e.2))
  | _, .msg r1 r2 (s := s) _ P =>
      fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z KA
          (e : (Ser A.1.P0 × Ser A.1.Pj) × (Ser A.2.1.P0 × Ser A.2.1.Pj) × SerA s A.2.2) =>
      SerA.recutK P K (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z KA
        ((Ser.prod e.1.1 e.2.1.1, Ser.prod e.1.2 e.2.1.2), e.2.2)
  | _, .chal r1 r2 (s := s) _ P =>
      fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z KA
          (e : (Ser A.1.P0 × Ser A.1.Pj) × (Ser A.2.1.P0 × Ser A.2.1.Pj) × SerA s A.2.2) =>
      SerA.recutK P K (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z KA
        (e.1, e.2.2)

/-! ## 3. The data of a record of protocols -/

variable {I X : Type}

/-- All new data of the plans for Test, Link and Batch (the three protocols of `BatchProtocol`). -/
structure BatchProtocol.RecutKits (L : BatchProtocol I X) (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape)
    (XB : XPlan L.onlineBatch.loc.shape) (ZB : AXPlan XB L.onlineBatch.ann) where
  T  : XT.Kits
  Lk : XL.Kits
  B  : XB.Kits
  A  : AXPlan.Kits XB B L.onlineBatch.ann ZB

variable {L : BatchProtocol I X} {XT : XPlan L.offline.shape} {XL : XPlan L.link.shape}
  {XB : XPlan L.onlineBatch.loc.shape} {ZB : AXPlan XB L.onlineBatch.ann}

def BatchProtocol.Aux.recut {pT : L.offline.shape.IsPoint} {pL : L.link.shape.IsPoint}
    {pB : L.onlineBatch.loc.shape.IsPoint} (ax : L.Aux pT pL pB)
    (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (K : L.RecutKits XT XL XB ZB) :
    (L.recut XT XL XB ZB hK).Aux (pT.recutK XT K.T) (pL.recutK XL K.Lk) (pB.recutK XB K.B) where
  posT := ax.posT.recutK XT K.T pT
  posL := ax.posL.recutK XL K.Lk pL
  posB := ax.posB.recutK XB K.B L.onlineBatch.ann ZB K.A pB
  numRI := ax.numRI
  numT := ax.numT
  numL := ax.numL
  numB0 := ax.numB0
  numB := ax.numB
  decT := fun w x ρ => ax.decT w x (Rho.old XT ρ)
  decL := fun w x ρ => ax.decL w x (Rho.old XL ρ)
  decB := fun w x ρ => ax.decB w x (RhoLo.old XB L.onlineBatch.ann ZB hK ρ)
  depthReq := ax.depthReq

theorem BatchProtocol.Aux.recut_depthReq {pT : L.offline.shape.IsPoint} {pL : L.link.shape.IsPoint}
    {pB : L.onlineBatch.loc.shape.IsPoint} (ax : L.Aux pT pL pB)
    (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (K : L.RecutKits XT XL XB ZB) :
    (ax.recut hK K).depthReq = ax.depthReq := rfl

def SerLHB.recut (D : SerLHB L) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (K : L.RecutKits XT XL XB ZB) :
    SerLHB (L.recut XT XL XB ZB hK) where
  tag := D.tag
  x := D.x
  sg := D.sg
  T := D.T.recutK XT K.T
  Lk := D.Lk.recutK XL K.Lk
  O := D.O.recutK XB K.B
  A := D.A.recutK XB K.B L.onlineBatch.ann ZB K.A

/-- After `BatchProtocol.recut` (which takes `hK`), the bounds `no` on the numbers of positions that the
verifiers open still hold. -/
theorem BatchProtocol.Opens.recut {no : OpenNums} (h : L.Opens no) (XT : XPlan L.offline.shape)
    (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
    (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) :
    (L.recut XT XL XB ZB hK).Opens no :=
  ⟨fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_recut XT x ρ pl)).le.trans (h.opT x _ _),
   fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_recut XL x ρ pl)).le.trans (h.opL x _ _),
   fun x ρ pl => (congrArg (· + _) (InteractiveOracleProof.card_reads_recut XB x ρ pl)).le.trans (h.opB x _ _)⟩

end Iop
