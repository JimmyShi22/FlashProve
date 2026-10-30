-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchWirePr.lean: which Merkle trees are opened by pruned Merkle paths: how the flags `pr0`,
`prJ` (Iop/BatchWire.lean) and `pr` (Iop/Wire.lean) of a wire record are set. (Words of this
library: lean/GLOSSARY.md.)

The flags say, tree by tree, whether the opened leaves are checked together, from one pruned list of
sibling digests, or each along a full path. They are fields with the default false, so a wire record
that is built without naming them asks for a full path at every opening. Here:
  `WireRB.setPr`                                  one round, with a flag for each of its two trees
  `RoundsQueryLayout.setPr`, `WireE.setPr`, `ProtocolQueryLayout.setPr`
      a wire record with its flags set from a list of numbers, one for each round (Iop/SerS.lean:
      `OpenList`): 0: false for both trees of the round; not 0: true for both; and one flag for the
      external trees
  `PrFlags`, `QueryLayout.setPr`   the same for the three protocols of an `BatchProtocol`
  `WireRB.OK.setPr`, .., `QueryLayout.OK.setPr`
      the conditions on a wire record do not mention the flags: a well-formed wire record stays
      well-formed
  `WireRB.OKG.setPr`, .., `QueryLayout.OKG.setPr`, `WireRB.gr0_setPr`, `WireRB.grJ_setPr`
      the same for a wire record whose rounds may have proof-of-work bits; the proof-of-work records
      are not changed
  All other fields are unchanged, by definition (rfl).
-/
import Iop.BatchWire
import Iop.SerS

namespace Iop

variable {lam K : ℕ}

def WireRB.setPr {r : Round} {a : RAnn r} (w : WireRB lam K r a) (b : Bool × Bool) :
    WireRB lam K r a :=
  { w with pr0 := b.1, prJ := b.2 }

def RoundsQueryLayout.setPr : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → OpenList s → RoundsQueryLayout lam K s A
  | [], _, _, _ => ()
  | _ :: s, (_, A), (w, W), (f, fs) =>
    (w.setPr (decide (f ≠ 0), decide (f ≠ 0)), RoundsQueryLayout.setPr s A W fs)

def WireE.setPr {E : ExtSpec} (we : WireE E) (b : Bool) : WireE E := { we with pr := b }

def ProtocolQueryLayout.setPr {X : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof X E} (wq : ProtocolQueryLayout lam K Q)
    (fl : OpenList Q.loc.shape) (e : Bool) : ProtocolQueryLayout lam K Q :=
  { wq with sh := RoundsQueryLayout.setPr Q.loc.shape Q.ann wq.sh fl, ext := wq.ext.setPr e }

/-- the flags of the three protocols: for each round of Test, Link and Batch; for their external
trees -/
structure PrFlags {I X : Type} (L : BatchProtocol I X) where
  T : OpenList L.offline.shape
  eT : Bool
  Lk : OpenList L.link.shape
  eL : Bool
  B : OpenList L.onlineBatch.loc.shape
  eB : Bool

def QueryLayout.setPr {I X : Type} {L : BatchProtocol I X} (W : QueryLayout lam L) (F : PrFlags L) : QueryLayout lam L :=
  { W with T := W.T.setPr F.T F.eT, Lk := W.Lk.setPr F.Lk F.eL, B := W.B.setPr F.B F.eB }

/-! ## Well-formedness is preserved -/

theorem WireRB.OK.setPr {r : Round} {a : RAnn r} {w : WireRB lam K r a}
    (h : w.OK) (b : Bool × Bool) : (w.setPr b).OK :=
  ⟨h.place_lt0, h.place_ltJ, h.posAt0_place, h.posAtJ_place, h.place_posAt0, h.place_posAtJ, h.no0,
    h.noJ, h.chal_unif, h.gr0_none, h.grJ_none⟩

theorem RoundsQueryLayout.OK.setPr :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (fl : OpenList s),
      RoundsQueryLayout.OK s A W → RoundsQueryLayout.OK s A (RoundsQueryLayout.setPr s A W fl)
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), (_, fs), h => ⟨h.1.setPr _, RoundsQueryLayout.OK.setPr s A W fs h.2⟩

theorem RoundsQueryLayout.DepthLe.setPr (d : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (fl : OpenList s),
      RoundsQueryLayout.DepthLe d s A W → RoundsQueryLayout.DepthLe d s A (RoundsQueryLayout.setPr s A W fl)
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), (_, fs), h => ⟨h.1, RoundsQueryLayout.DepthLe.setPr d s A W fs h.2⟩

theorem WireE.OK.setPr {E : ExtSpec} {we : WireE E} (h : we.OK) (b : Bool) : (we.setPr b).OK :=
  ⟨h.nodup, h.complete, h.build_rd⟩

theorem ProtocolQueryLayout.OK.setPr {X : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof X E} {wq : ProtocolQueryLayout lam K Q}
    (h : wq.OK) (fl : OpenList Q.loc.shape) (e : Bool) : (wq.setPr fl e).OK :=
  ⟨RoundsQueryLayout.OK.setPr _ _ _ _ h.sh, h.ext.setPr e, h.opens, RoundsQueryLayout.DepthLe.setPr _ _ _ _ _ h.depth⟩

theorem QueryLayout.OK.setPr {I X : Type} {L : BatchProtocol I X} {W : QueryLayout lam L} (h : W.OK) (F : PrFlags L) :
    (W.setPr F).OK :=
  ⟨h.T.setPr _ _, h.Lk.setPr _ _, h.B.setPr _ _, h.fits, h.slots, h.extDepth, h.depthT, h.depthL,
    h.depthB, h.extT, h.extB, h.extL⟩

/-! ## The same for a wire record whose rounds may have proof-of-work bits; their records do not
change -/

theorem WireRB.OKG.setPr {r : Round} {a : RAnn r} {w : WireRB lam K r a}
    (h : w.OKG) (b : Bool × Bool) : (w.setPr b).OKG :=
  ⟨h.place_lt0, h.place_ltJ, h.posAt0_place, h.posAtJ_place, h.place_posAt0, h.place_posAtJ, h.no0,
    h.noJ, h.chal_unif, h.gr0_ok, h.grJ_ok⟩

theorem WireRB.gr0_setPr {r : Round} {a : RAnn r} (w : WireRB lam K r a) (b : Bool × Bool) :
    (w.setPr b).gr0 = w.gr0 := rfl
theorem WireRB.grJ_setPr {r : Round} {a : RAnn r} (w : WireRB lam K r a) (b : Bool × Bool) :
    (w.setPr b).grJ = w.grJ := rfl

theorem RoundsQueryLayout.OKG.setPr :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (fl : OpenList s),
      RoundsQueryLayout.OKG s A W → RoundsQueryLayout.OKG s A (RoundsQueryLayout.setPr s A W fl)
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), (_, fs), h => ⟨h.1.setPr _, RoundsQueryLayout.OKG.setPr s A W fs h.2⟩

theorem ProtocolQueryLayout.OKG.setPr {X : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof X E} {wq : ProtocolQueryLayout lam K Q}
    (h : wq.OKG) (fl : OpenList Q.loc.shape) (e : Bool) : (wq.setPr fl e).OKG :=
  ⟨RoundsQueryLayout.OKG.setPr _ _ _ _ h.sh, h.ext.setPr e, h.opens, RoundsQueryLayout.DepthLe.setPr _ _ _ _ _ h.depth⟩

theorem QueryLayout.OKG.setPr {I X : Type} {L : BatchProtocol I X} {W : QueryLayout lam L} (h : W.OKG) (F : PrFlags L) :
    (W.setPr F).OKG :=
  ⟨h.T.setPr _ _, h.Lk.setPr _ _, h.B.setPr _ _, h.fits, h.slots, h.extDepth, h.depthT, h.depthL,
    h.depthB, h.extT, h.extB, h.extL⟩

end Iop
