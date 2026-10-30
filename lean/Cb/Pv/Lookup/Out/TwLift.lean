-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwLift.lean.
A typed transcript of the lookup's chain for all plain data that fit, general in the lookup A.

Definitions and proofs.
Main names:
  `spChn A`: the chain's spec: a plain list of (scalars sent, elements drawn, must the drawn be
    other than 0), by recursion on A's numbers, with the closing's degrees by round (dgEnd).
  `unChn Ex A : Un (flChn Ex A) (spChn A)`: a right inverse of Tw.flChn, built as nested Tr.app in
    the nesting of LkAsmH.chnK (Un.seq, Un.chain: the same recursions as flChn's).
  `flChn_un`: List.Forall₂ RFit (spChn A) rs → flChn Ex A ((unChn Ex A).un rs) = rs.
Which scalar of a message is which is part of the reading flChn, and is fixed by its text
(Cb/Pv/Lookup/Out/TwFlat.lean; flS: Cb/Pv/Lookup/Out/TwSc.lean) and nowhere else; unS follows it. A
round's scalars are the coefficients of the powers 1, 2, .. in rising order (flS, unS); the shown
values stand in flChn's three lists (Tw3.tieSh: [none, some false, some true] or [false, true]; a
level: [two false, two true]; the bits: [()]), the same lists as in Tw3.traceOf.
Limits: at one filling of the sumchecks, `SK₀` (Cb/Pv/Lookup/Out/TwFill.lean). No statement here
ties these orders to the byte-level verifier.

-/
import Cb.Pv.Lookup.Out.TwUn

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Johnson.L5.Layers

noncomputable section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec)

theorem nd3 : ([none, some false, some true] : List (Option Bool)).Nodup := by decide
theorem nd2 : ([false, true] : List Bool).Nodup := by decide
theorem nd1 : ([()] : List Unit).Nodup := by decide

/-! ### the variables of a lookup's sumchecks -/

theorem vfit_dummy (D : ℕ) : VFit [pDummy E D] [⟨D, 1, true⟩] :=
  ⟨⟨rfl, rfl, fun x h => ⟨⟨x, h rfl⟩, rfl⟩⟩, trivial⟩

theorem vfit_cubes (n D : ℕ) : ∀ k : ℕ,
    VFit (List.replicate k (pfCube E n) ++ [pDummy E D]) (List.replicate k ⟨n, 1, false⟩ ++ [⟨D, 1,
        true⟩])
  | 0 => vfit_dummy D
  | k + 1 => ⟨⟨rfl, rfl, fun x _ => ⟨x, rfl⟩⟩, vfit_cubes n D k⟩

theorem vfit_mix : ∀ (k : ℕ) (dg : Fin k → ℕ), VFit (pfMix E k dg) ((List.ofFn dg).map fun n => ⟨n,
    1, false⟩)
  | 0, _ => trivial
  | k + 1, dg => by
    rw [List.ofFn_succ]
    exact ⟨⟨rfl, rfl, fun x _ => ⟨x, rfl⟩⟩, vfit_mix k fun i => dg i.succ⟩

/-! ### the specs -/

/-- a sumcheck with the further variable: round 0, k cube variables of degree n, the further
variable of degree D (its challenge is not 0), then a shown values -/
def spSc (k n D a : ℕ) : List RSp :=
  ⟨1, 1, false⟩ :: ((List.replicate k ⟨n, 1, false⟩ ++ [⟨D, 1, true⟩]) ++ [⟨a, 0, false⟩])
def spStep (l : ℕ) : List RSp := spSc 0 0 3 (if l = 0 then 3 else 2)
def spLev (g l : ℕ) : List RSp := spSc (g + l) 2 2 2 ++ [⟨0, 1, false⟩]
def spForest (v' w : ℕ) : ℕ → List RSp
  | 0 => chainSp (spLev 0) v'
  | l + 1 => spForest v' w l ++ spLev w l

/-- The chain's spec, from the numbers and the closing's degrees by round. -/
def spOf (v' d w n : ℕ) (dgE : List ℕ) : List RSp :=
  (((([⟨0, 1, false⟩] ++ chainSp spStep n) ++ [⟨0, w + 0, false⟩]) ++ spForest v' w d) ++
    (⟨1, 1, false⟩ :: dgE.map fun n => ⟨n, 1, false⟩)) ++ ([⟨0, w + d, false⟩] ++ spSc (w + d) 2 2
        1)

/-! ### the blocks -/

def unStep (D : TieF E) : (l : ℕ) → Un (flStep Ex D l) (spStep l)
  | 0 => Un.full Ex (D.lv 0).T.par (tieSh D 0) nd3 _ (vfit_cubes 0 3 0)
  | l + 1 => Un.full Ex (D.lv (l + 1)).T.par (tieSh D (l + 1)) nd2 _ (vfit_cubes 0 3 0)

def unTie (D : TieF E) (n : ℕ) : Un (flTie Ex D n) (chainSp spStep n) :=
  Un.chain (fun l => E × (D.lv l).T.St) (D.stepK (SK₀ E Ex)) (flStep Ex D) spStep (unStep Ex D) n

def unHead (H : LkHeadF E) : Un (flHead Ex H) ([⟨0, 1, false⟩] ++ chainSp spStep H.n) :=
  Un.seq (a := drawK E (Prod.mk : H.St → E → H.St × E) Ex (2 ^ H.v - 1))
    (b := (H.tie.tieK (SK₀ E Ex) H.n).preM fun x => ((0 : E), x))
    (Un.draw E (Prod.mk : H.St → E → H.St × E) Ex (2 ^ H.v - 1) (fun β => [β]) 1 (fun l => l.headD
        0) fun l h => one_of_len l h)
    (unTie Ex H.tie H.n)

def unLine (D : TreeP E) (l : ℕ) : Un (flLine Ex D l) [⟨0, 1, false⟩] :=
  Un.draw (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (D.cube l).toLine.toIn.ev.err
    (fun ρ : E => [ρ]) 1 (fun l => l.headD 0) fun l h => one_of_len l h

def unLvSc (D : TreeP E) : (l : ℕ) →
    Un (flFull Ex (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true]) (spSc (D.g + l) 2 2 2)
  | 0 => Un.full Ex (D.lv 0).T.par [(D.lv 0).two false, (D.lv 0).two true] nd2 _ (vfit_cubes 2 2
      (D.g + 0))
  | l + 1 => Un.full Ex (D.lv (l + 1)).T.par [(D.lv (l + 1)).two false, (D.lv (l + 1)).two true] nd2
      _
      (vfit_cubes 2 2 (D.g + l + 1))

def unLev (D : TreeP E) (l : ℕ) : Un (flLev Ex D l) (spLev D.g l) := Un.seq (unLvSc Ex D l) (unLine
    Ex D l)

def unTree (D : TreeP E) (n : ℕ) : Un (flTree Ex D n) (chainSp (spLev D.g) n) :=
  Un.chain (fun l => E × (D.lv l).T.St) (D.levK (SK₀ E Ex)) (flLev Ex D) (spLev D.g) (unLev Ex D) n

variable (A : LkAsmH E)

def unRoot : Un (flRoot Ex A) [⟨0, A.w + 0, false⟩] :=
  Un.draw A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.ev.err (fun ϱ : Fin (A.w + 0) → E => List.ofFn ϱ)
      (A.w + 0)
    (fun l i => l.getD i.1 0) fun l h => ofFn_getD l _ h

def unForest : (l : ℕ) → Un (flForest Ex A l) (spForest A.v' A.w l)
  | 0 => unTree Ex (A.IK.setV (A.v' + 1)).DK A.v'
  | l + 1 => Un.seq (unForest l) (unLev Ex A.D l)

def unEnd : Un (flEnd Ex A) (⟨1, 1, false⟩ :: (List.ofFn (dgEnd A.w A.d A.oE)).map fun n => ⟨n, 1,
    false⟩) :=
  Un.core Ex A.En.par _ (vfit_mix (A.w + A.d) (dgEnd A.w A.d A.oE))

def unBit : Un (flBit Ex A) ([⟨0, A.w + A.d, false⟩] ++ spSc (A.w + A.d) 2 2 1) :=
  Un.seq (a := drawK A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.ev.err)
    (Un.draw A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.ev.err (fun β => List.ofFn β.2) (A.w
        + A.d)
      (fun l => ((), fun i => l.getD i.1 0)) fun l h => ofFn_getD l _ h)
    (Un.full Ex A.Bt.zc.next.par [()] nd1 _ (vfit_cubes 2 2 (A.w + A.d)))

/-- the chain's spec at A -/
def spChn : List RSp := spOf A.v' A.d A.w A.n (List.ofFn (dgEnd A.w A.d A.oE))

/-- The right inverse of flChn. -/
def unChn : Un (flChn Ex A) (spChn A) :=
  Un.seq (Un.seq (Un.seq (Un.seq (unHead Ex A.H) (unRoot Ex A)) (unForest Ex A A.d)) (unEnd Ex A))
      (unBit Ex A)

/-- For all plain data that fit: the typed transcript un rs, read as plain data, is rs. -/
theorem flChn_un (rs : Rounds E) (h : List.Forall₂ RFit (spChn A) rs) : flChn Ex A ((unChn Ex A).un
    rs) = rs :=
  (unChn Ex A).inv rs h

end
end Tw

#print axioms Tw.nd3
#print axioms Tw.nd2
#print axioms Tw.nd1
#print axioms Tw.vfit_dummy
#print axioms Tw.vfit_cubes
#print axioms Tw.vfit_mix
#print axioms Tw.unChn
#print axioms Tw.flChn_un
