-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPeelForB.lean.
The typed rounds of the sub-proofs' lookup, a reader a round, and the maps from a file's written
rounds to them.

OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean has a reader for each kind of typed round (Fo.Peel.Rd),
readers in a row (Rds), their
reading back of a typed transcript (outs), and the maps from written rounds that a row of readers
gives (car). This file lays the row of readers of the typed lookup Cb.Fo.forB, block for block as
its verifier is put together, at the spec Fo.specF h, and shows that the readers' reading back is
the reading Fo.forFl.

Main names:
  `Rk f sp`: a row of readers at the spec sp whose reading back is f.
  `Rk.seq`, `Rk.chain`, `Rk.draw`, `Rk.full`, `Rk.core`: the rules, one for each way in which the
    blocks are put together, as Tw.Un has them.
  `rkChn Ex A`: the lookup's chain. `rkAll`: with the shift's round in front, if there is one.
  `rkFor h L Ex` : Rk (forFl h L Ex) (specF h).
  `lookCarry h L Ex ds hl`: the maps from the written rounds ds, as many as the spec has, to the
    lookup's typed rounds: Fo.Peel.car at rkFor's readers.
  `lookCarry_read`: if each written round meets its spec and a written transcript τ has the image
    τ', then forFl h L Ex τ' is τ as plain data (flWs), these fit the spec round for round, no 0
    stands where a further variable's challenge stands (Fo.YNonZero), and every test of work has
    passed.
  `lookCarry_none`: a written transcript without an image has failed a test of work.
  `lookCarry_fits`: the written rounds' error counts bear the typed ones (Bears).
Under: List.Forall₂ Meets ds (specF h), a premise on the file's description of its rounds.
Does not say: that a description's rounds meet the spec; what the written plain data are in the
byte-level verifier's view.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelKit
import OnBytes.Tie.Pv.Lookup.Forest.FoMeet

set_option autoImplicit false

namespace Fo.Peel
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Johnson.L5.Layers
open OnBytes.Slice OnBytes.Flat Run

/-- A row of readers whose reading back is f. -/
structure Rk {s' : Shape} (f : Tr s' → Rounds GE) (sp : List RSp) where
  R : Rds s' sp
  read : ∀ τ, outs s' sp R τ = f τ

noncomputable section Rules
variable {X₁ X₂ X₃ : Type} {Ex : ExtSpec}

def Rk.seq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} {f : Fl GE a} {g : Fl GE b} {sa sb : List RSp}
    (u : Rk f sa) (v : Rk g sb) : Rk (fseq f g) (sa ++ sb) where
  R := Rds.app a.R.shape sa u.R v.R
  read := fun τ => by
    show outs (a.R.shape ++ b.R.shape) (sa ++ sb) (Rds.app a.R.shape sa u.R v.R) τ = _
    rw [outs_app, u.read, v.read]
    rfl

def Rk.chain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (f : ∀ l, Fl GE (b l))
    (sp : ℕ → List RSp) (u : ∀ l, Rk (f l) (sp l)) : ∀ n, Rk (fchain X b f n) (chainSp sp n)
  | 0 => u 0
  | n + 1 => Rk.seq (Rk.chain X b f sp u n) (u (n + 1))

def Rk.draw {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec)
    (err : ℕ) (dl : D → List GE) (k : ℕ) (mk : List GE → D)
    (h : ∀ l, l.length = k → dl (mk l) = l) : Rk (fdraw D nx Ex err dl) [⟨0, k, false⟩] where
  R := (show Rds [drawRound D] [⟨0, k, false⟩] from (Rd.draw dl k mk h, ()))
  read := fun _ => rfl

end Rules

/-! ### one short sumcheck -/

noncomputable section Sc

/-- The readers of a sumcheck's variables. -/
def rdsS : (l : List (PFmt GE)) → (sp : List RSp) → VFit l sp → Rds (sRounds l) sp
  | [], [], _ => ()
  | f :: l, s :: sp, hv =>
    (show Rd (sRound f) s × Rds (sRounds l) sp from (Rd.var f s hv.1, rdsS l sp hv.2))
  | [], _ :: _, hv => hv.elim
  | _ :: _, [], hv => hv.elim

theorem outs_S0 : ∀ (l : List (PFmt GE)) (sp : List RSp) (hv : VFit l sp) (τ : Tr (sRounds l)),
    outs (sRounds l) sp (rdsS l sp hv) τ = flS0 l τ
  | [], [], _, _ => rfl
  | f :: l, _ :: sp, hv, (m, c, τ) =>
    congrArg ((List.ofFn m.2, [f.val c]) :: ·) (outs_S0 l sp hv.2 τ)
  | [], _ :: _, hv, _ => hv.elim
  | _ :: _, [], hv, _ => hv.elim

theorem outs_S : ∀ (l : List (PFmt GE)) (sp : List RSp) (hv : VFit l sp) (t : Shape)
    (τ : Tr (sRounds l ++ t)),
    outs (sRounds l) sp (rdsS l sp hv) (Tr.fst (s := sRounds l) τ) = flS l t τ
  | [], [], _, _, _ => rfl
  | f :: l, _ :: sp, hv, t, (m, c, τ) =>
    congrArg ((List.ofFn m.2, [f.val c]) :: ·) (outs_S l sp hv.2 t τ)
  | [], _ :: _, hv, _, _ => hv.elim
  | _ :: _, [], hv, _, _ => hv.elim

variable (Ex : ExtSpec)

def Rk.full (Y : PscPar GE) (sh : List Y.A) (hn : sh.Nodup) (sp : List RSp) (hv : VFit Y.fmt sp) :
    Rk (flFull Ex Y sh) (⟨1, 1, false⟩ :: (sp ++ [⟨sh.length, 0, false⟩])) where
  R := (show Rds (shapeS Y) (⟨1, 1, false⟩ :: (sp ++ [⟨sh.length, 0, false⟩])) from
    (Rd.zero, Rds.app (sRounds Y.fmt) sp (rdsS Y.fmt sp hv)
      (show Rds [pRoundV GE Y.A] [⟨sh.length, 0, false⟩] from (Rd.vals sh hn, ()))))
  read := fun τ => by
    show (([τ.1.2], [τ.2.1]) : List GE × List GE) ::
      outs (sRounds Y.fmt ++ [pRoundV GE Y.A]) (sp ++ [⟨sh.length, 0, false⟩]) _ τ.2.2 = _
    rw [outs_app, outs_S]
    rfl

def Rk.core (Y : PscPar GE) (sp : List RSp) (hv : VFit Y.fmt sp) :
    Rk (flCore Ex Y) (⟨1, 1, false⟩ :: sp) where
  R := (show Rds (shapeSC Y) (⟨1, 1, false⟩ :: sp) from (Rd.zero, rdsS Y.fmt sp hv))
  read := fun τ => by
    show (([τ.1.2], [τ.2.1]) : List GE × List GE) :: outs (sRounds Y.fmt) sp _ τ.2.2 = _
    rw [outs_S0]
    rfl

end Sc

/-! ### the blocks -/

noncomputable section Blocks
variable (Ex : ExtSpec)

def rkStep (D : TieF GE) : (l : ℕ) → Rk (flStep Ex D l) (spStep l)
  | 0 => Rk.full Ex (D.lv 0).T.par (tieSh D 0) nd3 _ (vfit_cubes 0 3 0)
  | l + 1 => Rk.full Ex (D.lv (l + 1)).T.par (tieSh D (l + 1)) nd2 _ (vfit_cubes 0 3 0)

def rkTie (D : TieF GE) (n : ℕ) : Rk (flTie Ex D n) (chainSp spStep n) :=
  Rk.chain (fun l => GE × (D.lv l).T.St) (D.stepK (SK₀ GE Ex)) (flStep Ex D) spStep (rkStep Ex D) n

def rkHead (H : LkHeadF GE) : Rk (flHead Ex H) ([⟨0, 1, false⟩] ++ chainSp spStep H.n) :=
  Rk.seq (a := drawK GE (Prod.mk : H.St → GE → H.St × GE) Ex (2 ^ H.v - 1))
    (b := (H.tie.tieK (SK₀ GE Ex) H.n).preM fun x => ((0 : GE), x))
    (Rk.draw GE (Prod.mk : H.St → GE → H.St × GE) Ex (2 ^ H.v - 1) (fun β => [β]) 1
      (fun l => l.headD 0) fun l h => one_of_len l h)
    (rkTie Ex H.tie H.n)

def rkLine (D : TreeP GE) (l : ℕ) : Rk (flLine Ex D l) [⟨0, 1, false⟩] :=
  Rk.draw (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (D.cube l).toLine.toIn.ev.err
    (fun ρ : GE => [ρ]) 1 (fun l => l.headD 0) fun l h => one_of_len l h

def rkLvSc (D : TreeP GE) : (l : ℕ) →
    Rk (flFull Ex (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true]) (spSc (D.g + l) 2 2 2)
  | 0 => Rk.full Ex (D.lv 0).T.par [(D.lv 0).two false, (D.lv 0).two true] nd2 _
      (vfit_cubes 2 2 (D.g + 0))
  | l + 1 => Rk.full Ex (D.lv (l + 1)).T.par [(D.lv (l + 1)).two false, (D.lv (l + 1)).two true]
      nd2 _ (vfit_cubes 2 2 (D.g + l + 1))

def rkLev (D : TreeP GE) (l : ℕ) : Rk (flLev Ex D l) (spLev D.g l) :=
  Rk.seq (rkLvSc Ex D l) (rkLine Ex D l)

def rkTree (D : TreeP GE) (n : ℕ) : Rk (flTree Ex D n) (chainSp (spLev D.g) n) :=
  Rk.chain (fun l => GE × (D.lv l).T.St) (D.levK (SK₀ GE Ex)) (flLev Ex D) (spLev D.g)
    (rkLev Ex D) n

variable (A : LkAsmH GE)

def rkRoot : Rk (flRoot Ex A) [⟨0, A.w + 0, false⟩] :=
  Rk.draw A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.ev.err
    (fun ϱ : Fin (A.w + 0) → GE => List.ofFn ϱ) (A.w + 0) (fun l i => l.getD i.1 0)
    fun l h => ofFn_getD l _ h

def rkForest : (l : ℕ) → Rk (flForest Ex A l) (spForest A.v' A.w l)
  | 0 => rkTree Ex (A.IK.setV (A.v' + 1)).DK A.v'
  | l + 1 => Rk.seq (rkForest l) (rkLev Ex A.D l)

def rkEnd : Rk (flEnd Ex A)
    (⟨1, 1, false⟩ :: (List.ofFn (dgEnd A.w A.d A.oE)).map fun n => ⟨n, 1, false⟩) :=
  Rk.core Ex A.En.par _ (vfit_mix (A.w + A.d) (dgEnd A.w A.d A.oE))

def rkBit : Rk (flBit Ex A) ([⟨0, A.w + A.d, false⟩] ++ spSc (A.w + A.d) 2 2 1) :=
  Rk.seq (a := drawK A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.ev.err)
    (Rk.draw A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.ev.err (fun β => List.ofFn β.2)
      (A.w + A.d) (fun l => ((), fun i => l.getD i.1 0)) fun l h => ofFn_getD l _ h)
    (Rk.full Ex A.Bt.zc.next.par [()] nd1 _ (vfit_cubes 2 2 (A.w + A.d)))

/-- The readers of the lookup's chain. -/
def rkChn : Rk (flChn Ex A) (spChn A) :=
  Rk.seq (Rk.seq (Rk.seq (Rk.seq (rkHead Ex A.H) (rkRoot Ex A)) (rkForest Ex A A.d)) (rkEnd Ex A))
    (rkBit Ex A)

end Blocks

/-! ### the shift's round in front; the sub-proofs' lookup -/

noncomputable section All
variable {St : Type} (Ex : ExtSpec) (A0 : LkAsmH GE) (P : ShiftQ GE St (A0.J → GE))

/-- The readers of the whole lookup, the shift's round first if there is one. -/
def rkAll : (several : Bool) → Rk (flAll Ex A0 P several) (spShift several ++ spChn (P.asmH A0))
  | false => ⟨(rkChn Ex (P.asmH A0)).R, (rkChn Ex (P.asmH A0)).read⟩
  | true =>
    { R := (show Rds (drawRound GE :: ((P.asmH A0).chnK (SK₀ GE Ex)).R.shape)
          (⟨0, 1, false⟩ :: spChn (P.asmH A0)) from
        (Rd.draw (fun β : GE => [β]) 1 (fun l => l.headD 0) fun l h => one_of_len l h,
          (rkChn Ex (P.asmH A0)).R))
      read := fun τ => congrArg ((([] : List GE), [τ.2.1]) :: ·)
        ((rkChn Ex (P.asmH A0)).read τ.2.2) }

end All

noncomputable section For
open Cb.Fo
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh) (L : Lay GE St₀ J₀)
  (Ex : ExtSpec)

/-- The readers of the sub-proofs' lookup. -/
def rkFor : Rk (forFl h L Ex) (specF h) :=
  spec_forA h L ▸ (rkAll Ex (forA GE h L) (forP GE h L) (FoNums.several h) :
    Rk (forFl h L Ex) _)

/-- The maps from the written rounds ds to the lookup's typed rounds. -/
def lookCarry (ds : List PQ.RD) (hl : ds.length = (specF h).length) :
    CarryS (PQ.uL (ckP .two) ds) (forB GE h L V₀ V₀C (Ex := Ex)).R.shape :=
  car ds _ (specF h) (rkFor h L Ex).R hl

end For

theorem ynz_of_fit : ∀ {sp : List RSp} {rs : Rounds GE}, List.Forall₂ RFit sp rs →
    ∀ (i : ℕ) (x : GE), (sp.getD i ⟨0, 0, false⟩).nz = true → x ∈ (rs.getD i ([], [])).2 → x ≠ 0
  | _, _, .nil, _, _, h, _ => by simp at h
  | _, _, .cons h1 _, 0, x, h, hx => h1.2.2 (by simpa using h) x (by simpa using hx)
  | _, _, .cons _ h2, i + 1, x, h, hx => ynz_of_fit h2 i x (by simpa using h) (by simpa using hx)

section Laws
open Cb.Fo
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh) (L : Lay GE St₀ J₀)
  (Ex : ExtSpec) (ds : List PQ.RD)

/-- The image, read as plain data, is the written transcript's plain data. -/
theorem lookCarry_read (hM : List.Forall₂ Meets ds (specF h)) (τ : Tr (PQ.uL (ckP .two) ds))
    (τ' : Tr (forB GE h L V₀ V₀C (Ex := Ex)).R.shape)
    (e : (lookCarry h L Ex ds hM.length_eq).tr τ = some τ') :
    forFl h L Ex τ' = flWs ds τ ∧ List.Forall₂ RFit (specF h) (flWs ds τ) ∧
      YNonZero h (flWs ds τ) ∧ PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = true := by
  obtain ⟨h1, h2, h3⟩ := car_read ds _ (specF h) (rkFor h L Ex).R hM τ τ' e
  exact ⟨((rkFor h L Ex).read τ').symm.trans h1, h2, ynz_of_fit h2, h3⟩

/-- A written transcript without an image has failed a test of work. -/
theorem lookCarry_none (hl : ds.length = (specF h).length) (τ : Tr (PQ.uL (ckP .two) ds))
    (e : (lookCarry h L Ex ds hl).tr τ = none) :
    PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = false :=
  car_none ds _ (specF h) (rkFor h L Ex).R hl τ e

/-- The written rounds' error counts bear the typed ones. -/
theorem lookCarry_fits (hM : List.Forall₂ Meets ds (specF h))
    (ε : Err (forB GE h L V₀ V₀C (Ex := Ex)).R.shape) (ε' : Err (PQ.uL (ckP .two) ds))
    (hB : Bears ds _ ε ε') : (lookCarry h L Ex ds hM.length_eq).Fits ε ε' :=
  car_fits ds _ (specF h) (rkFor h L Ex).R hM ε ε' hB

end Laws

end Fo.Peel
