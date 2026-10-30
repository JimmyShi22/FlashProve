-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupData.lean: numberings (of verifier messages, vectors and plain parts: `SNum`,
Blocks/StageData.lean) and decision procedures for the rounds of the lookup argument.

This file gives `Core.Data` (Blocks/StageData.lean) for the lookup argument, which sends no vector.
Its rounds are: challenges, masked scalars followed by a point, product layers, one masked sumcheck.
Withheld are the points ϱ, ϱ3, ϱ5, ϱ' with a coordinate 0 and the challenges of product layers that
fail their public check; both are decided by the checks that the verifier itself runs (the withheld
sets: `Hon.withheld`, Blocks/BlockHon.lean). The names are those of Blocks/LookupBlock.lean.

Notation: `Core.Data` C t: the data of a protocol with its track: the numberings of its rounds, and
the decision procedures of its honest side (Blocks/StageData.lean); `Hon.Dec` H: decision procedures
for the public bad set and for the rest of the withheld set of an honest side
(Blocks/StageData.lean); `Hon.withheld` H a: `Set (Rho B.shape)`: `H.Bad ∪ H.Win a`: the withheld
set; `Hon.Bad`: the public bad set; `Hon.Win`: the rest of the withheld set (Blocks/BlockHon.lean).
-/
import Blocks.LookupStage
import Blocks.StageData
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks.Lk
open Iop

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N) (F : Type) [Field F]
  [Algebra F E] [FinEnum E]

/-! ## Numberings -/

def numKey : (n l : ℕ) → SNum (L.coKey n l).B.shape (L.encKey F n l)
  | 0, _ => ()
  | n + 1, l =>
    SNum.app (s := (L.coK l).B.shape) (d := encPl F (L.plK l))
      (PL.Prover.numPl F (L.plK l)) (numKey n (l + 1))

def numTab : (n l : ℕ) → SNum (L.coTab n l).B.shape (L.encTab F n l)
  | 0, _ => ()
  | n + 1, l =>
    SNum.app (s := (L.coT l).B.shape) (d := encPl F (L.plT l))
      (PL.Prover.numPl F (L.plT l)) (numTab n (l + 1))

def num14 : SNum L.co14.B.shape (L.enc14 F) :=
  SNum.app (s := L.coAl.B.shape)
      (d := (REnc.none E F Empty E, PUnit.unit)) (RNum.none F Empty E, ()) <|
  SNum.app (s := L.coZY.B.shape) (d := (REnc.none E F L.KZY (Fin L.par.σ → E), PUnit.unit))
      (RNum.none F L.KZY (Fin L.par.σ → E), ()) <|
  SNum.app (s := (L.coKey L.par.D 0).B.shape) (L.numKey F _ _) <|
  SNum.app (s := L.coKe.B.shape) (d := PUnit.unit) () <|
  SNum.app (s := L.coT0.B.shape)
      (d := (REnc.none E F Empty (Fin (L.par.σ + L.par.lp) → E), PUnit.unit))
      (RNum.none F Empty (Fin (L.par.σ + L.par.lp) → E), ()) <|
  SNum.app (s := (L.coTab L.par.r 0).B.shape) (L.numTab F _ _) <|
  SNum.app (s := L.coL.B.shape) (d := encPl F L.plL) (PL.Prover.numPl F L.plL) <|
  SNum.app (s := L.coB0.B.shape) (t := L.coB.B.shape)
    (d := (REnc.none E F Empty (Fin L.par.gT → E), PUnit.unit)) (d' := encPl F L.plB)
    (RNum.none F Empty (Fin L.par.gT → E), ()) (PL.Prover.numPl F L.plB)

def num5 : SNum L.co5.B.shape (L.enc5 F) := (RNum.none F Empty (Fin L.par.σ → E), ())

def num6 : SNum L.co6.B.shape (L.enc6 F) :=
  SNum.app (s := L.coUV.B.shape) (d := (REnc.none E F L.KUV (Fin L.par.σ → E), PUnit.unit))
      (RNum.none F L.KUV (Fin L.par.σ → E), ()) <|
  SNum.app (s := L.coXi.B.shape) (d := (REnc.none E F Empty (Fin (2 * L.par.Pm) → E), PUnit.unit))
      (RNum.none F Empty (Fin (2 * L.par.Pm) → E), ()) <|
  SNum.app (s := L.coRs.B.shape) (t := L.coRec.B.shape) (d := SC.encSc L.scR F (lkVars L.par.σ))
    (d' := PUnit.unit) (SC.numSc L.scR (lkVars L.par.σ)) ()

/-! ## Decision procedures -/

def decKey : (n l : ℕ) → (L.coKey n l).H.Dec
  | 0, _ => Hon.Dec.pure _ _ _
  | n + 1, l =>
    Hon.Dec.seq (H₁ := L.hK l) (H₂ := (L.coKey n (l + 1)).H)
      ((L.prK l).decPl.on _ _ _ _ _ _) (decKey n (l + 1))

def decTab : (n l : ℕ) → (L.coTab n l).H.Dec
  | 0, _ => Hon.Dec.pure _ _ _
  | n + 1, l =>
    Hon.Dec.seq (H₁ := L.hT l) (H₂ := (L.coTab n (l + 1)).H)
      ((L.prT l).decPl.on _ _ _ _ _ _) (decTab n (l + 1))

def decAl : L.hAl.Dec := Hon.Dec.oneEmpty _ _
def decZY : L.hZY.Dec :=
  Hon.Dec.one _ _ _ _ (fun ϱ => inferInstanceAs (Decidable (nzT ϱ = false))) fun _ _ =>
    isFalse fun h => h
def decKe : L.hKe.Dec := Hon.Dec.pure _ _ _
def decT0 : L.hT0.Dec :=
  Hon.Dec.one _ _ _ _ (fun ϱ => inferInstanceAs (Decidable (nzT ϱ = false))) fun _ _ =>
    isFalse fun h => h
def decL : L.hL.Dec := L.prL.decPl.on _ _ _ _ _ _
def decB0 : L.hB0.Dec :=
  Hon.Dec.one _ _ _ _ (fun ϱ => inferInstanceAs (Decidable (nzT ϱ = false))) fun _ _ =>
    isFalse fun h => h
def decB : L.hB.Dec := L.prB.decPl.on _ _ _ _ _ _
def decDeg : L.hDeg.Dec := Hon.Dec.oneEmpty _ _
def decUV : L.hUV.Dec :=
  Hon.Dec.one _ _ _ _ (fun ϱ => inferInstanceAs (Decidable (nzT ϱ = false))) fun _ _ =>
    isFalse fun h => h
def decXi : L.hXi.Dec := Hon.Dec.oneEmpty _ _
def decRs : L.hRs.Dec := (L.prR.decSc (lkVars L.par.σ) []).on _ _ _ _ _ _
def decRec : L.hRec.Dec := Hon.Dec.pure _ _ _

def dec14 : L.co14.H.Dec :=
  Hon.Dec.seq (H₁ := L.hAl) L.decAl <|
  Hon.Dec.seq (H₁ := L.hZY) L.decZY <|
  Hon.Dec.seq (H₁ := (L.coKey L.par.D 0).H) (L.decKey _ _) <|
  Hon.Dec.seq (H₁ := L.hKe) L.decKe <|
  Hon.Dec.seq (H₁ := L.hT0) L.decT0 <|
  Hon.Dec.seq (H₁ := (L.coTab L.par.r 0).H) (L.decTab _ _) <|
  Hon.Dec.seq (H₁ := L.hL) L.decL <|
  Hon.Dec.seq (H₁ := L.hB0) (H₂ := L.hB) L.decB0 L.decB

def dec6 : L.co6.H.Dec :=
  Hon.Dec.seq (H₁ := L.hUV) L.decUV <|
  Hon.Dec.seq (H₁ := L.hXi) L.decXi <|
  Hon.Dec.seq (H₁ := L.hRs) (H₂ := L.hRec) L.decRs L.decRec

/-! ## The three phases and the whole argument -/

def data14 (ra : Reads F E L.sL) : L.co14.Data (L.tk14 F ra) := ⟨L.num14 F, L.dec14⟩
def data5 (ra : Reads F E L.sX) : L.co5.Data (L.tk5 F ra) := ⟨L.num5 F, L.decDeg⟩
def data6 (ra : Reads F E L.sX) : L.co6.Data (L.tk6 F ra) := ⟨L.num6 F, L.dec6⟩

/-- The data of the lookup argument. -/
def dataLookup (ra : Reads F E L.sL) : L.coLookup.Data (L.tkLookup F ra) where
  num := SNum.app (s := L.co14.B.shape) (L.num14 F)
    (SNum.app (s := L.co5.B.shape) (t := L.co6.B.shape) (L.num5 F) (L.num6 F))
  dec := Hon.Dec.seq (H₁ := L.co14.H) L.dec14
    (Hon.Dec.seq (H₁ := L.co5.H) (H₂ := L.co6.H) L.decDeg L.dec6)

end Blocks.Lk
