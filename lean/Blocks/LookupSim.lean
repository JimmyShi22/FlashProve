-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupSim.lean: the lookup argument as protocols with their simulators, and nothing else.

X is the ending of a name. For each stage stX of Blocks/LookupStage.lean, Blocks/LookupSplit.lean,
Blocks/LookupWhole.lean, except `Lk.stT`, this file has Lk.csX (a `CS`, Blocks/StageSim.lean), with
the arguments of Lk.coX, and, by `rfl`, two equations: Lk.toCore_csX : L.csX.toCore = L.coX and
Lk.toCS_stX : L.stX.toCS = L.csX. A rider (Blocks/LookupRider.lean) changes errors only:
`Lk.toCS_stLookupR` holds for all σ, d with the one `Lk.csLookupR`. All simulators sample
independent uniform scalars; rounds with a challenge only have the empty plain part.

Notation:
 * `CS` P E a b: a protocol with its simulator: a `Core` with `Sim` (Blocks/StageSim.lean); `Core`:
   the protocol of a stage: a block and its honest prover (Blocks/Stage.lean); `toCore`: the `Core`
   of a `CS` or a `Stage`; `Stage.toCS`: the protocol and the simulator of a stage.
 * the endings Al, ZY, K, Ke, T0, T, L, B0, B, UV, Xi, Rs, Rec: those of the blocks `bAl`, ..,
   `bRec` (the head of Blocks/LookupBlock.lean); 14a, Last, 14b: the head of
   Blocks/LookupSplit.lean.
 * steps 1 to 4, 5, 6: the stages `Lk.st14`, `Lk.st5` (the degree check), `Lk.st6` (the root test)
   (Blocks/LookupStage.lean; the head of Blocks/LookupBlock.lean).
 * E, Y, Pd, N: types, the arguments of `Lk`: E the field; Y the implicit part; Pd the set of places
   of pads; N the set of entries (Blocks/LookupBlock.lean).
 * σ, d: `Fin n → ℕ`, the arguments of `Lk.stLookupR` (the head of Blocks/LookupWhole.lean).

Limits: what the head of Blocks/StageSim.lean lists as not said is not said here either.
-/
import Blocks.LookupWhole
import Blocks.ClosingStage
import Blocks.StageBatched
import Blocks.StageSim
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks.Lk

open Iop Prob

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N)

/-! ## The steps -/

def csAl : CS Pd E L.sL L.sX := ⟨L.coAl, simNone E⟩
def csZY : CS Pd E L.sX L.sX := ⟨L.coZY, Hon.simOne (r := L.rZY) (K := L.KZY) E id⟩
def csKe : CS Pd E L.sX L.sX := ⟨L.coKe, fun _ => PMF.pure ()⟩
def csT0 : CS Pd E L.sX L.sX := ⟨L.coT0, simNone _⟩
def csL : CS Pd E L.sX L.sX := ⟨L.coL, PL.Prover.simPl L.plL⟩
def csB0 : CS Pd E L.sX L.sX := ⟨L.coB0, simNone _⟩
def csB : CS Pd E L.sX L.sX := ⟨L.coB, PL.Prover.simPl L.plB⟩
def cs5 : CS Pd E L.sX L.sX := ⟨L.co5, simNone _⟩
def csUV : CS Pd E L.sX L.sX := ⟨L.coUV, Hon.simOne (r := L.rUV) (K := L.KUV) E id⟩
def csXi : CS Pd E L.sX L.sX := ⟨L.coXi, simNone _⟩
def csRs : CS Pd E L.sX L.sX := ⟨L.coRs, L.scR.simSc (lkVars L.par.σ)⟩
def csRec : CS Pd E L.sX L.sX := ⟨L.coRec, fun _ => PMF.pure ()⟩
def csK (l : ℕ) : CS Pd E L.sX L.sX := ⟨L.coK l, PL.Prover.simPl (L.plK l)⟩
/-- the layers l, .., l + n - 1 of the key side, of the table side -/
def csKey (n l : ℕ) : CS Pd E L.sX L.sX := ⟨L.coKey n l, L.simKey n l⟩
def csTab (n l : ℕ) : CS Pd E L.sX L.sX := ⟨L.coTab n l, L.simTab n l⟩

omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csAl : L.csAl.toCore = L.coAl := rfl
omit [NeZero (2 : E)] [Fintype N] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csZY : L.csZY.toCore = L.coZY := rfl
omit [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
omit [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csKe : L.csKe.toCore = L.coKe := rfl
omit [NeZero (2 : E)] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csT0 : L.csT0.toCore = L.coT0 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csL : L.csL.toCore = L.coL := rfl
omit [NeZero (2 : E)] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csB0 : L.csB0.toCore = L.coB0 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csB : L.csB.toCore = L.coB := rfl
omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_cs5 : L.cs5.toCore = L.co5 := rfl
omit [NeZero (2 : E)] [Fintype N] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csUV : L.csUV.toCore = L.coUV := rfl
omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csXi : L.csXi.toCore = L.coXi := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csRs : L.csRs.toCore = L.coRs := rfl
omit [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]
  [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csRec : L.csRec.toCore = L.coRec := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csK (l : ℕ) : (L.csK l).toCore = L.coK l := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csKey (n l : ℕ) : (L.csKey n l).toCore = L.coKey n l := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csTab (n l : ℕ) : (L.csTab n l).toCore = L.coTab n l := rfl

omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stAl : L.stAl.toCS = L.csAl := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stZY : L.stZY.toCS = L.csZY := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
omit [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem toCS_stKe : L.stKe.toCS = L.csKe := rfl
omit [NeZero (2 : E)] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stT0 : L.stT0.toCS = L.csT0 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stL : L.stL.toCS = L.csL := rfl
omit [NeZero (2 : E)] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stB0 : L.stB0.toCS = L.csB0 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stB : L.stB.toCS = L.csB := rfl
omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_st5 : L.st5.toCS = L.cs5 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stUV : L.stUV.toCS = L.csUV := rfl
omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stXi : L.stXi.toCS = L.csXi := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stRs : L.stRs.toCS = L.csRs := rfl
omit [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]
  [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stRec : L.stRec.toCS = L.csRec := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stK (l : ℕ) : (L.stK l).toCS = L.csK l := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stKey (n l : ℕ) : (L.stKey n l).toCS = L.csKey n l := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stTab (n l : ℕ) : (L.stTab n l).toCS = L.csTab n l := rfl

/-! ## Steps 1 to 4, step 6, the whole -/

def cs14 : CS Pd E L.sL L.sX :=
  L.csAl.seq
    (L.csZY.seq
      ((L.csKey L.par.D 0).seq
        (L.csKe.seq (L.csT0.seq ((L.csTab L.par.r 0).seq (L.csL.seq (L.csB0.seq L.csB)))))))
def cs6 : CS Pd E L.sX L.sX := L.csUV.seq (L.csXi.seq (L.csRs.seq L.csRec))
/-- The lookup argument. -/
def csLookup : CS Pd E L.sL L.sX := L.cs14.seq (L.cs5.seq L.cs6)

omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_cs14 : L.cs14.toCore = L.co14 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_cs6 : L.cs6.toCore = L.co6 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csLookup : L.csLookup.toCore = L.coLookup := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_st14 : L.st14.toCS = L.cs14 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_st6 : L.st6.toCS = L.cs6 := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stLookup : L.stLookup.toCS = L.csLookup := rfl

/-! ## The split form, and the whole with a rider -/

def cs14a : CS Pd E L.sL L.sX := L.csAl.seq (L.csZY.seq (L.csKey (L.par.D - 1) 0))
def csLast : CS Pd E L.sX L.sX := L.csK (L.par.D - 1)
def cs14b : CS Pd E L.sX L.sX :=
  L.csKe.seq (L.csT0.seq ((L.csTab L.par.r 0).seq (L.csL.seq (L.csB0.seq L.csB))))
/-- steps 1 to 4 in three parts -/
def cs14r : CS Pd E L.sL L.sX := L.cs14a.seq (L.csLast.seq L.cs14b)
/-- The lookup argument with a rider. -/
def csLookupR : CS Pd E L.sL L.sX :=
  L.cs14a.seq (L.csLast.seq (L.cs14b.seq (L.cs5.seq L.cs6)))

omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_cs14a : L.cs14a.toCore = L.co14a := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csLast : L.csLast.toCore = L.coLast := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_cs14b : L.cs14b.toCore = L.co14b := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCore_csLookupR : L.csLookupR.toCore = L.coLookupR := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_st14a : L.st14a.toCS = L.cs14a := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stLast : L.stLast.toCS = L.csLast := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_st14b : L.st14b.toCS = L.cs14b := rfl
omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
theorem toCS_stLookupR {n : ℕ} (σ d : Fin n → ℕ) : (L.stLookupR σ d).toCS = L.csLookupR := rfl

end Blocks.Lk
