-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/TotalAtGrind.lean: the hash term for one query bound (Compile/Batch/SpecTotalG.lean),
taken at `L.grind`, the record of protocols with proof-of-work bits (Iop/BatchGrind.lean), and at
its wire record `Wr.grind D` (Iop/GrindWire.lean). (Words of this library: lean/GLOSSARY.md.)

The terms of Compile/Batch/SpecTotalG.lean are taken at a wire record with proof-of-work bits. This
file ties `muB` and `xGr` to the L and Wr without such bits from which `L.grind` and `Wr.grind D`
are made.

  `muB_grind`   muB (Wr.grind D ..) p n = muB Wr p n: the part that is linear in t is that of the
                scheme without proof-of-work bits, at L and Wr (`xTree_grind`:
                Compile/Batch/CountsGrind.lean; `xFb_grind`)
  `xGr_grind`   what `xGr` (the searches of setup and n batches, at most:
                Compile/Batch/SpecTotalG.lean) is here. A round counts if it has b ≥ 1 proof-of-work
                bits and mo b ≥ 1 (a second attempt is allowed). Such a round of Test, and of each
                Link, counts one search over nonces; in each of the n batches, such a local round of
                Batch counts N and such a shared round one. Any other round counts none.

Notation: the hash term: `zetaHashBGTot` without its first summand: t * `muB` + `hashSqBG`
(Compile/Batch/SpecTotalG.lean); t, n: natural numbers: one bound of t queries, and n batches
(`zetaHashBGTot`); `W`: a type with a default element (`[Inhabited W]`): the type of nonces (the
head of Iop/Grind.lean); `D`: a `GrData W`: what the wire record adds to the numbers of
proof-of-work bits; `D.mo b`: in a round with b proof-of-work bits the honest prover tries the
nonces for 0, .., mo b: at most mo b + 1 attempts (Iop/GrindWire.lean); `gT`, `gL`, `gB`: `GBits` of
the shapes of Test, Link and Batch: for each round a number of proof-of-work bits (Iop/GBits.lean);
`p.leaves`: `p.M` + 1 (Compile/Spec.lean); `gSearch D k Ns`: searches of one execution with Ns slots
that can reach attempt k + 1 (counted from 0); `gSearchL`: the same for Test and Link: local rounds
only.

Limits: what the head of Compile/Batch/SpecTotalG.lean lists as not said is not said here either.
Nothing about any scheme. No number.
-/
import Compile.Batch.CountsGrind
import Compile.Batch.BindingG
import Compile.Batch.DisciplineChainAll
import Compile.Batch.EqBatch
import Compile.Batch.EqProve
import Compile.Batch.EqSetup
import Compile.Batch.GhostGuards
import Compile.Batch.GluePrivacy
import Compile.Batch.GrOK
import Compile.Batch.HopLate
import Compile.Batch.HopTot
import Compile.Batch.Late4
import Compile.Batch.LifeStar
import Compile.Batch.Lump
import Compile.Batch.OverrunGen
import Compile.Batch.WithinVCB

noncomputable section
namespace Compile.Batch
open Iop Rom Prob ZKCP
open scoped ENNReal

variable {W : Type} [Inhabited W] {lam K : ℕ}

/-- searches of one execution with Ns slots that can reach attempt k + 1 (counted from 0), read from
the list of the rounds' numbers of proof-of-work bits and the kinds of the rounds -/
def gSearch (D : GrData W) (k Ns : ℕ) : (s : Shape) → RoundSplits s → GBits s → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (b, g) =>
      (match a.kind, b with
        | _, 0 => 0
        | .lo, b + 1 => Ns * (if k < D.mo (b + 1) then 1 else 0)
        | .sh, b + 1 => (if k < D.mo (b + 1) then 1 else 0)) + gSearch D k Ns s A g

/-- `gSearch` for Test and Link: local rounds only -/
def gSearchL (D : GrData W) (k Ns : ℕ) : (s : Shape) → GBits s → ℕ
  | [], _ => 0
  | _ :: s, (b, g) =>
      (match b with
        | 0 => 0
        | b + 1 => Ns * (if k < D.mo (b + 1) then 1 else 0)) + gSearchL D k Ns s g

theorem cTry_grind (D : GrData W) (k Ns : ℕ) :
    ∀ {s : Shape} {A : RoundSplits s} (ws : RoundsQueryLayout lam K s A) (g : GBits s),
      cTry k Ns (s.grind W g) (A.grind W g) (RoundsQueryLayout.grind ws D g) = gSearch D k Ns s A g
  | [], _, _, _ => rfl
  | r :: _, (a, _), (w, ws), (b, g) => by
      show Ns * (if k < moreOf (grJOf D r.Chal a.Pj a.kind b) then 1 else 0) +
          (if k < moreOf (gr0Of D r.Chal a.P0 a.kind b) then 1 else 0) +
          cTry k Ns _ _ (RoundsQueryLayout.grind ws D g) = _
      have e : Ns * (if k < moreOf (grJOf D r.Chal a.Pj a.kind b) then 1 else 0) +
          (if k < moreOf (gr0Of D r.Chal a.P0 a.kind b) then 1 else 0)
          = (match a.kind, b with
            | _, 0 => 0
            | .lo, b + 1 => Ns * (if k < D.mo (b + 1) then 1 else 0)
            | .sh, b + 1 => (if k < D.mo (b + 1) then 1 else 0)) := by
        cases a.kind <;> cases b <;> simp [grJOf, gr0Of, moreOf, GrW.ofBits]
      rw [cTry_grind D k Ns ws g, e]
      rfl

theorem cTry_grindLocal (D : GrData W) (k Ns : ℕ) :
    ∀ {s : Shape} (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s)) (g : GBits s),
      cTry k Ns (s.grind W g) (RoundSplits.allLocal (s.grind W g)) (RoundsQueryLayout.grindLocal ws D g) =
        gSearchL D k Ns s g
  | [], _, _ => rfl
  | r :: _, (w, ws), (b, g) => by
      show Ns * (if k < moreOf (grOf D r.Chal r.Plain b) then 1 else 0) +
          (if k < moreOf (none : Option (GrW _ _)) then 1 else 0) +
          cTry k Ns _ _ (RoundsQueryLayout.grindLocal ws D g) = _
      have e : Ns * (if k < moreOf (grOf D r.Chal r.Plain b) then 1 else 0) +
          (if k < moreOf (none : Option (GrW (GChal b r.Chal) PUnit)) then 1 else 0)
          = (match b with
            | 0 => 0
            | b + 1 => Ns * (if k < D.mo (b + 1) then 1 else 0)) := by
        cases b <;> simp [grOf, moreOf, GrW.ofBits]
      have e0 : ∀ (C P : Type), moreOf (none : Option (GrW C P)) = 0 := fun _ _ => rfl
      rw [cTry_grindLocal D k Ns ws g, e0]
      rw [e0] at e
      rw [e]
      rfl

variable {I X : Type} {L : BatchProtocol I X}

/-- as many Fiat-Shamir queries, further attempts not counted, as for L: the rounds are as many -/
theorem xFb_grind (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
    (gB : GBits L.onlineBatch.loc.shape) (p : Params) (n : ℕ) :
    xFb (L := L.grind W gT gL gB) p n = xFb (L := L) p n := by
  show 2 * (L.offline.shape.grind W gT).length + p.leaves * (2 * (L.link.shape.grind W gL).length) +
      n * ((L.maxBatchSize + 1) * (L.onlineBatch.loc.shape.grind W gB).length) = _
  rw [Shape.grind_length, Shape.grind_length, Shape.grind_length]
  rfl

/-- The part that is linear in t is that of the scheme without proof-of-work bits, at L and Wr. -/
theorem muB_grind (Wr : QueryLayout lam L) (D : GrData W) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (p : Params) (n : ℕ) :
    muB (Wr.grind D gT gL gB) p n = muB Wr p n := by
  unfold muB
  rw [xTree_grind Wr D gT gL gB p n, xFb_grind]
  rfl

/-- What xGr is at `L.grind`: a round of Test, of each Link: one search; in each of the n batches, a
local round of Batch: N; a shared round: one; a round with b = 0 proof-of-work bits or with mo b = 0
(no second attempt is allowed): none. -/
theorem xGr_grind (Wr : QueryLayout lam L) (D : GrData W) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (p : Params) (n : ℕ) :
    xGr (Wr.grind D gT gL gB) p n =
      gSearchL D 0 1 L.offline.shape gT + p.leaves * gSearchL D 0 1 L.link.shape gL +
        n * gSearch D 0 L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann gB := by
  show cTry 0 1 _ _ (RoundsQueryLayout.grindLocal Wr.T.sh D gT) +
      p.leaves * cTry 0 1 _ _ (RoundsQueryLayout.grindLocal Wr.Lk.sh D gL) +
      n * cTry 0 L.maxBatchSize _ _ (RoundsQueryLayout.grind Wr.B.sh D gB) = _
  rw [cTry_grindLocal, cTry_grindLocal, cTry_grind]

end Compile.Batch
