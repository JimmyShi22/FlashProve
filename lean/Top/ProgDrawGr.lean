-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/ProgDrawGr.lean: the record of protocols with proof-of-work bits ("grinding") and its
  wire records, for any record of protocols.

  Data: for `L`: `IsPoint` records, numbers of opened positions, samplers `dr`, further data `ax`;
  and: a type `Wn` of nonces; the data `Dg` of the search (at most Dg.mo b + 1 attempts in a round
  with b bits; how a number is encoded as a nonce); three lists gT, gL, gB of numbers of
  proof-of-work bits.
    `LBdG`, `WBdG`, `WPBdG`:
        `(LBd lam L dr).grind Wn gT gL gB`: first challenges from hash blocks, then the
        proof-of-work bits (from a separate block); its wire records (Iop/GrindWire.lean).
  At lists of zeros the wire record is not the one without proof-of-work bits: it has one block more
  (Iop/GrindWire.lean).
  What proof-of-work bits mean for a round's error, and what is counted: the header of
  Compile/Batch/SpecGrind.lean. (Terms: lean/GLOSSARY.md.)

  Limits: Three definitions. This file defines no scheme and states no theorem. No statement here is
  a security level.
-/
import Top.ProgDraw
import Compile.Batch.SimsGrind
import Compile.Batch.FitGrind
import Iop.GrindData
import Compile.Batch.CompleteUMainG
import Compile.Batch.StepSGr

noncomputable section

namespace Top.ProgDraw
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.Prog
open Compile.BatchLife (Sims)
open Compile.Seed (blocksStd)
open scoped ENNReal

variable {I X : Type} (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
  (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
  (dr : L.Draws lam) (ax : L.Aux pT pL pB) (p : Params) (D : SerLHB L) {Wn : Type} [Inhabited Wn]
  (Dg : GrData Wn) (sW : Ser Wn) (gT : GBits (LBd lam L dr).offline.shape)
  (gL : GBits (LBd lam L dr).link.shape) (gB : GBits (LBd lam L dr).onlineBatch.loc.shape)

/-- The record: challenges from hash blocks, then the proof-of-work bits; then its wire records. -/
abbrev LBdG : BatchProtocol I X := (LBd lam L dr).grind Wn gT gL gB
abbrev WBdG : QueryLayout lam (LBdG lam L dr (Wn := Wn) gT gL gB) :=
  (WBd lam L pT pL pB z no dr ax).grind Dg gT gL gB
abbrev WPBdG : WireBP (LBdG lam L dr (Wn := Wn) gT gL gB) :=
  (WPBd lam L pT pL pB dr ax).grind gT gL gB



variable {Ryes Rno : I → X → Prop} {M : LH.Nums} {κ₀ : ℝ≥0∞} {n nb : ℕ} {εs' : ℝ≥0∞}


variable {Sim : Gen.Simulator
    (Compile.Batch.spec lam (WBdG lam L pT pL pB z no dr ax Dg gT gL gB).K
      (LBdG lam L dr (Wn := Wn) gT gL gB))
    Unit (IVKK lam (LBdG lam L dr (Wn := Wn) gT gL gB)) X
    (PrfK lam (LBdG lam L dr (Wn := Wn) gT gL gB))}
  {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞}


end Top.ProgDraw
