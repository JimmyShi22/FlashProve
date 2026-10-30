-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecPubGr.lean: the simulator of the compiled scheme over typed oracles with the
entries in the verification key, for wire records with or without proof-of-work bits, as an explicit
term. Two definitions; no statement. (Words of this library: lean/GLOSSARY.md.)

  `simBPGr`   for a scheme that publishes a function pw of the verification key and of what the
              reduction keeps of the proving key (Compile/Batch/PubChall.lean): the reduction of
              Compile/Batch/PubWr.lean (`WrBP`, `iniBP`) around the lifetime experiment on encodings
              of the fixed index i₀ with simulated sessions Sm (Compile/Batch/SpecLifeStar.lean:
              `simWorldB`), its oracle answers read through the exchange of queries (`World.pre` at
              `ghost W`, Compile/Batch/SpecGhost.lean: a later attempt's query ↔ the same under its
              ghost name)
  `simBKGr`   the case that the entries go into the key (pw = the key with `linksOf`,
              Compile/Batch/StarK.lean), followed by the removal of the two fields from each proof
              (`pushSim stripK`)

By its type the simulator is given neither the index nor, of a batch, anything but the adversary's
own requests (`GlueB.SCall`).

`simBKGr` is the simulator named in the theorems on the scheme `argBKE` over typed oracles
(Compile/Batch/PubProgMainBGr.lean, Compile/Batch/MainKEGr.lean).

Notation: the entries: `Links` (Compile/Batch/StarK.lean): "the published entries: for each copy the
root of its tree and Link's proof string"; the two fields: `cm` and `piL` of a `Prf` (`stripK`,
Compile/Batch/StarK.lean: "take the fields cm and piL out of a proof"); `Sm`: a `Sims L`
(Compile/Batch/SpecLife.lean); `pw`: of type `IVK lam L → WKey lam L → V`; `V`: a type: that of the
values of `pw`; `WKey`: Compile/Batch/Mirror.lean.

Limits: nothing is proved here. A named term, not a program: nothing about whether it can be run. t
in `zetaBGTot` (Compile/Batch/SpecTotalG.lean; it is `zetaBGen L p M h` of the section below at h =
`hashTermsBGTot W p`: `zetaBGTot_eq_gen`, Compile/Batch/HopTot.lean) is the adversary's number of
all queries; the hash term counts every attempt (`xFbG`).
-/
import Compile.Batch.SpecGrind
import Compile.Batch.SpecHop
import Compile.Batch.GhostGuards
import Compile.Batch.PubWr
import Compile.Batch.StarK

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile.GenMap Compile.GenPub
open Compile.GlueB (GCall SCall GAdm asW realW simOf viaCP Close)
open Compile.BatchLife (LifeB Sims simWorldB)
open scoped ENNReal

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}


/-- The simulator, as an explicit term. It is given neither the index nor, of a batch, anything but
the adversary's own requests (by type: GlueB.SCall). -/
def simBPGr [Inhabited V] (W : QueryLayout lam L) (p : Params) (pw : IVK lam L → WKey lam L → V)
    (Sm : Sims L) (i₀ : I) :
    Gen.Simulator (spec lam W.K L) Unit V X (Prf lam L) :=
  simOf Unit ((WrBP W p pw (simWorldB _ L p.leaves Sm i₀)).pre (ghost W))
    (iniBP W p pw _ (none, Table.empty _))


/-- the simulator for the scheme with the entries in the key: simBPGr, followed by the removal of
the two fields from each proof -/
def simBKGr (W : QueryLayout lam L) (p : Params) (Sm : Sims L) (i₀ : I) :
    Gen.Simulator (spec lam W.K L) Unit (IVKK lam L) X (PrfK lam L) :=
  pushSim stripK (simBPGr W p (fun v key => (v, linksOf key)) Sm i₀)

/-! ## Generic in the bound of the game hop of deferred programming

This library has no statement under this title. A theorem with zetaBGen L p M h is in
Compile/Batch/PubProgMainBGr.lean.

What the title means: the sequence of experiments has one hop whose bound depends on how the lemma
on deferred programming is applied. h is any bound for it at the counts of the scheme (HopB W p h:
Compile/Batch/SpecHop.lean); ζ is zetaBGen L p M h: the overrun term + h t n + the terms of L. -/




end Compile.Batch
