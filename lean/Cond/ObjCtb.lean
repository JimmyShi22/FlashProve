-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/ObjCtb.lean: countability of instances, symbols, positions and plain parts of an object with
records (`Ctb`), and the empty proof of work (`SubsR.noWk`).

Definitions.

Limits: "The two languages agree" is the model's duty, by reading and not by a theorem. This file
does not say that any object meets `Ctb`.

Terms: lean/GLOSSARY.md.
-/
import Cond.ObjBitsProof
import CompileK.WideZero
import Hiop.KnowWideRecompute
import CompileK.WideLang
import CompileK.KnowWidePass
import CompileK.Recompute
import CompileK.KnowLocal
import CompileK.FitExists
import CompileK.ImplExists
import CompileK.ImplCountable

set_option autoImplicit false

noncomputable section

namespace Hiop

/-- No proof of work. -/
abbrev SubsR.noWk {C : ConfigurationWithOutOfDomainSample} (S : SubsR C) (r : C.Rec) :
    Option (Compile.Batch.Work Unit (S.obj r)) :=
  SubsR.wkAt r (none : Option (S.Wk Unit))

end Hiop

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open Compile.BatchLife (Sims)
open scoped ENNReal

/-- Instances, symbols, positions and plain parts are countable. -/
structure Ctb {C : ConfigurationWithOutOfDomainSample} (S : SubsR C) (r : C.Rec) : Prop where
  inst : Countable C.X
  sym  : Countable (S.obj r).Symbol
  test : CtbSh (S.obj r).offline.shape
  link : CtbSh (S.obj r).link.shape
  bat  : CtbS (S.obj r).onlineBatch.loc.shape (S.obj r).onlineBatch.ann

end TopC
