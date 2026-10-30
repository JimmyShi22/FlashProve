-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyConfM.lean: a small test instance of a configuration (a code with encoder, the format
of the encoded index, and a model) in which the model's instances, cells and two relations are a
parameter.

Definitions, statements (`Cb.Gl.Spec.toyCf8M_same` and its like) and proofs. No parameter of a
protocol.
It is built on `toyCf8` of Cb/GlVal/GlToyConf.lean (F the integers modulo p = 2^64 - 2^32 + 1:
entries of index messages; E = F[x] / (x^3 - 2): all that is read). The analogue over one field with
101 elements: Cb/Obj/LdObjectToyConf7M.lean.

Why: a request that claims something cannot start at a configuration whose cells are `Unit` (head of
Cb/Obj/LdObjectToyConf7M.lean).

Main names:
  `ToyMd I`: the data: instances `Xm`, cells, `Ryes`, `Rno`, `trace`, a fixed value of the cells.
    Nothing in it names a field: over which field cells lie is the instance's matter.
  `toyCf8M Mo Md`: `toyCf8 Mo` with these put in. Code, format, index set, encoder, decoder, record
    are those of `toyCf8 Mo`, by definition (`Spec.toyCf8M_same` states it of `conf.E0`, `conf.Msg`,
    `conf.Rec`, `conf.PIdx`, `conf.I` and `X`).
  `Md.OK`: its fields: `Ryes` gives `Rno`; `Ryes` of some cells gives `Ryes` of the trace.
  `Spec.toyCf8M_third`, `Spec.toyCf8M_ok`: `(toyCf8M Mo Md).Third` and
    `(toyCf8M Mo Md).OK 1` from `Md.OK`.

Of the clauses on the configuration none needs F = E.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyConf

set_option autoImplicit false

namespace Cb.Gl
open Iop Prob Hiop Blocks Cb.Ood

/-- The relation pair of a toy: the data. -/
structure ToyMd (I : Type) where
  Xm     : Type
  Cells  : Type
  Ryes   : I → Xm → Cells → Prop
  Rno    : I → Xm → Cells → Prop
  trace  : I → Xm → Cells
  cells0 : Cells

/-- The trivial one. -/
def ToyMd.triv (I : Type) : ToyMd I :=
  ⟨Unit, Unit, fun _ _ _ => True, fun _ _ _ => True, fun _ _ => (), ()⟩

structure ToyMd.OK {I : Type} (Md : ToyMd I) : Prop where
  sub    : ∀ i x w, Md.Ryes i x w → Md.Rno i x w
  admits : ∀ i x w, Md.Ryes i x w → Md.Ryes i x (Md.trace i x)

/-- The toy configuration with a relation pair. -/
def toyCf8M (Mo : ToyMo8) (Md : ToyMd Mo.I) : LdCf F E :=
  { toyCf8 Mo with
    Xm := Md.Xm, Cells := Md.Cells, Ryes := Md.Ryes, Rno := Md.Rno,
    trace := Md.trace, cells0 := Md.cells0 }

instance neN8M (Mo : ToyMo8) (Md : ToyMd Mo.I) : Nonempty (Fin (toyCf8M Mo Md).C₀.n) := neN8 Mo

namespace Spec

/-- Code, format, index set, encoder, decoder, record: those of `toyCf8 Mo`. (Stated of the parts
named below.) -/
def toyCf8M_same : Prop :=
  ∀ (Mo : ToyMo8) (Md : ToyMd Mo.I),
    (toyCf8M Mo Md).conf.E0 = (toyCf8 Mo).conf.E0 ∧
    (toyCf8M Mo Md).conf.Msg = (toyCf8 Mo).conf.Msg ∧
    (toyCf8M Mo Md).conf.Rec = (toyCf8 Mo).conf.Rec ∧
    (toyCf8M Mo Md).conf.PIdx = (toyCf8 Mo).conf.PIdx ∧
    (toyCf8M Mo Md).conf.I = (toyCf8 Mo).conf.I ∧
    (toyCf8M Mo Md).X = (toyCf8 Mo).X

def toyCf8M_third : Prop := ∀ (Mo : ToyMo8) (Md : ToyMd Mo.I), Md.OK → (toyCf8M Mo Md).Third

def toyCf8M_ok : Prop := ∀ (Mo : ToyMo8) (Md : ToyMd Mo.I), Md.OK → (toyCf8M Mo Md).OK 1

end Spec

theorem toyCf8M_same : Spec.toyCf8M_same := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem toyCf8M_third : Spec.toyCf8M_third := fun Mo Md h =>
  ⟨core8, distC8 Mo, (by norm_num : 3 * 1 < 6), smp8 Mo,
    ⟨h.sub, h.admits, Mo.held, fun _ _ h => congrArg Mo.heldB (funext fun n => h n.1 n.2)⟩⟩

theorem toyCf8M_ok : Spec.toyCf8M_ok := fun Mo Md h =>
  ldT3_conf F E (toyCf8M Mo Md) (toyCf8M_third Mo Md h)

end Cb.Gl
