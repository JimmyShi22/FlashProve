-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectToyConf7M.lean: the relation pair of a toy (`ToyMd`).


In standard terms: an arbitrary indexed relation for a toy: an exact relation, its relaxation, and
the trace, a function from index and instance to cells.


Definitions. No parameter of a protocol.


Why: with instances and cells Unit and both relations "true", a request that claims something
cannot start, for this
reason. Behind a request's first sending the exact relation knows of the messages sent only what the
old witness says of them: the old witness is read back off the new messages (`grow`,
Cb/Ld/LdSigSum.lean). With cells = Unit the old witness says nothing of them, so no exact claim on
the messages (keys in a table, valid multiplicities, packing) can be had at the entry of the first
segment.

Main names:
  `ToyMd I`: the data.


  `Md.OK`: Ryes gives Rno; Ryes of some cells gives Ryes of the trace.

Where it is used: Cb/Ld/LdWfToy.lean.

Limits: this file does not say that a pair Md says anything: `ToyMd.triv` is an instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectToyConf7

set_option autoImplicit false

namespace Cb
namespace LdToy7
open Iop Prob Hiop Blocks Cb.Ood LdToy

/-- The relation pair of a toy: the data. -/
structure ToyMd (I : Type) where
  Xm     : Type
  Cells  : Type
  Ryes   : I → Xm → Cells → Prop
  Rno    : I → Xm → Cells → Prop
  trace  : I → Xm → Cells
  cells0 : Cells

/-- the trivial one -/
def ToyMd.triv (I : Type) : ToyMd I :=
  ⟨Unit, Unit, fun _ _ _ => True, fun _ _ _ => True, fun _ _ => (), ()⟩

structure ToyMd.OK {I : Type} (Md : ToyMd I) : Prop where
  sub    : ∀ i x w, Md.Ryes i x w → Md.Rno i x w
  admits : ∀ i x w, Md.Ryes i x w → Md.Ryes i x (Md.trace i x)

end LdToy7

open Iop Prob Hiop Blocks Cb.Ood LdToy LdToy7

end Cb
