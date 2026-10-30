-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbToy.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for small example instances.

Theorems. Bookkeeping for the passage to one random oracle (CompileK/ImplCountable.lean: `CtbSh`).
See Cb/Obj/LdObjectCtb.lean (which says what `CtbSh`, `Sig.CtbSy` and `LdCode.FinNS` are),
Cb/Obj/LdObjectCtbPre.lean and Cb/Obj/LdObjectCtbParts.lean (the clauses of `P.CtbP`).

Main names:
  `finNS_ofEnc`, `finNS_il`, `finNS_pair`, `finNS_fam`, `finNS_reading`: in
    Cb/Obj/LdObjectCtbFin.lean.
  `finNS_toy7`, `finNS_toy74`: "a native symbol has finitely many coordinates" (`LdCode.FinNS`) of
    the toy codes over seven points.
  `ctbSy_stdFam`: the standard family of two members, both in the plain format
    (Cb/Ld/LdSendToyFam.lean), if the two codes have `FinNS`.
  `ctbSy_fam7`: the family at the small code: no hypothesis beside its instance arguments.



Limits: on a protocol this file has two kinds of conclusion: countability (`ctbSy_fam7`, at the
toy; `ctbSy_stdFam`, generic, from `FinNS`
of the family's two codes) and, of the two toy codes, `LdCode.FinNS` (`finNS_toy7`, `finNS_toy74`);
beyond these no statement of the file concludes anything of a protocol.












Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtbFin
import Cb.Obj.LdObjectCtbPre
import Cb.Ld.LdWfToyItem
import Cb.Ld.LdRelToy7d4

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

theorem finNS_toy7 (R : Type) [Fintype R] [DecidableEq R] : (LdToy7.toyLd7 R).FinNS :=
  finNS_reading _ _
theorem finNS_toy74 (R : Type) [Fintype R] [DecidableEq R] : (LdToy74.toyLd74 R).FinNS :=
  finNS_reading _ _

section Fam
variable {E : Type} [Field E] [Fintype E]

theorem ctbSy_stdFam (F : StdFam E) (h₁ : F.C₁.FinNS) (h₂ : F.C₂.FinNS) :
    F.sig.CtbSy := fun a p => match a, p with
  | false, p => by
      haveI := h₁ p
      exact inferInstanceAs (Countable (F.C₁.NS p → E))
  | true, p => by
      haveI := h₂ p
      exact inferInstanceAs (Countable (F.C₂.NS p → E))

end Fam

open LdToy LdToy7 in
theorem ctbSy_fam7 (Ix Im μ₁ μ₂ : Type) [Fintype Ix] [DecidableEq Ix] [Fintype Im]
    [DecidableEq Im] [Fintype μ₁] [DecidableEq μ₁] [Fintype μ₂] [DecidableEq μ₂]
    (pl₁ : Ix → μ₁ → Bool) (pl₂ : Im → μ₂ → Bool) :
    (fam7 Ix Im μ₁ μ₂ pl₁ pl₂).sig.CtbSy :=
  ctbSy_stdFam _ (finNS_toy7 _) (finNS_toy7 _)

end Cb
