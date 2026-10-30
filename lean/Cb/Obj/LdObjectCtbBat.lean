-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbBat.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for the test for linear constraints on a batch, built from standard parts.

This test is the fifth part of the object (`PBat`, Cb/Obj/LdObjectParts.lean).

Theorems. Bookkeeping for the passage to one random oracle (Cb/Obj/LdObjectCtbParts.lean;
`PBat.CtbB`: Cb/Obj/LdObjectCtbSplit.lean).

Main names:
  `ctbA_tcNil`, `ctbA_consLo`, `ctbA_consSh`: plans for a batch (`LdTcA`,
    Cb/Ld/LdBatchBlocksPlan.lean): nothing is left; a test in every slot, then a plan; a test run
    once by the shared part, then a plan.
  `std2_fin`: all oracle messages at the end of the standard test with kept messages have
    `LdCode.FinNS`, if the codes of the kept family `D.Sa` and of `D.MW`, `D.MU`, `D.MO` have.
  `std2B_ctbB`: `(D.partB ..).CtbB` for `D : StdLn2 Cf P`, from "a native symbol of each code has
    finitely many coordinates" (`LdCode.FinNS`, Cb/Obj/LdObjectCtb.lean), if the configuration's
    code `Cf.C₀` and P have a position (`Nonempty`).

Limits: on a protocol this file has two kinds of conclusion: countability (as in `ctbA_tcNil`) and,
of the codes of a test, `LdCode.FinNS` (`std2_fin`: from `FinNS` of the members' codes); beyond
these no statement of the file concludes anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtbSplit
import Cb.Obj.LdObjectPartBat

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ctbA_lo {K : Type} {A B : Joint K} (l : Link K A B) (h : l.Ctb) : l.lo.CtbA :=
  ctbS_allLocal h

section
variable {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

theorem ctbA_tcNil (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp) :
    (LdTcA.nil S E₀ Wp w₀).cA.CtbA :=
  (ChainA.ctbA_one _).2 (ctbA_lo _ trivial)

variable [Fintype E]

theorem ctbA_consLo (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp)
    (d' : LdBrW D.G D.kp Wp) (h : CtbSh D.T.R.shape) (hQ : QA.cA.CtbA) :
    (LdTcA.consLo D QA d d').cA.CtbA :=
  chainA_ctb_append _ _ ((ChainA.ctbA_one _).2 (ctbS_allLocal (ctb_run D QA.Q.base d d' h))) hQ

theorem ctbA_consSh (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp)
    (d' : LdBrW D.G D.kp Wp) (h : CtbSh D.T.R.shape) (hQ : QA.cA.CtbA) :
    (LdTcA.consSh D QA d d').cA.CtbA :=
  chainA_ctb_append _ _ ((ChainA.ctbA_one _).2 (ctbS_shared (ctb_run D QA.Q.base d d' h))) hQ

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  {P : Type} [Fintype P] (D : StdLn2 Cf P)

omit [Fintype F] in
theorem std2_fin (hA : ∀ a, (D.Sa.om a).C.FinNS) (hW : D.MW.Cm.FinNS)
    (hU : D.MU.Cm.FinNS) (hO : D.MO.Cm.FinNS) :
    ∀ o : D.C.S.O, (D.C.S.om o).C.FinNS
  | .inl (.inl (.inl a)) => hA a
  | .inl (.inl (.inr _)) => hW
  | .inl (.inr _) => hU
  | .inr _ => hO

variable [Nonempty (Fin Cf.C₀.n)] [Nonempty P]

omit [Fintype F] in
/-- The fifth part with standard parts. -/
theorem std2B_ctbB (N L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) (x₀ : D.T.St₁ × D.C.S.Smp)
    (y₀ : (D.C.E₀.prod D.C.S.ext).Str) (d : D.C.P.W0) (d₀ : D.O.P.W0) (ya : D.C.P.Ea.Str)
    (hA : ∀ a, (D.Sa.om a).C.FinNS) (hW : D.MW.Cm.FinNS) (hU : D.MU.Cm.FinNS) (hO : D.MO.Cm.FinNS) :
    (D.partB N L tW tU tO ba x₀ y₀ d d₀ ya).CtbB :=
  ⟨ctbSy_one _ hW, ctbSy_one _ hU, ctbSy_one _ hO,
    ctb_base _ _ _ _ _ _ (finNS_grp _ (std2_fin D hA hW hU hO)),
    ctb_base _ _ _ _ _ _ (finNS_grp _ fun a => std2_fin D hA hW hU hO a.1),
    ctbA_consLo D.D₃ D.nil3 _ _
      (ctb_base _ _ _ _ _ _ (finNS_grp _ fun a => std2_fin D hA hW hU hO a.1.1))
      (ctbA_tcNil _ _ _ _)⟩

end
end Cb
