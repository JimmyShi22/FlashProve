-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseVStep.lean: the step without rounds with which the closing of the test for linear
constraints begins (`C.link fq Bq`, Cb/Ld/LdLinClosePre.lean): part of what the honest side of a
batch requires of it.

Statements (each a `Prop` in `Cb.Spec`) and proofs.

Main names:
  `Spec.ldLinVS_good`: if the base joint Bq says the rows that are left and what the preamble left
    (`C.Says Bq fq`), the link has the whole bundle (`GoodT`), and nothing hidden is withheld.
  `Spec.ldLinVS_bears`: run in every slot (`RoundSplits.allLocal`, each slot's budget), the link bears what
    follows for families of slots (`BearsV`) as soon as the positions fit (`NeedsV`,
    Ior/LinkVBearsMore.lean): for its budget is "true".
In `Spec.ldLinVS_good`, `GoodT` (of a link) is in the conclusion. `IOR.GoodT` (likewise `IOR.Good`,
Ior/Chain.lean) bundles what is asked of one reduction, with its honest side, between two joints, at
given numbers; among its clauses: completeness between the honest relations, outside sets of
verifier randomness whose probabilities further clauses bound by the numbers; round-by-round
knowledge soundness (`Know`) between the relaxed relations, on the input joint's set of statements,
with a given extractor, at the numbers' list of errors; and one on honest-verifier zero knowledge.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseV
import Cb.Ld.LdLinClosePreProofs
import Ior.LinkVBearsMore

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

def ldLinVS_good : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (Stq : Type)
      (Bq : Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa)) (fq : C.St6 → Stq),
    C.Says Bq fq → (C.link fq Bq).GoodT ∧ ∀ w x, (C.link fq Bq).H.Hid w x = ∅

def ldLinVS_bears : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (Stq : Type) (Bq : Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa))
      (fq : C.St6 → Stq) (N : ℕ) (qi : QFam C.P.E5 N) (qo : QFam (C.E₀.prod C.S.ext) N),
    (C.link fq Bq).R.NeedsV (RoundSplits.allLocal _) qi qo →
    (C.link fq Bq).R.BearsV (RoundSplits.allLocal _)
      (budEach (C.link fq Bq).R N (C.link fq Bq).P.bud) qi qo

end
end Spec

section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] in
theorem ldLinVS_good : Spec.ldLinVS_good E ι κ J Y := by
  intro C Stq Bq fq hS
  exact ⟨goodT_pure Unit _ _ _ _ _ _ C.P.j6.cf (C.S.over Bq).cf (C.stepF fq) C.toE (C.stepM fq)
      (fun _ w => C.back w) (ldLinPre_step_cf E ι κ J Y C Stq Bq fq hS),
    fun _ _ => rfl⟩

omit [Fintype E] [Fintype ι] in
theorem ldLinVS_bears : Spec.ldLinVS_bears E ι κ J Y := fun _ _ _ _ _ _ _ hN J ρ Us hU =>
  ⟨fun _ => trivial, hN J ρ Us hU⟩

end
end Cb
