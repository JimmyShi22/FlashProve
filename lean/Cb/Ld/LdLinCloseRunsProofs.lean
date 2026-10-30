-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseRunsProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseRuns.lean (several
whole tests on groups in a row). An assembly: under the hypotheses of `Spec.ldClose_run`, one test
is a piece that may tie (`ClosedTr`; Cb/Ld/LdLinCloseRunProofs.lean); such a piece, then a tail, is
a tail (Cb/Ld/LdLinCloseKit.lean). Nothing is defined here that a statement reads.
Main names (statements and hypotheses: Cb/Ld/LdLinCloseRuns.lean):
  `ldRuns_cons`: a test in front of a closing.
  `ldRuns_nil`: the closing with no oracle message left.
  `ldRuns_cf`: a closing as a tail from the joint whose condition may fail (`Rels.cf`).
  `ldRuns_data`: rounds and errors.
-/
import Cb.Ld.LdLinCloseRuns
import Cb.Ld.LdLinCloseRunProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

theorem ldRuns_cons : Spec.ldRuns_cons := by
  intro E _ _ S E₀ Wp D Q d d' hD hQ
  exact tailTr_consC Unit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ _ _
    (ldClose_run E D.B Unit Q.St Wp S D.G D.kp D.Sb D.sl D.Z D.L E₀ Q.base D.hc d d' D.T D.t _ Q.q
      hD.ev hD.list hD.fits hD.tail fun U hU => ⟨U, hU, rfl⟩) hQ

theorem ldRuns_nil : Spec.ldRuns_nil := by
  intro E _ S _ E₀ Wp w₀
  exact ldClose_done _ _ _ _ w₀ _ (fun _ _ => ⟨fun i => isEmptyElim i, trivial⟩) rfl

theorem ldRuns_cf : Spec.ldRuns_cf := fun _ _ _ _ _ Q hQ =>
  tailTr_cf Unit _ _ _ Q.R _ _ Q.H _ trivRels Q.ext Q.N Q.q (fun _ => trivial) hQ

theorem ldRuns_data : Spec.ldRuns_data := by
  intro E _ _ S E₀ Wp D Q d d'
  refine ⟨?_, rfl⟩
  show ((ldRunE D.G D.kp D.Sb D.sl D.Z Q.St E₀ D.T).shape ++ Q.R.shape).length = _
  rw [List.length_append, (ldClose_run_data E D.B Unit Q.St S D.G D.kp D.Sb D.sl D.Z 0 E₀ D.T).1]

end Cb
