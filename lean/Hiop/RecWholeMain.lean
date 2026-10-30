-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecWholeMain.lean: honest-verifier zero knowledge of the whole object with records, for the
object that the four sub-protocols form.

The proof of `Spec.rec_main_zk` (Hiop/RecWhole.lean): one application of `rec_honest`
(Hiop/RecMainProof.lean) and one of `rec_hvzk_whole_hiding` (Hiop/RecWholeProof.lean).

Notation: `C`: `ConfigurationWithOutOfDomainSample` (Hiop/RecConf.lean), a configuration with a record; `S`: `SubsR C`
(Hiop/RecSubs.lean), the four sub-protocols: the data, among its fields `wf`, `linOff`, `link`,
`req`, `linOn`: the preamble of weights-formedness, the IOPP at one instance, the link, the preamble
of a request, the IOPP at N instances; `P`: `S.Nums` (Hiop/RecBuild.lean), the numbers of the four
parameter lists; `b`, `eR`: ℕ, the two arguments of `ConfigurationWithOutOfDomainSample.Props` (Hiop/RecConf.lean); `hC`, `hH`:
the premises `C.Props b eR` (Hiop/RecConf.lean) and `S.HypH P` (Hiop/RecBuild.lean) of
`Spec.rec_main_zk`; the `0` handed to `rec_honest`: its argument `εs` (Hiop/RecMain.lean), the `0`
handed to `rec_hvzk_whole_hiding`: its argument `zL` (Hiop/RecWhole.lean).

Limits: see the header of Hiop/RecWhole.lean.
Terms: lean/GLOSSARY.md.
-/
/- Limits: at a record phase that is not empty no theorem of this library states that the hypotheses
   of `rec_main_zk` can be met together. -/
import Hiop.RecWholeProof
import Hiop.RecMainProof

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

theorem rec_main_zk : Spec.rec_main_zk := by
  intro C S P b eR hC hH
  have h := rec_honest C S P b eR 0 hC hH
  exact rec_hvzk_whole_hiding C.I C.X S.lhr (fun i x => ∃ c, C.Ryes i x c) b P.linOff.q P.link.qpar
    P.link.qch P.linOn.q P.wf.pHid 0 P.req.pHid h.wired h.reads h.hidden

end Hiop
