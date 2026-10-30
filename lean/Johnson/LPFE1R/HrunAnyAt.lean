-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/HrunAnyAt.lean: AT EVERY STATE OF THE CONDITION IN FRONT OF THE HEAD's BATCHING THE
RUN's OWN READER ANSWERS AT EVERY ENTRY OF THE HEAD's ORDER BUT "K8.equations": hrun_at
(LPFE1R/HrunAt347.lean) said it of six entries; its proof never looked at which. One statement and
its proof. WHAT IT IS FOR: HitemsLeft's k3i at the head's link ("objects" · "join" · "planes"): a
clause that is had at the empty second hole (silent = none by rfl) is carried to the seat's own
readers by itemIn_congr | forms_of_run (Link/Law/HitemsHead.lean) where the run's own
reader answers.
Limits. The head AtMgA is a premise. The full size alone. No soundness statement.

-/
import Johnson.LPFE1R.HrunAt347

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (speaks_of_forms)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The run's own reader answers, at every entry of the head's order but "K8.equations".** -/
theorem hrun_any_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    {L : Link S Claim} (hlk : h.𝔇.lk 24 = some L) :
    ∀ a, on0At h z 24 a → ∀ e ∈ sortItems .head, (e.2 == "K8.equations") = false →
      (K9.readerOf (K9.statesOfLink L) e.1 e.2 a.1).isSome = true := by
  intro a ha e he h8
  have hs : IM.subAt 24 = .head := by decide
  have hin := hin_at h (m := 24) (by omega) z _ a ha (hs ▸ he) h8
  obtain ⟨R, hR⟩ := reader_of_formsIn _ _ _ _ _ hin
  rw [readers_at24 h 24, K9.readersAt_some _ _ _ _ L hlk] at hR
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr := P5J.list_rchIs h z _ _ ha.2
  have hb : batchAt P5J.fullLinks P5J.At.ps 24 = 347 := by
    rw [LPFK9.batchAt_full 24 (by omega)]
    decide
  rw [hb] at hr
  have ht := tablesLaid_347 h.scope h.reads O hr
  rw [O.W] at ht
  exact speaks_of_forms (K9.holesAt (P5J.At.X Zp) 24 24 L) L (K9.phAt (P5J.At.X Zp) 24) e.1
    h8 (by unfold K9.holesAt; rfl) ht (by rw [hR]; rfl)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hrun_any_at
