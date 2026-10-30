-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Proofs of statements of Johnson/Desc/Sound/SharedCertain.lean.
import Johnson.Desc.Sound.SharedCertain
import Johnson.Desc.Sound.SharedOnceProofs
import OnBytes.Slice.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

theorem paysOfCertain : PaysOfCertain := by
  intro S Cl W C F p N on on' R R' act h
  exact paysN_of_lostBy p on on' R R' act N
    ⟨fun _ _ => True, fun _ _ => OnBytes.Slice.doomed_of_all _ _ _ fun _ => trivial,
      fun a τ b ha _ hb => h a τ b ha hb⟩

theorem promsAt_zero (split : Bool) : promsAt split 0 = [.tablePromise, .shape 0] := by
  cases split <;> rfl

theorem promsAt_one (split : Bool) : promsAt split 1 = [.tablePromise, .shape 1] := by
  cases split <;> rfl

theorem rowAtS_zero (split : Bool) : rowAtS split 0 = {} := by
  cases split <;> rfl

theorem frontPays : FrontPays := by
  intro P₁ S₂ Cl Wt C Fr N Mg Pm Oc split n f pt r hout hbase hext hshape
  refine paysOfCertain _ _ _ _ _ f n _ _ _ _ _ fun a τ b ha hb => ?_
  obtain rfl := hout a τ b hb
  have hact : (actQ N f (pt :: r) 1).2 b = (actQ N f (pt :: r) 0).2 b := by
    show (actAt Fr Prod.snd N.lo pt.base).2 b = (actAt Fr Prod.snd N.lo f.base).2 b
    rw [hbase]
  refine ⟨⟨fun c hc => ?_, ha.2⟩, fun w hw => ?_⟩
  · rw [promsAt_one] at hc
    have h0 := ha.1
    rcases List.mem_cons.1 hc with rfl | hc
    · have := h0 .tablePromise (by rw [promsAt_zero]; exact List.mem_cons_self ..)
      rw [hact]
      exact this
    · obtain rfl := List.mem_singleton.1 hc
      have := h0 (.shape 0) (by rw [promsAt_zero]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      rw [hact]
      exact hshape _ this
  · rw [hext]
    refine ⟨fun i hi => ?_, hw.2⟩
    have h1 := hw.1 i (Or.inl ⟨hi, fun hin => by
      have := hin.2
      rw [rowAtS_zero] at this
      cases this⟩)
    have h2 : muQ N Mg f (pt :: r) i 1 ((actQ N f (pt :: r) 1).2 b) w := h1
    rw [hact] at h2
    exact h2

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.paysOfCertain
#print axioms VerifiableInference.Desc.Sound.frontPays
