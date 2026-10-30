-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartKeepProofs.lean: the statements of Cb/Part/LdPartKeep.lean, proved.

Main names:
  `ldPartKeep_world`: under `P.Props p`, the ties and O.pkR m: the relaxed worlds (`P.world`,
    Cb/Part/LdPartRide.lean) of segment k at the reading O of all rows and at the reading
    `Ok.pull r` of the kept rows agree at every place that a segment j with k < j < P.n reads (rows
    of segments ≤ k that j reads are kept behind k; segments > k are read off the further witness in
    both).
  `ldPartKeep_fw`, `ldPartKeep_bw`, `ldPartKeep_pull`.

Limits: what the head of Cb/Part/LdPartKeep.lean lists as not said is not said here either.
-/
import Cb.Part.LdPartKeep
import Cb.Part.LdPartCfProofs

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk IOR

theorem ldPartKeep_world {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
    (P : LdPartD Cf) (K : LdPartPk) {p k : ℕ} {S Sk : Sig E} {O : LdPartOut E S}
    {Ok : LdPartOut E Sk} {r : S.Msg → Sk.Msg} (hP : P.Props p) (hT : LdPartKeepTie P k O Ok r)
    (m : S.Msg) (w : LdPartW E) (hm : O.pkR m) {j : ℕ} (hkj : k < j) (hj : j < P.n) :
    ∀ q ∈ (P.seg j).places,
      P.world K k (Ok.pull r) m w q.1 q.2.1 q.2.2 = P.world K k O m w q.1 q.2.1 q.2.2 := by
  intro q hq
  unfold LdPartD.world
  by_cases h1 : q.1 ≤ k
  · rw [if_pos h1, if_pos h1]
    exact (hT.rdKept m hm (q.1, q.2.1) (hP.keeps j hj q hq k h1 hkj) q.2.2).symm
  · rw [if_neg h1, if_neg h1]

theorem ldPartKeep_fw : Spec.ldPartKeep_fw := by
  intro F E _ _ _ _ Cf P K k S Sk O Ok r St x rc bitX hT st y t h
  exact ⟨h.1, hT.pkX _ _ h.2.1, h.2.2⟩

theorem ldPartKeep_bw : Spec.ldPartKeep_bw := by
  intro F E _ _ _ _ Cf P K p k S Sk O Ok r St x rc bitX hP hT a t hm h
  exact ⟨hm, h.1,
    fun j h1 h2 =>
      ldPartCf_holds _ _ _ _ _ _ (hP.wf j h2)
        (ldPartKeep_world P K hP hT t.1.2 t.2.1 hm h1 h2) (h.2 j h1 h2)⟩

theorem ldPartKeep_pull : Spec.ldPartKeep_pull := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ _ => rfl⟩

end Cb
