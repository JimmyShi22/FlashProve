-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/ProofKit.lean: small facts on "an IOR in every slot, then a batch IOP" (Ior/Batch.lean: `online`,
`onlineHonest`).

In standard terms: lemmas on a batch protocol in which every slot first runs the same interactive
oracle reduction by itself, and one batch IOP then treats all the outputs.

Main names: what `IOR.Tied` says with the union written out (`tied_union`); the verifier messages
of the second part among the local and the shared ones of a slot (`back_lo`, `back_sh`); the
withheld set of a slot and its probability (`withheld_online_subset`, `prRho_withheld_online_le`);
the positions read in the shared oracle are a function of the shared verifier messages
(`extShared_online`). Each under the hypotheses of its statement.

Limits: this file says nothing on soundness or zero knowledge.

Terms: lean/GLOSSARY.md.
-/
import Hiop.ListNums
import Ior.ToProtoProofsSeq

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

/-- The local verifier messages of the second part are those of the second part of ρ. -/
theorem back_lo :
    ∀ (s : Shape) {t : Shape} (A' : RoundSplits t) (ρ : Rho (s ++ t)),
      RhoLo.back s (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') ρ) =
        Rho.lo A' (Rho.snd (s := s) ρ)
  | [], _, _, _ => rfl
  | _ :: s, _, A', (_, ρ) => back_lo s A' ρ

/-- The shared verifier messages of the second part are those of the second part of ρ. -/
theorem back_sh :
    ∀ (s : Shape) {t : Shape} (A' : RoundSplits t) (ρ : Rho (s ++ t)),
      RhoSh.back s (Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') ρ) =
        Rho.sh A' (Rho.snd (s := s) ρ)
  | [], _, _, _ => rfl
  | _ :: s, _, A', (_, ρ) => back_sh s A' ρ

open Classical in
/-- "The verifier reads all that is tied to its positions", with the union written out: the form in
which `Spec.hvzk_toProto` and the composed budget take it. -/
theorem tied_union {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo)
    (h : R.Tied) (ρ : Rho R.shape) :
    (R.reads ρ).biUnion (R.tie ρ) ⊆ R.extReads ρ :=
  Finset.biUnion_subset.2 (h ρ)

section Online
variable {X Xl Wt WA W0 Wj : Type} {E0 Ej : ExtSpec} (F : IOR X E0 Xl (E0.prod Ej))
  (Q : BIOP Xl (E0.prod Ej)) (HF : F.Honest WA (W0 × Wj)) (HQ : Q.Honest W0 Wj) (ext : Wt → E0.Str)
  (sh : Wt → W0) (inp : Wt → X → WA)

/-- On the withheld set of a slot the first part of ρ is withheld by the IOR, or the second by the
batch IOP. -/
theorem withheld_online_subset (w : Wt) (x : X) :
    (onlineHonest F Q HF HQ ext sh inp).one.withheld w x ⊆
      Rho.cylFst Q.ior.shape (HF.Bad ∪ HF.Hid (inp w x) x) ∪ Rho.cylSnd F.shape HQ.withheld := by
  intro ρ hρ
  rcases hρ with ((hb | hb) | hs) | hh
  · have hb : RhoLo.front F.shape (A' := Q.ann)
          (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ) ∈ HF.Bad := hb
    rw [RhoLo.front_lo] at hb
    exact Or.inl (Or.inl hb)
  · have hb : RhoLo.back F.shape (A' := Q.ann)
          (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ) ∈ HQ.Bad := hb
    rw [back_lo] at hb
    exact Or.inr (Or.inl hb)
  · have hs : HQ.stop0
          (RhoSh.back F.shape (A' := Q.ann)
            (Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ)) = true := hs
    rw [back_sh] at hs
    exact Or.inr (Or.inr hs)
  · have hh : RhoLo.front F.shape (A' := Q.ann)
          (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ) ∈
        HF.Hid (inp w x) x := hh
    rw [RhoLo.front_lo] at hh
    exact Or.inl (Or.inr hh)

theorem prRho_withheld_online_le (w : Wt) (x : X) :
    prRho ((onlineHonest F Q HF HQ ext sh inp).one.withheld w x) ≤
      prRho HF.Bad + prRho (HF.Hid (inp w x) x) + prRho HQ.withheld :=
  le_trans (pr_mono _ (withheld_online_subset F Q HF HQ ext sh inp w x))
    (le_trans (prRho_cyl_union_le _ _) (add_le_add (pr_union_le _ _ _) le_rfl))

/-- `BatchInteractiveOracleProof.ExtShared` (Iop/Batch.lean): if the IOR reads nothing of the shared oracle (`h0`),
computes the symbol at `Sum.inl p` of the new implicit instance from that oracle's symbol at p and
from no other symbol of it (`hI`) and computes no other symbol of the new implicit instance from it
(`hA`), and the positions that the batch IOP reads in it are a function of the shared verifier
messages (`hQ`), then so are those of the composition. -/
theorem extShared_online [DecidablePred fun p : E0.Pos ⊕ Ej.Pos => p.isLeft = true]
    (h0 : ∀ ρ, F.extReads ρ = ∅) (hI : ∀ ρ p, F.srcE ρ (Sum.inl p) = {p})
    (hA : ∀ ρ q, F.srcE ρ (Sum.inr q) = ∅)
    (hQ : ∀ ρ ρ', Rho.sh Q.ann ρ = Rho.sh Q.ann ρ' →
      (Q.ior.extReads ρ).filter (fun p => p.isLeft = true) =
        (Q.ior.extReads ρ').filter (fun p => p.isLeft = true)) :
    (online F Q).toBatch.ExtShared := by
  intro _ _ ρ ρ' h
  have h' := hQ _ _ (Rho.sh_snd_eq (s := F.shape) (RoundSplits.allLocal F.shape) Q.ann h)
  ext p
  show p ∈ (F.seq Q.ior).extReads ρ ↔ p ∈ (F.seq Q.ior).extReads ρ'
  rw [IOR.mem_extReads_seq_copy F Q.ior h0 hI hA, IOR.mem_extReads_seq_copy F Q.ior h0 hI hA]
  have e : ∀ U : Finset (E0.Pos ⊕ Ej.Pos),
      Sum.inl p ∈ U ↔ Sum.inl p ∈ U.filter (fun p => p.isLeft = true) := fun U => by
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩
  rw [e, e (Q.ior.extReads _), h']

end Online
end Hiop
