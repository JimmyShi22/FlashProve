-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/GameMembers.lean: a member of the premises of `Spec.lifeSeeded` (Hiop/Seeded/Game.lean).

Definitions, statements and proofs. Nothing here is about the protocol of the release.
Part 1, at ANY object: the kit whose auxiliary value is the verifier's randomness itself, uniform
(`Kit.plain`). It is never none. At it `SimsG.Good` follows from what the exact form of
honest-verifier zero knowledge says of each honest side, on honest out-of-domain (OOD) samples at
seeds of Gs (`good_plain`; the converse is not stated).
Part 2, a small member.
The object is `pad` (Hiop/Seeded/Pad.lean). The auxiliary value of a test is either nothing or a
value of the verifier's randomness, each with probability 1/2, so both arms of a run occur; links
and sessions never have a verifier's randomness and show nothing. All premises hold together, with
error 0 (`game_member`). It guards against premises that contradict one another, and no more.

Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.GameProof
import Hiop.Seeded.Pad

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Rom Compile.Lifetime
open scoped ENNReal

/-! ## Part 1. The kit without an auxiliary value -/

section Plain
variable {I X : Type} {L : HolographicProtocol I X}

/-- The auxiliary value is the verifier's randomness itself, uniform. -/
def Kit.plain (L : HolographicProtocol I X) : Kit L where
  AT := Rho L.offline.shape
  AL := Rho L.link.shape
  AB := Rho L.onlineBatch.loc.shape
  μT := fun _ _ => unif _
  μL := fun _ _ => unif _
  μB := fun _ _ => unif _
  ρT := some
  ρL := some
  ρB := some

/-- a set of values that are "some ρ with P ρ" is the set of ρ with P ρ -/
theorem pr_some_le {γ : Type} (p : PMF γ) (P : γ → Prop) {z : ℝ≥0∞} (h : pr p {a | P a} ≤ z) :
    pr p {a | ∃ ρ, some a = some ρ ∧ P ρ} ≤ z :=
  (pr_mono p fun _ ha => ha.elim fun _ hρ => (Option.some.inj hρ.1) ▸ hρ.2).trans h

/-- At the plain kit: simulators that are good in the exact form of honest-verifier zero knowledge
(the probability is that of the set of verifier's randomness at which output and simulator differ)
are good. -/
theorem good_plain {P : RecsG L} {Sm : SimsG L} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop}
    {zT zL zO : ℝ≥0∞}
    (hT : ∀ e i r s, Gs s →
      prRho {ρ | (P.T e).output (i, r, s) (L.recOf i r s) ρ ≠
        Sm.T e (L.recOf i r s) ρ (L.offline.extAns (L.recOf i r s) ρ (L.encodeIndex i r))} ≤ zT)
    (hL : ∀ e i r s r' s', Gs s → Gs s' →
      prRho {ρ | (P.Lk e).output (i, (r, s), (r', s')) (L.recOf i r s, L.recOf i r' s') ρ ≠
        Sm.Lk e (L.recOf i r s, L.recOf i r' s') ρ
          (L.link.extAns (L.recOf i r s, L.recOf i r' s') ρ (L.encodeIndex i r, L.encodeIndex i r'))} ≤ zL)
    (hB : ∀ e i r s x, Gs s → Ryes i x →
      prRho {ρ | (P.B e).output (i, r, s) (x, L.recOf i r s) ρ ≠
        Sm.B e (x, L.recOf i r s) ρ (L.onlineBatch.loc.extAns (x, L.recOf i r s) ρ (L.encodeIndex i r))} ≤ zO) :
    Sm.Good (Kit.plain L) P Gs Ryes zT zL zO where
  goodT := fun e i r s hs => pr_some_le _ _ (hT e i r s hs)
  goodL := fun e i r s r' s' hs hs' => pr_some_le _ _ (hL e i r s r' s' hs hs')
  goodB := fun e i r s x hs hx => pr_some_le _ _ (hB e i r s x hs hx)

end Plain

/-! ## Part 2. A small member -/

def padKit : Kit pad where
  AT := Option (Rho pad.offline.shape)
  AL := Unit
  AB := Unit
  μT := fun _ _ => unif (Option (Rho pad.offline.shape))
  μL := fun _ _ => PMF.pure ()
  μB := fun _ _ => PMF.pure ()
  ρT := id
  ρL := fun _ => none
  ρB := fun _ => none

def padRecs : RecsG pad := ⟨fun _ => pad.honestOfflineProver, fun _ => pad.honestLinkProver, fun _ => pad.honestOnlineBatchProver.one⟩

def padSimsG : SimsG pad :=
  ⟨fun _ => bitSim, fun _ _ _ _ => PMF.pure none, fun _ _ _ _ => PMF.pure none⟩

theorem padRecs_ext : padRecs.Ext :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem pad_readsG : ReadsG pad (fun _ => True) 1 1 0 0 0 where
  cntT := pad_reads.cntT
  cntLp := pad_reads.cntLp
  cntLc := pad_reads.cntLc
  cntO := fun _ _ => by
    show (∅ : Finset (Fin 1)).card ≤ 0
    rw [Finset.card_empty]
  hidE := fun S hS s _ i i' => pad_reads.hidE S hS s i i'

/-- The offline simulator is exact at every verifier's randomness. -/
theorem pad_exact (w : Bool × (Bool × Bool) × Bool) (x : pad.Rec) (ρ : Rho pad.offline.shape) :
    pad.honestOfflineProver.output w x ρ = bitSim x ρ (pad.offline.extAns x ρ fun _ => xor w.1 w.2.1.1) := by
  have h0 := output_bitSide (Y := pad.Rec)
    (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1)
    (fun w => xor w.1 w.2.1.1) (fun _ => false) w x ρ
  rw [if_neg (by simp)] at h0
  refine h0.trans ?_
  show _ = PMF.pure (some (bitView
    ((((bitProto pad.Rec).extAns x ρ fun _ => xor w.1 w.2.1.1) 0).getD false) _))
  rw [extAns_zero]
  rfl

theorem pad_goodG (Ryes : Bool → Unit → Prop) (zT zL zO : ℝ≥0∞) :
    padSimsG.Good padKit padRecs (fun _ => True) Ryes zT zL zO where
  goodT := fun _ i r s _ =>
    (le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ ha =>
      ha.elim fun ρ h => h.2 (pad_exact (i, r, s) _ ρ))).trans (zero_le _)
  goodL := fun _ _ _ _ _ _ _ _ =>
    (le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ ha =>
      ha.elim fun ρ h => Option.some_ne_none ρ h.1.symm)).trans (zero_le _)
  goodB := fun _ _ _ _ _ _ _ =>
    (le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ ha =>
      ha.elim fun ρ h => Option.some_ne_none ρ h.1.symm)).trans (zero_le _)

theorem padBounds_fitsG : padBounds.Fits 1 1 0 0 0 := by
  intro e _
  show 1 * 1 + (if e = 0 then padBounds.sum padBounds.links * 0 else 0) + 1 * 0 + 0 * 0 + 0 ≤ 1
  split_ifs <;> simp

/-- All premises of `Spec.lifeSeeded` hold together at this object; its conclusion there. -/
theorem game_member (S : OSpec) (Ryes : Bool → Unit → Prop) (i i₀ : Bool) (α : Type)
    (A : Adv S (GOut pad padKit.form) (GIn pad padKit.form) α)
    (hA : A.CallsOK (okCall (Ryes i))) :
    tv ((interact (gameReal pad padKit padRecs i padBounds (fun _ => True) S) A
          (none, Table.empty S)).map Prod.fst)
        ((interact (gameSim pad padKit padSimsG i₀ padBounds (fun _ => True) S) A
          (none, Table.empty S)).map Prod.fst) ≤ padBounds.err 0 0 0 :=
  lifeSeeded S Bool Unit pad padKit (fun _ => True) Ryes 1 1 0 0 0 0 0 0 pad_readsG padRecs
    padRecs_ext padSimsG (pad_goodG Ryes 0 0 0) padBounds padBounds_fitsG i i₀ α A hA

end Hiop.Seeded

#print axioms Hiop.Seeded.good_plain
#print axioms Hiop.Seeded.pad_goodG
#print axioms Hiop.Seeded.game_member
