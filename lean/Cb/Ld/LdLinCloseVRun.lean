-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseVRun.lean: a whole test on a group, beside what is carried: what its simulator is
given; none of its oracles survives; so, under `D.OK` (D: a whole test, `LdRunD`,
Cb/Ld/LdLinCloseRuns.lean), its budget bears whatever follows.

Statements (each a `Prop` in `Cb.Spec`) and proofs; and the proof of `Spec.ldRunV_given` of
Cb/Ld/LdLinCloseV.lean.
The term (Cb/Ld/LdLinCloseRun.lean): the bridge, then the test beside the carried part, then the
trivial statement is dropped.

Main names:
  `ldRunV_given`: every position that the simulator is given (`IOR.given`, Ior/Honest.lean) is a
    position of a member of the group: the bridge and the last step read and tie nothing; the test
    beside the carried part is given positions of the complex only (`keep_not_mem_given_inr`,
    Cb/Ld/LdGroupKit.lean); a position of the complex has its sources in the members' words.
  `Spec.ldRunV_shut`: no position of what the test leaves has a source in the test's own oracles.
  `Spec.ldRunV_bud0`: `D.OK` ⇒ the test's budget holds at no further read.
  `Spec.ldRunV_bears_local`, `Spec.ldRunV_bears_shared`: so, under `D.OK`, for families of slots:
    the budget half of "bears what follows" holds outright (each slot's; at the union), and what is
    left is the half on positions alone (`NeedsV`, Ior/LinkVBearsMore.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseV
import Ior.LinkVBearsMore

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec

def ldRunV_shut : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    (D.link A₀ d d').R.Shut

def ldRunV_bud0 : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    D.OK → ∀ ρ, (D.link A₀ d d').P.bud ρ ∅

/-- States: under `D.OK`, the test in every slot bears what follows, as soon as the positions fit.
-/
def ldRunV_bears_local : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (N : ℕ) (qi : QFam (E₀.prod S.ext) N) (qo : QFam (E₀.prod (S.sub D.kp).ext) N),
    D.OK → (D.link A₀ d d').R.NeedsV (RoundSplits.allLocal _) qi qo →
    (D.link A₀ d d').R.BearsV (RoundSplits.allLocal _)
      (budEach (D.link A₀ d d').R N (D.link A₀ d d').P.bud) qi qo

/-- States: under `D.OK`, the test run once by the shared part bears what follows, as soon as the
positions fit. -/
def ldRunV_bears_shared : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (N : ℕ) (qi : QFam (E₀.prod S.ext) N) (qo : QFam (E₀.prod (S.sub D.kp).ext) N),
    D.OK → (D.link A₀ d d').R.NeedsV (RoundSplits.const (RAnn.ofShared .sh) _) qi qo →
    (D.link A₀ d d').R.BearsV (RoundSplits.const (RAnn.ofShared .sh) _)
      (budUnion (D.link A₀ d d').R N (D.link A₀ d d').P.bud) qi qo

end Spec

/-- shut, then shut, is shut -/
theorem ldRunV_shut_seq {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} (R₁ : IOR X₁ E₁ X₂ E₂)
    (R₂ : IOR X₂ E₂ X₃ E₃) (h₁ : R₁.Shut) (h₂ : R₂.Shut) : (R₁.seq R₂).Shut := by
  classical
  intro ρ q
  show ((R₂.srcE (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcO (Rho.fst ρ))).image OPos.left ∪
      (R₂.srcO (Rho.snd (s := R₁.shape) ρ) q).image (OPos.right (s := R₁.shape)) = ∅
  rw [h₂, Finset.image_empty, Finset.union_empty]
  have : (R₂.srcE (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcO (Rho.fst ρ)) = ∅ := by
    ext p
    simp [h₁ (Rho.fst ρ)]
  rw [this, Finset.image_empty]

theorem ldRunV_shut : Spec.ldRunV_shut := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d'
  refine ldRunV_shut_seq _ _ (fun _ _ => rfl) (ldRunV_shut_seq _ _ (fun ρ q => ?_) fun _ _ => rfl)
  rcases q with q | q
  · exact q.elim
  · rfl

theorem ldRunV_bud0 : Spec.ldRunV_bud0 := by
  classical
  intro E _ _ S D St₀ Wp E₀ A₀ d d' hD ρ
  have h := (ldChain_link E S D St₀ Wp E₀ A₀ d d' (fun _ => True) (fun _ => True)
      hD fun _ _ => trivial).2.bears
    ρ ∅ trivial
  simpa using h.1

/-- membership in a union of two sets, whatever the instance that decides equality -/
theorem ldRunV_mem_union {α : Type} (inst : DecidableEq α) {s t : Finset α} {a : α} :
    a ∈ @Union.union _ (@Finset.instUnion α inst) s t ↔ a ∈ s ∨ a ∈ t := Finset.mem_union

theorem ldRunV_given : Spec.ldRunV_given := by
  classical
  intro E _ _ S D St₀ Wp E₀ A₀ d d' ρ T p hp
  have hp1 : p ∈
      ((ldBridge D.G D.kp D.Sb D.Z St₀ E₀).seq
          ((D.T.R.keep (LdCarX D.kp St₀) (LdCarE D.kp E₀)).seq (ldDropT D.kp St₀ E₀))).given
        ρ T := hp
  rw [given_seq] at hp1
  rcases (ldRunV_mem_union _).1 hp1 with h | h
  · exfalso
    rcases mem_given.1 h with h | ⟨q, _, h⟩
    · obtain ⟨a, ha, _⟩ := (ldLkC_mem_biUnion _).1 h
      exact absurd ha (Finset.notMem_empty _)
    · obtain ⟨a, ha, _⟩ := (ldLkC_mem_biUnion _).1 h
      exact absurd ha (Finset.notMem_empty _)
  · obtain ⟨e, he, hpe⟩ := (ldLkC_mem_biUnion _).1 h
    rw [given_seq] at he
    rcases (ldRunV_mem_union _).1 he with h1 | h1
    · rcases e with x | e
      · obtain ⟨u, hu, hpu⟩ := (ldLkC_mem_biUnion _).1 hpe
        obtain rfl := Finset.mem_singleton.1 hu
        obtain ⟨r, hr, hpr⟩ := (ldLkC_mem_biUnion _).1 hpu
        obtain ⟨a, -, rfl⟩ := (ldLkC_mem_image _).1 hr
        exact ⟨a, D.G.pos a x, Finset.mem_singleton.1 hpr⟩
      · exact absurd h1 (keep_not_mem_given_inr D.T.R _ _ e)
    · exfalso
      obtain ⟨u, hu, _⟩ := (ldLkC_mem_biUnion _).1 h1
      rcases mem_given.1 hu with h2 | ⟨q, _, h2⟩
      · exact absurd h2 (Finset.notMem_empty _)
      · exact absurd h2 (Finset.notMem_empty _)

theorem ldRunV_bears_local : Spec.ldRunV_bears_local := by
  classical
  intro E _ _ S D St₀ Wp E₀ A₀ d d' N qi qo hD hN J ρ Us hU
  refine ⟨fun j => ?_, hN J ρ Us hU⟩
  have e : (Us j).biUnion ((D.link A₀ d d').R.srcO (ρ.slot j.1)) = ∅ := by
    ext p
    simp [ldRunV_shut E S D St₀ Wp E₀ A₀ d d' (ρ.slot j.1)]
  show (D.link A₀ d d').P.bud (ρ.slot j.1) ((Us j).biUnion ((D.link A₀ d d').R.srcO (ρ.slot j.1)))
  rw [e]
  exact ldRunV_bud0 E S D St₀ Wp E₀ A₀ d d' hD _

theorem ldRunV_bears_shared : Spec.ldRunV_bears_shared := by
  classical
  intro E _ _ S D St₀ Wp E₀ A₀ d d' N qi qo hD hN J ρ Us hU
  refine ⟨fun j => ?_, hN J ρ Us hU⟩
  have e : (Finset.univ.biUnion fun j' : J =>
        (Us j').biUnion ((D.link A₀ d d').R.srcO (ρ.slot j'.1))) = ∅ := by
    ext p
    simp [ldRunV_shut E S D St₀ Wp E₀ A₀ d d' _]
  show (D.link A₀ d d').P.bud (ρ.slot j.1)
    (Finset.univ.biUnion fun j' : J => (Us j').biUnion ((D.link A₀ d d').R.srcO (ρ.slot j'.1)))
  rw [e]
  exact ldRunV_bud0 E S D St₀ Wp E₀ A₀ d d' hD _

end Cb
