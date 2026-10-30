-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Step.lean: the law of (fold) at the format's step of a block.

Main names: step_decides (where a block's step says yes, its decision has said yes at the rounds
without the sealed digest), split_one, DecidesBySplit (a block whose decision's yes is a yes of
"SPLIT"), FoldSoundStep, foldSound_step.

What is not claimed. That a given block decides by "SPLIT" is shown where the block is written.
Nothing on how z_fd is drawn. Nothing on soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Condition
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block noDigest OpenedColumn)

variable {K : Type} [Field K] (ρ : Reading K)

/-- Where a block's step says yes, its decision has said yes at the rounds without the sealed
digest. -/
theorem step_decides {S Cl : Type} (ft : Nat) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : Nat) (h : b.step ft s rs cols = .ok (s', k)) :
    ∃ gs, b.decide s (rs.map noDigest) gs = .ok s' := by
  unfold Block.step at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i v hv
        cases h
        exact ⟨_, hv⟩

/-- With two codes "SPLIT" says yes at one round alone. -/
theorem split_one (p : Par) (d d' : St) (rs : List Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : split p d rs = some d') : ∃ r, rs = [r] := by
  rcases rs with _ | ⟨r, _ | ⟨r2, l⟩⟩
  · simp [split, hS] at h
  · exact ⟨r, rfl⟩
  · simp [split, hS] at h

/-- A block whose decision's yes is a yes of "SPLIT" at the same rounds. -/
def DecidesBySplit (p : Par) (b : Block St Unit) : Prop :=
  ∀ d rs gs d', b.decide d rs gs = .ok d' → split p d rs = some d'

open Classical in
/-- The law of (fold), of a block's step. -/
def FoldSoundStep [Fintype K] (p : Par) (b : Block St Unit) : Prop :=
  ∀ (ft : Nat) (d : St) (T : Statement) (m : Words K), p.S.sharedSplitNeeded = true →
    Placed T p.S d.loc (linLayOmega d.st.codes p.S) →
    (∃ j < p.S.matrixRows, omegaOf d.loc (linLayOmega d.st.codes p.S) m j ≠
      ∑ t ∈ Finset.range (2 ^ p.S.kLo),
        eqK ((d.loc.psiSh.take p.S.kLo).map ρ.val) t * uOf d.loc m (t + 2 ^ p.S.kLo * j)) →
    (Finset.univ.filter fun z : Fin p.S.kRow → K =>
      ∃ (zs : List E) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (d' : St) (k : Nat),
        zs.map ρ.val = List.ofFn z ∧
        b.step ft { d with loc := { d.loc with zFd := zs } } rs cols = .ok (d', k) ∧
        Means.AllSay ρ T (rowsOn d' d.loc.gOmega) m ∧
        Means.AllSay ρ T (rowsOn d' d.loc.gU) m).card ≤
      p.S.kRow * Fintype.card K ^ (p.S.kRow - 1)

/-- **The law of (fold) at the step of a block that decides by "SPLIT".** -/
theorem foldSound_step [Fintype K] (p : Par) (b : Block St Unit) (hb : DecidesBySplit p b) :
    FoldSoundStep ρ p b := by
  classical
  intro ft d T m hS hP hgap
  refine le_trans (Finset.card_le_card ?_) (foldSound ρ p d T m hS hP hgap)
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  obtain ⟨_, zs, rs, cols, d', k, hzs, hst, hO, hU⟩ := hz
  obtain ⟨gs, hdec⟩ := step_decides ft b _ d' rs cols k hst
  have hsp := hb _ _ _ _ hdec
  obtain ⟨r, hr⟩ := split_one p _ d' _ hS hsp
  rw [hr] at hsp
  exact ⟨Finset.mem_univ _, zs, r, d', hzs, hsp, hO, hU⟩

end Desc.K14.Law
