-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CloseProg.lean: two conditions on provers' programs with tokens (Rom/Defer.lean), and
a lemma on one batch under the first condition. Generic in the programs.

For programs pp, pp₁, pp₂ in the place of the prover's program in the compiled scheme (same
committer C, keys and proofs):

  `SafeProg W p pp`  pp obeys the rules of deferred programming with the counts of one batch of maxBatchSize
                     slots: `Disc.Spec.safePB` (Compile/Batch/SpecDiscipline.lean) for pp, without
                     the hypothesis on the number of slots.
  `SkipProg pp₁ pp₂`  pp₂ is pp₁ without work that is never shown (`Rom.Skip`), with equal results,
                      for every correspondence in which the token 0 and the tokens of the key's
                      copies (`k.leaves`) correspond to themselves.
  `Prog.session`  Under `SafeProg W p pp`, one batch keeps the invariant `WorldB.Inv` and makes at
                  most the queries of one batch.

Limits: this file does not prove that two provers whose programs meet these conditions cannot be
distinguished.
-/
import Compile.Batch.ChallUHopR
import Compile.Batch.ChallUWithin
import Compile.Batch.SpecHop
import Compile.Batch.ModeIU
import Compile.Batch.StarKE

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Prob
open scoped ENNReal
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt up chall_reply)
open Compile.Life2.Many (view run_virt frame_virt)
open Compile.Life2.WorldsX (dummy gap)
open Compile.Disc (nEv)
open Disc Disc.VirtO HopD WithinD ModeI

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The program obeys the rules, with the counts of one batch. -/
def SafeProg (W : QueryLayout lam L) (p : Params) (pp : PProg lam L W.K) : Prop :=
  ∀ (k : IskH lam L) (xs : List X) (d : DSt (spec lam W.K L)),
    TidyO (rulesB W.K L lam p) d → IskOKB d k →
    SafeO (rulesB W.K L lam p) (pp k xs) d fun _ d' =>
      TidyO (rulesB W.K L lam p) d' ∧
      IskOKB d' k ∧
      GrowsO (fun _ => False) (IskTokB k) ePB (mPB W) d d'

/-- The second program is the first without work that is never shown. -/
def SkipProg {K : ℕ} (pp₁ pp₂ : PProg lam L K) : Prop :=
  ∀ (k : IskH lam L) (xs : List X) (w : Wd), w.ρ 0 0 →
    (∀ lf ∈ k.leaves, ∀ s s', some (s, s') ∈ lf.node.tree.salts → w.ρ s s ∧ w.ρ s' s') →
    Skip (fun _ a₁ a₂ => a₁ = a₂) w (pp₁ k xs) (pp₂ k xs)

namespace Prog

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- under `SafeProg`: one batch keeps the invariant and makes at most the queries of one batch (one
batch: the program `virt N₀ (gap N₀ d) (pp k xs)`, run in the mode m from the state `dummy d`;
`virt` (Compile/Step1_life2_Virt.lean): the program under the renumbering; `dummy`
(Compile/Step1_life2_WorldsX.lean): the state with one more token, for the empty string; `gap`:
Compile/Step1_life2_WorldsX.lean; the invariant: `WorldB.Inv`, Compile/Batch/WithinVCB.lean, also a
hypothesis: hI) -/
theorem session {pp : PProg lam L W.K} (hP : SafeProg W p pp) (m : Bool) (k : IskH lam L) (N₀ : ℕ)
    (xs : List X) (d : DSt (spec lam W.K L)) (hI : WorldB.Inv W p (some (k, N₀)) d) :
    ∀ y ∈ ((virt N₀ (gap N₀ d) (pp k xs)).run m (dummy d)).support,
      WorldB.Inv W p (some (k, N₀)) y.2 ∧
      ∀ o, y.2.nPlain o ≤ d.nPlain o + ePB o ∧ nEv y.2 o ≤ nEv d o + mPB W o := by
  obtain ⟨ht, hk, hm, hh⟩ := hI
  have hwf := wf_start ht hm
  have hV₁ := tidy_view_start ht hm
  have hkV₁ : IskOKB (view N₀ (gap N₀ d) (dummy d)) k :=
    WorldB.iskOK_of hk fun ts hts hc => closed_view_start ht hm hc fun t h => hh t (hts t h)
  intro y hy
  have hfr := frame_virt m _ _ hwf y hy
  have hmem : (y.1, view N₀ (gap N₀ d) y.2) ∈
      ((pp k xs).run m (view N₀ (gap N₀ d) (dummy d))).support := by
    rw [← run_virt m _ _ hwf]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩
  obtain ⟨hV', hkV', hg⟩ := safeRunO _ _ _ _ _ _ _ m (hP k xs _ hV₁ hkV₁) _ hmem
  refine ⟨⟨tidy_of_view (tidy_dummy ht) (gap_len hm) hfr hV',
      WorldB.iskOK_of hkV' fun ts hts hc => closed_of_view hfr.wf hc fun t h => hh t (hts t h),
      mid_of_view hfr hm.high hV₁ (length_view_start ht hm) hg,
      hh⟩,
    fun o => ⟨hg.plain o, ?_⟩⟩
  have h1 := nEv_split (N₀ := N₀) (δ := gap N₀ d) y.2 o
  have h2 := nEv_split (N₀ := N₀) (δ := gap N₀ d) (dummy d) o
  have h3 : nEv (dummy d) o = nEv d o := rfl
  have h4 : nEv (view N₀ (gap N₀ d) y.2) o ≤ nEv (view N₀ (gap N₀ d) (dummy d)) o + mPB W o :=
    hg.marked o
  rw [hfr.dead] at h1
  omega



end Prog


end Compile.Batch
