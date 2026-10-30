-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/WithinVCB.lean: the setup and one batch of the compiled scheme obey the rules of
deferred programming and keep within the counts of ordinary and marked queries (`eCB`, `mCB`, `ePB`,
`mPB`, Compile/Batch/SpecDiscipline.lean), under these hypotheses: for the setup, `Spec.safeCB`,
from a well-formed state (`TidyO`); for a batch, `Spec.safePB` and L.maxBatchSize = 2 ^ W.depthReq, from a
state with the invariant `Inv`. (Words of this library: lean/GLOSSARY.md.)

The two conclusions are parts of the hypothesis of the lemma on deferred programming
(`Rom.Spec.defer`, Rom/Defer.lean). They follow from the statements `Spec.safeCB`, `Spec.safePB` on
the two programs, which are hypotheses here.

  `Inv`   the invariant of the challenger's private state and the state of the experiment
  `session`, `setup`   one batch with token numbers shifted (`virt`), the setup

Notation: `m`: a `Bool`: true is mode I, false is mode R (`Step.run`, Rom/Defer.lean); `k`, `N₀`: an
`IskH lam L` and a natural number: the first argument of `Inv` is `some (k, N₀)`; `fr`: a map
`ℕ → Bool`: for which requests a proof string is made at all (the head of Compile/Batch/Star.lean);
`xs`: a `List X`: the requests (`slotsOfReq`, Compile/Batch/Star.lean); `dummy d`: the state with
one more token, for the empty string; `gap N₀ d`: `d.vals.length + 1 - N₀`
(Compile/Step1_life2_WorldsX.lean); `virt N₀ δ c`: the program c under the renumbering
(Compile/Step1_life2_Virt.lean).

This file does not prove the statement for a run of a challenger, and no bound on the distance of
the two modes.

The generic parts are Compile/Batch/DisciplineVirt.lean (states and the shift) and
Compile/Batch/DisciplineWorld.lean (the induction on the adversary).
-/
import Compile.Batch.DisciplineVirt
import Compile.Batch.DisciplineStar
import Compile.Batch.DisciplineWorld
import Compile.Batch.DisciplineSumG
import Rom.DeferProof_tail
import Compile.Batch.SpecHop
import Rom.HopCost
import Compile.Batch.RealB

noncomputable section

namespace Compile.Batch.Disc
open Iop Rom Prob
open scoped ENNReal
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt run_bind run_fresh0)
open Compile.Life2.Many (view run_virt frame_virt)
open Compile.Life2.WorldsX (dummy gap)
open Compile.Disc (Rules nEv TreeTok)
open VirtO

/-- A well-formed state (`TidyO`) within the counts is within the bounds of the lemma on deferred
programming, for a set of oracles outside which the counts allow no marked query. -/
theorem withinO' : Spec.withinO' := fun _ _ d _ M os ht hz he hM =>
  ⟨ht.viol, he, hM, fun v hv => ⟨by
    by_contra hn
    have h1 : nEv d v.o ≤ 0 := hz v.o hn ▸ hM v.o
    have h2 : v ∈ d.evs.filter fun v' => decide (v'.o = v.o) := List.mem_filter.2 ⟨hv, by simp⟩
    have h3 : 0 < nEv d v.o := List.length_pos_of_mem h2
    omega, ht.bits v hv⟩⟩

namespace WorldB

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- The invariant. Before the setup the state is well-formed. After it: the state is well-formed,
the tokens of the key can be revealed, they are among the first N₀ tokens, and the queries keep the
first N₀ tokens and the later ones apart. -/
def Inv : Option (IskH lam L × ℕ) → DSt (spec lam W.K L) → Prop
  | none, d => TidyO (rulesB W.K L lam p) d
  | some (k, N₀), d =>
    TidyO (rulesB W.K L lam p) d ∧ IskOKB d k ∧ MidO N₀ d ∧ ∀ u, IskTokB k u → u < N₀

variable {W p}

/-- `IskOKB` carries over from one state to another if "can be revealed together" does, for lists of
tokens of the key. -/
theorem iskOK_of {d d' : DSt (spec lam W.K L)} {k : IskH lam L} (h : IskOKB d k)
    (hc : ∀ ts : List Tok, (∀ t ∈ ts, IskTokB k t) → ClosedO d ts → ClosedO d' ts) :
    IskOKB d' k := by
  refine ⟨fun s s' hs => hc _ (fun t ht => Or.inl ⟨s, s', hs, ?_⟩) (h.1 s s' hs),
      fun lf hlf s s' hs => hc _ (fun t ht => Or.inr ⟨lf, hlf, s, s', hs, ?_⟩) (h.2 lf hlf s s' hs)⟩
    <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    exact ht

theorem iskTok_lt {d : DSt (spec lam W.K L)} {k : IskH lam L} (h : IskOKB d k)
    {u : Tok} (hu : IskTokB k u) : u < d.vals.length := by
  rcases hu with hu | ⟨lf, hlf, hu⟩
  · exact h.1.lt hu
  · exact (h.2 lf hlf).lt hu

variable {WP}

/-- Under `Spec.safePB`, L.maxBatchSize = 2 ^ W.depthReq: one batch keeps the invariant and costs at most the
counts of one batch. -/
theorem session (hP : Spec.safePB) (hN : L.maxBatchSize = 2 ^ W.depthReq) (m : Bool) (k : IskH lam L) (N₀ : ℕ)
    (fr : ℕ → Bool) (xs : List X) (d : DSt (spec lam W.K L)) (hI : Inv W p (some (k, N₀)) d) :
    ∀ y ∈ ((virt N₀ (gap N₀ d) (Pp W WP p k fr xs)).run m (dummy d)).support,
      Inv W p (some (k, N₀)) y.2 ∧
      ∀ o, y.2.nPlain o ≤ d.nPlain o + ePB o ∧ nEv y.2 o ≤ nEv d o + mPB W o := by
  obtain ⟨ht, hk, hm, hh⟩ := hI
  have hwf := wf_start ht hm
  have hV₁ := tidy_view_start ht hm
  have hkV₁ : IskOKB (view N₀ (gap N₀ d) (dummy d)) k :=
    iskOK_of hk fun ts hts hc => closed_view_start ht hm hc fun t h => hh t (hts t h)
  intro y hy
  have hfr := frame_virt m _ _ hwf y hy
  have hmem : (y.1, view N₀ (gap N₀ d) y.2) ∈
      ((Pp W WP p k fr xs).run m (view N₀ (gap N₀ d) (dummy d))).support := by
    rw [← run_virt m _ _ hwf]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨y, hy, rfl⟩
  obtain ⟨hV', hkV', hg⟩ :=
    safeRunO _ _ _ _ _ _ _ m (hP I X lam L W WP p k fr xs _ hN hV₁ hkV₁) _ hmem
  refine ⟨⟨tidy_of_view (tidy_dummy ht) (gap_len hm) hfr hV',
      iskOK_of hkV' fun ts hts hc => closed_of_view hfr.wf hc fun t h => hh t (hts t h),
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

/-- Under `Spec.safeCB`, from a well-formed state: the setup establishes the invariant and costs at
most the counts of the committer. -/
theorem setup (hC : Spec.safeCB) (m : Bool)
    (d : DSt (spec lam W.K L)) (hI : TidyO (rulesB W.K L lam p) d) :
    ∀ y ∈ ((Cp W WP p i).run m d).support,
      Inv W p (some (y.1.2, y.2.vals.length)) (dummy y.2) ∧
      ∀ o, y.2.nPlain o ≤ d.nPlain o + eCB W p o ∧ nEv y.2 o ≤ nEv d o + mCB W p o := by
  intro y hy
  obtain ⟨ht, hk, hg⟩ := safeRunO _ _ _ _ _ _ _ m (hC I X lam L W WP p i d hI) y hy
  refine ⟨⟨tidy_dummy ht,
      iskOK_of hk fun ts _ hc => ⟨fun t h => ?_, hc.tail, hc.others⟩,
      ⟨?_, fun e he _ => ht.tail_lt e he,
        fun e he _ => ht.others_lt e he,
        fun e he hc => absurd (ht.charged_lt e he) (Nat.not_lt.mpr hc)⟩,
      fun u hu => iskTok_lt hk hu⟩,
    fun o => ⟨hg.plain o, hg.marked o⟩⟩
  · show t < (y.2.vals ++ [[]]).length
    rw [List.length_append]
    exact Nat.lt_add_right _ (hc.lt t h)
  · show y.2.vals.length ≤ (y.2.vals ++ [[]]).length
    simp

variable (W WP p)

/-- At most t queries in all are at most t queries to each oracle. -/
theorem bounded_of_totalBound {S : OSpec} {Out In α : Type} (A : Adv S Out In α) :
    ∀ (t N : ℕ) (f : S.ι → ℕ), (∀ o, t ≤ f o) → A.TotalBound t N → A.Bounded f N :=
  Rom.Adv.Bounded.of_total A

end WorldB

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)



end Compile.Batch.Disc
