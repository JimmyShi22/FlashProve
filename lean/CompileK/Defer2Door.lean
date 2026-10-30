-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Door.lean: the lemma on deferred programming of the random oracle (`Rom.Spec.defer2`,
CompileK/SpecDefer2.lean) applied to the scheme's challenger.
The step of `PubG.hopUOf`
(Compile/Batch/PubProgMainBGr.lean), here with the sharper lemma
(CompileK/SpecDefer2.lean): under the premises told below, mode R of the challenger with the prover
with free empty slots (VCBPG .. (PpU ..)) is within `costU2 W p B t n` of mode I of the challenger
with the base prover (VCBPG .. (Pp ..)): the counts `eAllB`, `mAllU`, one budget t, and the two
vertex oracles at 2 λ bits for λ.

Statement `Compile.Batch.Disc.Spec.hopU2` and its proof. The premises are `hopUOf`'s own (2^depthReq
slots; batches of at most B requests; t queries in all, n + 1 calls; an admissible adversary),
without its parameter h and its premise `HopU`. Nothing assumed beyond the hypotheses of the
statements, in the random-oracle model, on Lean's three axioms. Programs, states and the two modes:
Rom/Defer.lean. The challenger `VCBPG W WP p pw P i` (Compile/Batch/PubProg.lean) runs the committer
`Cp` at the first call "setup" and, after the setup, if `hasOwn b`, the prover program P behind
`virt` at a call "batch"; `Pp` (Compile/Batch/Star.lean) and `PpU` (Compile/Batch/StarU.lean) are
two such programs. In this file the door, or the passage, is the step from mode R to mode I; the
inequality at the door is what `Spec.hopU2` states (as a premise: `HopDoor`,
CompileK/Defer2Main.lean); its price is the bound, here `costU2`.

The proof, in five steps, each lemma under the hypotheses of its statement:
  1. `tidy2_view_start`, `upClosed_view_start`, `upClosed_of_view`: what a batch sees at its start,
    and the key's handles at its end: the way upwards (companions of `tidy_view_start`,
    `closed_view_start`, `closed_of_view`, Compile/Batch/DisciplineVirt.lean).
  2. `Inv2`; `door_step`: every step of VCBPG .. (Pp ..) has `Step.Alw` with `DSt.Ok2` on the way
    and keeps `Inv2` (`safeCB2`, `safePB2`: CompileK/Defer2ChainAll.lean; `virt_of_safeO2`:
    CompileK/Defer2Virt.lean); `door_alw1`: `AdvAlw` (nothing asked at a halt) there, for every
    adversary.
  3. `door_rel_step`: from a step of the first challenger to the step of the second
    (`PubG.skip_batch`: the second's step is the first's without work that is never shown;
    `alw_skip`, `ok2_skip`: CompileK/Defer2Skip.lean; the invariant of `PubG.step` at the first's
    ends by `alw_supp`); `door_alw2`: `AdvAlw` (nothing asked at a halt) at VCBPG .. (PpU ..)
    (`advAlw_rel`: CompileK/Defer2Rel.lean, at the relation `ModeI.RelW`).
  4. `door_alw3`: the counts at a halt are those of `PubG.within₂`, `countRunU`, by `advAlw_supp`
    (CompileK/Defer2Supp.lean).
  5. `hopU2`: `Rom.DeferTail2.defer2`; mode I of the two challengers agree (`PubG.modeI_cpl`).

Limits:
`zetaT` (Cond/ObjBounds.lean) has the hash term `hashTerms2` (its summands `muB2`, `hashSqBG2`).
`zetaT0`
(Cond/ObjBounds.lean) has the summands `muB`, `hashSqBG`.
Between this door and ζ stand the five theorems that take "hh : HopU W p B h" (`realToWrBPUTOf`,
`closePubUTOf`, `privacyPubGrWithUOf`, `privacyKEGrWithBOf`, `mainBatchKEGrWithBOf`)
and the statements in which `hashTermsBGTot`
stands. Their twins, where they have one, stand in CompileK/Defer2Main.lean,
CompileK/Defer2Cost.lean, CompileK/Defer2Work.lean,
Cond/Defer2Obj.lean;
for `zetaT` none is
needed: it itself has `hashTerms2`. Two proofs give `mainBatchKEGrWithBOf` its `HopU`: in
CompileK/Glue.lean and CompileK/WideMain.lean.
`costU2` is a formula, not evaluated.
Only the vertices gain: the chains' oracles (fb, its further names, g), the leaves' and the request
leaves' stay at the rules' bits.
`hopU2` is not a `HopU`: it is a statement on this challenger. `HopU` speaks of every challenger
within the counts; the sharper lemma (`Rom.Spec.defer2`) has a further hypothesis on the way, which
such a challenger need not meet: CompileK/Defer2Guard.lean: guard3; in the larger library guard5
(two vertices with the same second token); the guard's file is not in this library.
-/
import CompileK.Defer2
import CompileK.Defer2Supp
import CompileK.Defer2Skip
import CompileK.Defer2Rel
import CompileK.Defer2Virt
import CompileK.Defer2ChainAll
import Compile.Batch.PubProgMainBGr
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom Rom.DeferTail Rom.DeferTail2
open Compile.Life2 (virt up down vis vis_iff vis_up down_up up_down viewShown)
open Compile.Life2.Many
open Compile.Life2.WorldsX (mem_viewShown down_of_lt lt_of_down_lt dummy gap)
open Compile.GlueB (GCall GAdm)
open Compile.Disc (Rules nEv TreeTok afterFresh)
open VirtO

/-! ## 1. What a batch sees at its start, and the key's handles at its end: the way upwards.
Generic. -/

section Generic
variable {S : OSpec} {Rl : Rules S} {Jo : S.ι → Bool} {ℓ2 : S.ι → ℕ} {N₀ δ : ℕ}

theorem val_view_start {D : DSt S} (ht : TidyO Rl D) (h : MidO N₀ D) {v : ℕ} (hv : v < N₀) :
    (view N₀ (gap N₀ D) (dummy D)).val v = D.val v := by
  rw [val_view (wf_start ht h), show up N₀ (gap N₀ D) v = v from if_pos hv]
  exact Compile.Disc.val_of_prefix
    (d := D) (d' := dummy D) (List.prefix_append _ _) (lt_of_lt_of_le hv h.len)

/-- Under the hypotheses below: what a new batch sees is orderly upwards. -/
theorem tidy2_view_start {D : DSt S} (ht : TidyO Rl D) (h2 : Tidy2 Jo ℓ2 D) (h : MidO N₀ D) :
    Tidy2 Jo ℓ2 (view N₀ (gap N₀ D) (dummy D)) := by
  intro x hx hJ
  obtain ⟨e, he, hc, -, hl, ho, -, h1, -, h3, -⟩ := ev_view_start ht h hx
  obtain ⟨b, hb, hlen, hsn⟩ := h2 e he (ho ▸ hJ)
  have hbN : b < N₀ := hl b (by rw [hb]; exact List.mem_singleton.2 rfl)
  refine ⟨b, h3.trans hb, ?_, fun hs => ?_⟩
  · rw [ho, h1, val_view_start ht h hc, val_view_start ht h hbN]
    exact hlen
  · rw [h1]
    exact (shown_view_start ht h _).2 ⟨hc, hsn ((shown_view_start ht h _).1 hs).2⟩

theorem upClosed_view_start {D : DSt S} (ht : TidyO Rl D) (h : MidO N₀ D)
    {ts : List Tok} (hc : UpClosed Jo D ts) :
    UpClosed Jo (view N₀ (gap N₀ D) (dummy D)) ts := by
  intro x hx hJ b hb hbt
  obtain ⟨e, he, hcN, -, -, ho, -, h1, -, h3, -⟩ := ev_view_start ht h hx
  rw [h1]
  exact (hc e he (ho ▸ hJ) b (h3 ▸ hb) hbt).imp_right fun hs =>
    (shown_view_start ht h _).2 ⟨hcN, hs⟩

theorem upClosed_of_view {D' : DSt S} (hwf : WF N₀ δ D') {ts : List Tok}
    (hc : UpClosed Jo (view N₀ δ D') ts) (hts : ∀ t ∈ ts, t < N₀) : UpClosed Jo D' ts := by
  intro e he hJ b hb hbt
  have hbN := hts b hbt
  have hbvis : vis N₀ δ b = true := (vis_iff _ _ _).2 (Or.inl hbN)
  by_cases hvis : vis N₀ δ e.charged = true
  · have hb' : b ∈ (ren N₀ δ e).others := List.mem_map.2 ⟨b, hb, down_of_lt hbN⟩
    rcases hc (ren N₀ δ e) (mem_viewEvs.2 ⟨e, he, hvis, rfl⟩) hJ b hb' hbt with h1 | h1
    · have h2 : down N₀ δ e.charged ∈ ts := h1
      have h3 : e.charged < N₀ := lt_of_down_lt hvis (hts _ h2)
      rw [down_of_lt h3] at h2
      exact Or.inl h2
    · have h2 : up N₀ δ (down N₀ δ e.charged) ∈ D'.shown := mem_viewShown.1 h1
      rw [up_down N₀ δ hvis] at h2
      exact Or.inr h2
  · have hvis' : vis N₀ δ e.charged = false := by simpa using hvis
    have := hwf.evs.unseen e he hvis' b hb
    rw [hbvis] at this
    exact Bool.noConfusion this

end Generic

/-! ## 2. The first challenger: the base prover behind the translation -/

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (pw : IVK lam L → WKey lam L → V) (i : I)

/-- The invariant, both ways. -/
def Inv2 : Option (IskH lam L × ℕ) → DSt (spec lam W.K L) → Prop
  | none, d => TidyBoth p (maxMoreB W) d
  | some (k, N₀), d =>
    TidyBoth p (maxMoreB W) d ∧ IskOKB2 d k ∧ MidO N₀ d ∧ ∀ u, IskTokB k u → u < N₀

variable {W p}

theorem iskOK2_of {d d' : DSt (spec lam W.K L)} {k : IskH lam L} (h : IskOKB2 d k)
    (hc : ∀ ts : List Tok, (∀ t ∈ ts, IskTokB k t) → ClosedBoth d ts → ClosedBoth d' ts) :
    IskOKB2 d' k := by
  refine ⟨fun s s' hs => hc _ (fun t ht => Or.inl ⟨s, s', hs, ?_⟩) (h.1 s s' hs),
      fun lf hlf s s' hs => hc _ (fun t ht => Or.inr ⟨lf, hlf, s, s', hs, ?_⟩) (h.2 lf hlf s s' hs)⟩
    <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    exact ht

theorem iskTok_lt2 {d : DSt (spec lam W.K L)} {k : IskH lam L} (h : IskOKB2 d k)
    {u : Tok} (hu : IskTokB k u) : u < d.vals.length := by
  rcases hu with hu | ⟨lf, hlf, hu⟩
  · exact h.1.lt hu
  · exact (h.2 lf hlf).lt hu

theorem Inv2.table {s : Option (IskH lam L × ℕ)} {d : DSt (spec lam W.K L)}
    (h : Inv2 W p s d) (T : Table (spec lam W.K L)) :
    Inv2 W p s { d with table := T } := by
  rcases s with _ | ⟨k, N₀⟩
  · exact ⟨h.1.table T, h.2.table T⟩
  · exact ⟨⟨h.1.1.table T, h.1.2.table T⟩,
      iskOK2_of h.2.1 fun ts _ hc => ⟨⟨hc.1.lt, hc.1.tail, hc.1.others⟩, hc.2⟩,
      ⟨h.2.2.1.len, h.2.2.1.tails, h.2.2.1.low, h.2.2.1.high⟩,
      h.2.2.2⟩

variable (W p)

abbrev okD : DSt (spec lam W.K L) → Prop :=
  DSt.Ok2 (clO _) Jt (bits2 (rulesT W.K L lam p (maxMoreB W)) Jt (ellT lam)) (osBG (maxMoreB W))

/-- Under `hN` and `hI`: every step of the challenger with the base prover has the hypothesis on the
way, and keeps the invariant. -/
theorem door_step (hN : L.maxBatchSize = 2 ^ W.depthReq) (s : Option (IskH lam L × ℕ)) (c : GCall X Unit)
    (d : DSt (spec lam W.K L)) (hI : Inv2 W p s d) :
    ((VCBPG W WP p pw (Pp W WP p) i).step s c).Alw (clO _) Jt (okD W p) d fun y =>
      Inv2 W p y.1.2 y.2 := by
  have hks : ∀ o q, (rulesT W.K L lam p (maxMoreB W)).Mk o q → o ∈ osBG (maxMoreB W) := fun _ _ h =>
    h
  rcases c with _ | b
  · rcases s with _ | k
    · rw [HopRPG.VCBP_setupG W WP p pw (Pp W WP p) i]
      refine alw_bind _ _ d
        (alw_mono (fun y hy => ?_) _ _
          (alw_of_safeO2 _ _ _ _ Jt (ellT lam) _ hks (Cp W WP p i)
            d _ hI.1 hI.2 (safeCB2 I X lam L W WP p i d hI)))
      obtain ⟨⟨ht, hk, -⟩, -, -⟩ := hy
      intro u
      have hu : List.ofFn u = ([] : Bits) := by simp
      show Inv2 W p (some (y.1.2, y.2.vals.length)) (postFresh y.2 (List.ofFn u))
      rw [hu]
      refine ⟨ht.fresh [],
        iskOK2_of hk fun ts _ hc =>
          hc.grows (GrowsO.ofFresh (Ch := NoTok) (R := NoTok) (e := zr) (M := zr) y.2 [])
            fun _ _ h => h,
        ⟨?_, fun e he _ => ht.1.tail_lt e he,
          fun e he _ => ht.1.others_lt e he,
          fun e he hc => absurd (ht.1.charged_lt e he) (Nat.not_lt.mpr hc)⟩,
        fun u hu => iskTok_lt2 hk hu⟩
      show y.2.vals.length ≤ (y.2.vals ++ [[]]).length
      simp
    · exact hI
  · rcases s with _ | ⟨k, N₀⟩
    · exact hI
    · by_cases hb : hasOwn b = true
      · rw [HopRPG.VCBP_ownG W WP p pw (Pp W WP p) i k N₀ b hb]
        obtain ⟨ht, hk, hm, hh⟩ := hI
        intro u
        have hu : List.ofFn u = ([] : Bits) := by simp
        show Step.Alw _ _ _ ((virt N₀ (gap N₀ d) (Pp W WP p k (ownFlag b) (reqs b))).bind _)
          (postFresh d (List.ofFn u)) _
        rw [hu]
        have hV₁ := tidy_view_start ht.1 hm
        have hV₂ := tidy2_view_start ht.1 ht.2 hm
        have hkV₁ : IskOKB2 (view N₀ (gap N₀ d) (dummy d)) k :=
          iskOK2_of hk fun ts hts hc =>
            ⟨closed_view_start ht.1 hm hc.1 fun t h => hh t (hts t h),
              upClosed_view_start ht.1 hm hc.2⟩
        refine alw_bind _ _ _
          (alw_mono (fun y hy => ?_) _ _
            (virt_of_safeO2 _ _ _ N₀ (gap N₀ d) _ Jt (ellT lam) _ hks
              (Pp W WP p k (ownFlag b) (reqs b)) (dummy d) _ (VirtO.tidy_dummy ht.1)
              (Tidy2.fresh ht.1 ht.2 []) (gap_len hm) (wf_start ht.1 hm) hV₁ hV₂
              (safePB2 I X lam L W WP p k (ownFlag b) (reqs b) _ hN ⟨hV₁, hV₂⟩ hkV₁)))
        obtain ⟨hfr, ⟨-, hkV', hg⟩, -, hT1, hT2⟩ := hy
        exact ⟨⟨hT1, hT2⟩,
          iskOK2_of hkV' fun ts hts hc =>
            ⟨closed_of_view hfr.wf hc.1 fun t h => hh t (hts t h),
              upClosed_of_view hfr.wf hc.2 fun t h => hh t (hts t h)⟩,
          mid_of_view hfr hm.high hV₁ (length_view_start ht.1 hm) hg,
          hh⟩
      · rw [HopRPG.VCBP_noneG W WP p pw (Pp W WP p) i k N₀ b (by simpa using hb)]
        exact hI

/-- `AdvAlw` (nothing asked at a halt) at the challenger with the base prover, for every adversary.
(not all hypotheses are named here: see the statement below) -/
theorem door_alw1 (hN : L.maxBatchSize = 2 ^ W.depthReq) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
    AdvAlw (VCBPG W WP p pw (Pp W WP p) i) (clO _) Jt (okD W p)
      (fun _ => True) A (none, DSt.init _) :=
  advAlw_of_inv (VCBPG W WP p pw (Pp W WP p) i) (fun _ => True)
    (fun _ (s : Option (IskH lam L × ℕ) × DSt (spec lam W.K L)) => Inv2 W p s.1 s.2)
    (fun _ _ _ => trivial) (fun _ _ _ h _ => h) (fun _ _ _ _ h _ T => h.table T)
    (fun m _ s h => door_step W WP p pw i hN s.1 m s.2 h) A _ tidyBoth_init

/-! ## 3. The second challenger: the prover with free empty slots -/

/-- One step, from the first challenger to the second. -/
theorem door_rel_step (hN : L.maxBatchSize = 2 ^ W.depthReq) (s₁ s₂ : ModeI.WSt W) (c : GCall X Unit)
    (Post₁ : (BInP V lam L × Option (IskH lam L × ℕ)) × DSt (spec lam W.K L) → Prop)
    (h : ModeI.RelW W p s₁ s₂)
    (hA : ((VCBPG W WP p pw (Pp W WP p) i).step s₁.1 c).Alw (clO _) Jt (okD W p) s₁.2 Post₁) :
    ((VCBPG W WP p pw (PpU W WP p) i).step s₂.1 c).Alw (clO _) Jt (okD W p) s₂.2 fun y₂ =>
      ∃ y₁, y₁.1.1 = y₂.1.1 ∧ ModeI.RelW W p (y₁.1.2, y₁.2) (y₂.1.2, y₂.2) ∧ Post₁ y₁ := by
  obtain ⟨τ₁, d₁⟩ := s₁
  obtain ⟨τ₂, d₂⟩ := s₂
  obtain ⟨hτ, hI, hm⟩ := h
  have hτ' : τ₁ = τ₂ := hτ
  subst hτ'
  have hst := PubG.step W WP p pw i (safeFPp W WP p hN) true τ₁ d₁ c hI
  have hA' := alw_supp _ _ _ _ _ _ _ _ _ Post₁
    (fun y => Post₁ y ∧ Compile.Batch.Spec.InvD W p y.1.2 y.2)
    hA (fun y hy hp => ⟨hp, (hst y hy).1⟩)
  rcases c with _ | b
  · rcases τ₁ with _ | ⟨k, N₀⟩
    · have e : d₁ = d₂ := hm
      subst e
      exact alw_mono (fun y hy => ⟨y, rfl, ModeI.RelW.refl hy.2, hy.1⟩) _ _ hA'
    · exact ⟨((.inr [], some (k, N₀)), d₁), rfl, ⟨rfl, hI, hm⟩, hA⟩
  · rcases τ₁ with _ | ⟨k, N₀⟩
    · exact ⟨((.inr [], none), d₁), rfl, ⟨rfl, hI, hm⟩, hA⟩
    · obtain ⟨w, hs, g₁, g₂, hid⟩ := hm
      have hsk := (PubG.skip_batch
          W WP p pw i (skipFPpU W WP p) k N₀ b w hI.2 hI.1.2.2.2 g₁ g₂ hid).keep (Wd.le_refl w)
      refine alw_mono (fun y₂ hy => ?_) _ _
        (alw_skip _ _ _ _ _ _ (fun w d₁ d₂ h => ok2_skip _ _ _ _ _ _ w d₁ d₂ h)
          _ _ _ w _ _ hsk _ d₁ d₂ hs hA')
      obtain ⟨y₁, w', ⟨hw, heq, hk⟩, hs', hp, hI'⟩ := hy
      exact ⟨y₁,
        congrArg (fun z : BInP V lam L × Option (IskH lam L × ℕ) => z.1) heq,
        ModeI.RelW.mk_some hk
          (congrArg (fun z : BInP V lam L × Option (IskH lam L × ℕ) => z.2) heq).symm hI' w' hs'
          (g₁.trans hw.n₁) (g₂.trans hw.n₂) fun a ha => hw.ρ _ _ (hid a ha),
        hp⟩

/-- `AdvAlw` (nothing asked at a halt) at the challenger with the prover with free empty slots, for
every adversary. (not all hypotheses are named here: see the statement below) -/
theorem door_alw2 (hN : L.maxBatchSize = 2 ^ W.depthReq) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
    AdvAlw (VCBPG W WP p pw (PpU W WP p) i) (clO _) Jt (okD W p)
      (fun _ => True) A (none, DSt.init _) :=
  advAlw_rel _ _ _ _ _ _ _ _ _ (VCBPG W WP p pw (Pp W WP p) i) (VCBPG W WP p pw (PpU W WP p) i)
    (ModeI.RelW W p) (fun _ _ h => h.table) (fun _ _ T h => h.setTable T)
    (fun s₁ s₂ m Post₁ h hA => door_rel_step W WP p pw i hN s₁ s₂ m Post₁ h hA) A
    (none, DSt.init _) (none, DSt.init _)
    (ModeI.RelW.refl (τ := none)
      (show Compile.Batch.Spec.InvD W p none (DSt.init _) from Or.inl rfl))
    (door_alw1 W WP p pw i hN A)

/-- `AdvAlw` at the challenger with the prover with free empty slots, with the counts `eAllB`,
`mAllU` at a halt. -/
theorem door_alw3 (hN : L.maxBatchSize = 2 ^ W.depthReq) (B : ℕ) (ok : ZKCP.Gen.Batch X Unit → Prop)
    (hok : ∀ b, ok b → b.pairs.length ≤ B) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (n : ℕ) (hA : GAdm ok A false n) :
    AdvAlw (VCBPG W WP p pw (PpU W WP p) i) (clO _) Jt (okD W p)
      (DSt.CntK2 (clO _) (eAllB W p n) (mAllU W p B n)) A (none, DSt.init _) :=
  advAlw_supp _ _ _ _ _ _ _ _ _ _ _ A _ (door_alw2 W WP p pw i hN A) fun x hx =>
    ⟨(PubG.within₂ W WP p pw i (safeFPp W WP p hN) (skipFPpU W WP p) ok A n hA x hx).2.1,
      countRunU W WP p pw i hN ok hok A n true hA x hx⟩

open scoped ENNReal in
/-- The bound of `Spec.hopU2` on the distance of mode R from mode I: the price of one passage to
fresh answers at the counts of the scheme with free empty slots, the vertices at 2 λ. -/
def costU2 (B t n : ℕ) : ℝ≥0∞ :=
  (t : ℝ≥0∞) *
      (osBG (maxMoreB W)).sup (fun o =>
        (mAllU W p B n o : ℝ≥0∞) / 2 ^ bits2 (rulesT W.K L lam p (maxMoreB W)) Jt (ellT lam) o) +
    ∑ o ∈ osBG (maxMoreB W), (mAllU W p B n o : ℝ≥0∞) * (eAllB W p n o + mAllU W p B n o : ℕ) /
      2 ^ bits2 (rulesT W.K L lam p (maxMoreB W)) Jt (ellT lam) o

/-- States: under the premises that the head tells, mode R of the challenger with `PpU` is within
`costU2 W p B t n` of mode I of the challenger with `Pp`. -/
def Spec.hopU2 : Prop :=
  ∀ (I X V : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (pw : IVK lam L → WKey lam L → V) (i : I),
    L.maxBatchSize = 2 ^ W.depthReq →
    ∀ (B : ℕ) (ok : ZKCP.Gen.Batch X Unit → Prop), (∀ b, ok b → b.pairs.length ≤ B) →
      ∀ (α : Type) (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (t n : ℕ),
        A.TotalBound t (n + 1) → GAdm ok A false n →
        Prob.tv ((interact ((VCBPG W WP p pw (PpU W WP p) i).world false)
              A (none, DSt.init _)).map Prod.fst)
            ((interact ((VCBPG W WP p pw (Pp W WP p) i).world true) A (none, DSt.init _)).map
              Prod.fst) ≤ costU2 W p B t n

theorem hopU2 : Spec.hopU2 := by
  intro I X V lam L W WP p pw i hN B ok hok α A t n hT hA
  rw [Rom.Cpl.map_eq _ _
      ((PubG.modeI_cpl W WP p pw i (safeFPp W WP p hN) (skipFPpU W WP p) A).mono fun _ _ h => h.1)]
  exact defer2 _ _ _ _ _ _ (VCBPG W WP p pw (PpU W WP p) i) none A t (eAllB W p n) (mAllU W p B n) _
    (n + 1) (osBG (maxMoreB W)) (clO _) Jt hT (door_alw3 W WP p pw i hN B ok hok A n hA)

end Compile.Batch.Disc
