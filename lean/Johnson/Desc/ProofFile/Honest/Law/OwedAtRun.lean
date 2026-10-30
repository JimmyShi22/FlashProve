-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/OwedAtRun.lean: a rule for `Owed` (Honest/Owed.lean) that asks `On`
list by list, at a run that has returned, beside `owed_of_threads` (Honest/Law/OwedRule.lean). That
rule asks `OnDebts` of every list: `On` at every state and front that an invariant allows. This one
asks, of each list, `On` at the run's own rounds before a part that the run has called, with all that
`owed_part_first`, `owed_part_shared` and `owed_part_second` (Honest/Law/OwedParts.lean) hold there:
the state's place under the invariant, what it has seen, and besides: that the part was called, the
equation of `midAtW` or `midSharedAtW`, and that the front is the run's `beforeAt`. So a list may pay
by `OnDebts` (`onAtRun_of_onDebts`, one line) and another at the run: `owed_of_threads` is a corollary
(`owed_of_onDebts`).

  1  `Lettered.atRun`   a list whose `On` takes the three facts of a run as hypotheses
  2  `OnAtRun₁`, `OnAtRun₂`, `OnAtRun₃`   `On` at one run, of one list of each chain
  3  `onAtRun₁_of_onDebts`, `onAtRun₂_of_onDebts`, `onAtRun₃_of_onDebts`
  4  `runs_at_run`, `owed_at_run`   the fields `runs` and `owed`
  5  `owed_of_threads_at_run`, `owed_of_onDebts`   the rule at the lists; the corollary
  6  `owed_mute_of_threads_at_run`   the rule at the muted lists (Honest/Law/Rule/Mute.lean): of each
     side `Good` at any A and B

What is derived: `bud`, the carried blocks and the state. What is not: `On`. This rule moves that debt
and pays none of it: a conditional lemma on this folder's own functions.

Limits.
  * All of `owed_of_threads`'s (Honest/Law/OwedRule.lean), with `OnAtRun` for `OnDebts` in that head's
    fourth way: at `On` := the equation of `Good.exact` all content moves into the premise.
  * The muted end takes `Good` at any A and B: `plays` and `acc` then say nothing there. That no early
    part always refuses is not in this rule: it has to come from acceptance at the same F Bk H G, which
    no file states yet.
  * `ThreadsP`, `PartsStand`, `BudDebts` and the hands are premises.
  * `InsideOf` says of the field `opened` what the invariant says of it; the equation of `midAtW` says
    that the state is the walk's own: what follows of that field the payer proves.
  * The front holds all positions that ρ fixes, also of rounds behind the part, and no coin behind it:
    `Honest/Law/Rule/Row.lean`, limit 13.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.OwedRule
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X S Cl V W Y Pb : Type}

/-- **A list whose `On` takes three facts of a run as hypotheses**: that the part was called, that the
state is what `mid` returns at its address, and that the front is what `front₀` gives there. Its
place, parts and `bud` stay. -/
@[reducible] def Lettered.atRun {Bk : ProverCoinCounts} (L : Lettered Bk S Cl V W Y Pb) (called : Addr → Bool)
    (mid : Addr → Except Refusal (Mid W Y)) (front₀ : Addr → Before) :
    Lettered Bk S Cl V W Y Pb :=
  { L with
    On := fun u ca m front => called ⟨L.place, u.number⟩ = true →
      mid ⟨L.place, u.number⟩ = .ok m → front = front₀ ⟨L.place, u.number⟩ → L.On u ca m front }

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **`On` at one run, of one list of the first chain**, in the form of `owed_part_first`'s premise,
with three more hypotheses. -/
def OnAtRun₁ (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F)
    (L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop :=
  ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t, F.first.blocksInOrder = pre ++ σ.block :: t →
    ∀ m ca, InsideOf .own Bk 0 (G.prover H).first σ.block (T.I₁ pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (fun _ _ => none)
        (r.run.played.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))) →
    m.seen = roundsOf (r.run.played.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) →
    carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
    r.called ⟨L.place, u.number⟩ = true →
    orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    (laidOf F ρ (r.run.played.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) [] []).front 0
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) =
      r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, u.number⟩ →
    L.On u ca m ((laidOf F ρ
      (r.run.played.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) [] []).front 0
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))

/-- **The same, of one list of the shared chain.** -/
def OnAtRun₂ (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F)
    (L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky) : Prop :=
  ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.shared.blocksInOrder = pre ++ σ.block :: t →
    ∀ m ca, InsideOf .shared Bk 1 (G.prover H).shared σ.block (T.I₂ pre.length) (σ.roundsTo u.number)
      k m (envOf (H.storedWords w₀ rc) (fun _ _ => none)
        (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))) →
    m.seen =
      roundsOf (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) →
    carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
    r.called ⟨L.place, u.number⟩ = true →
    orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    (laidOf F ρ [] (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))
        []).front 1 (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) =
      r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, u.number⟩ →
    L.On u ca m ((laidOf F ρ []
      (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) []).front 1
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))

/-- **The same, of one list of the second chain.** -/
def OnAtRun₃ (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F)
    (L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop :=
  ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.second.blocksInOrder = pre ++ σ.block :: t →
    ∀ m ca, InsideOf .own Bk 2 (G.prover H).second σ.block (T.I₃ pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
        (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))) →
    m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
      roundsOf (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number)) →
    carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca →
    r.called ⟨L.place, u.number⟩ = true →
    orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    (laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))).front 2
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) =
      r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, u.number⟩ →
    L.On u ca m ((laidOf F ρ r.run.played.1 r.run.played.2.1
      (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + σ.roundsTo u.number))).front 2
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))

/-- `OnDebts` gives it at a list of the first chain. -/
theorem onAtRun₁_of_onDebts {T : ThreadsP F Bk (G.prover H) w₀ rc x k R} (D : OnDebts T)
    {ρ : Draws} (hρ : ρ.due F = true) (r : RunC F) :
    ∀ L ∈ G.first, OnAtRun₁ T ρ r L :=
  fun L hL σ hσ u hu pre t hc m ca hin hs hca _ _ _ =>
    D.on₁ L hL σ hσ u hu pre t hc ρ _ m ca hρ hin hs hca

/-- At a list of the shared chain. -/
theorem onAtRun₂_of_onDebts {T : ThreadsP F Bk (G.prover H) w₀ rc x k R} (D : OnDebts T)
    {ρ : Draws} (hρ : ρ.due F = true) (r : RunC F) :
    ∀ L ∈ G.shared, OnAtRun₂ T ρ r L :=
  fun L hL σ hσ u hu pre t hc m ca hin hs hca _ _ _ =>
    D.on₂ L hL σ hσ u hu pre t hc ρ _ m ca hρ hin hs hca

/-- At a list of the second chain. -/
theorem onAtRun₃_of_onDebts {T : ThreadsP F Bk (G.prover H) w₀ rc x k R} (D : OnDebts T)
    {ρ : Draws} (hρ : ρ.due F = true) (r : RunC F) :
    ∀ L ∈ G.second, OnAtRun₃ T ρ r L :=
  fun L hL σ hσ u hu pre t hc m ca hin hs hca _ _ _ =>
    D.on₃ L hL σ hσ u hu pre t hc ρ _ _ _ m ca hρ hin hs hca

end

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}

/-- **The field `runs`**, from the invariants. -/
theorem runs_at_run (plan : F.planOk = true) (hq : sealPlain F = true)
    (hroot : rootedAll F (G.prover H) = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R) :
    ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins Bk) ρ, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      ∃ r, runC F Bk (G.prover H) w₀ rc x k ρ = .ok r := fun w₀ rc x hrel k ρ hρ hsil => by
  obtain ⟨R, hR⟩ := hready w₀ rc x hrel k
  exact runC_returns hR hq hρ hsil (planServes hR plan hroot (hst w₀ rc x hrel))
    (T w₀ rc x hrel k R hR).I₁ (T w₀ rc x hrel k R hR).I₂ (T w₀ rc x hrel k R hR).I₃
    (T w₀ rc x hrel k R hR).h₁ (T w₀ rc x hrel k R hR).h₂ (T w₀ rc x hrel k R hR).h₃
    (T w₀ rc x hrel k R hR).a₁ (T w₀ rc x hrel k R hR).a₂ (T w₀ rc x hrel k R hR).a₃

/-- **The field `owed`**: `bud` and the blocks and state from the invariants, `On` from `OnAtRun`. -/
theorem owed_at_run (plan : F.planOk = true)
    (hroot : rootedAll F (G.prover H) = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (hW : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      PartsStand G k R)
    (hbud : BudDebts F Bk G)
    (hon : ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) ρ r, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
      (∀ L ∈ G.first, OnAtRun₁ (T w₀ rc x hrel k R hR) ρ r L) ∧
      (∀ L ∈ G.shared, OnAtRun₂ (T w₀ rc x hrel k R hR) ρ r L) ∧
      ∀ L ∈ G.second, OnAtRun₃ (T w₀ rc x hrel k R hR) ρ r L) :
    ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins Bk) ρ r, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
      (∀ L ∈ G.first, L.owedAt F.first.blocksInOrder k 0
        (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called) ∧
      (∀ L ∈ G.shared, L.owedAt F.shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called) ∧
      ∀ L ∈ G.second, L.owedAt F.second.blocksInOrder k 2
        (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called :=
  fun w₀ rc x hrel k ρ r hρ hsil h => by
    obtain ⟨R, hR⟩ := hready w₀ rc x hrel k
    have hPS := planServes hR plan hroot (hst w₀ rc x hrel)
    obtain ⟨O₁, O₂, O₃⟩ := hon w₀ rc x hrel k R hR ρ r hρ hsil h
    exact ⟨fun L hL σ hσ u hu => by
      obtain ⟨⟨pre, t, S⟩, hl⟩ := (hW w₀ rc x hrel k R hR).at₁ L hL σ hσ u hu
      have A := owed_part_first (L := L.atRun r.called
          (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a))
          (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)))
        h hR plan hρ hsil (T w₀ rc x hrel k R hR) (side_place hσ) S rfl hl
        (hbud.bud₁ L hL σ hσ u hu pre t _ S.cut rfl ρ hρ)
        (fun m ca hin hs hca hc hm hf => O₁ L hL σ hσ u hu pre t S.cut m ca hin hs hca hc hm hf)
      refine ⟨A.1, fun hc => ?_⟩
      obtain ⟨ca, m, h₁, h₂, h₃⟩ := A.2 hc
      exact ⟨ca, m, h₁, h₂, h₃ hc h₂ rfl⟩,
      fun L hL σ hσ u hu => by
      obtain ⟨⟨pre, t, S⟩, hl⟩ := (hW w₀ rc x hrel k R hR).at₂ L hL σ hσ u hu
      have A := owed_part_shared (L := L.atRun r.called
          (fun a => orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ a))
          (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)))
        h hR plan hρ hsil (T w₀ rc x hrel k R hR) (side_place hσ) S rfl hl
        (hbud.bud₂ L hL σ hσ u hu pre t _ S.cut rfl ρ hρ)
        (fun m ca hin hs hca hc hm hf => O₂ L hL σ hσ u hu pre t S.cut m ca hin hs hca hc hm hf)
      refine ⟨A.1, fun hc => ?_⟩
      obtain ⟨ca, m, h₁, h₂, h₃⟩ := A.2 hc
      exact ⟨ca, m, h₁, h₂, h₃ hc h₂ rfl⟩,
      fun L hL σ hσ u hu => by
      obtain ⟨⟨pre, t, S⟩, hl⟩ := (hW w₀ rc x hrel k R hR).at₃ L hL σ hσ u hu
      have A := owed_part_second (L := L.atRun r.called
          (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a))
          (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)))
        h hR plan hρ hsil hPS (T w₀ rc x hrel k R hR) (side_place hσ) S rfl hl
        (hbud.bud₃ L hL σ hσ u hu pre t _ S.cut rfl ρ hρ)
        (fun m ca hin hs hca hc hm hf => O₃ L hL σ hσ u hu pre t S.cut m ca hin hs hca hc hm hf)
      refine ⟨A.1, fun hc => ?_⟩
      obtain ⟨ca, m, h₁, h₂, h₃⟩ := A.2 hc
      exact ⟨ca, m, h₁, h₂, h₃ hc h₂ rfl⟩⟩

/-- **The rule for `Owed`, with `On` asked at the run.** A conditional lemma on this folder's own
functions, at parameters. Its conclusion is a structure of hypotheses: no property, and none of the
library's goals. -/
theorem owed_of_threads_at_run
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (good : (∀ L ∈ G.first, (L.withField 0 0 F.first.blocksInOrder [] 0).goodAt (earlierOf F 0) .own
          F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
      (∀ L ∈ G.shared, (L.withField 1 0 F.shared.blocksInOrder [] 0).goodAt (earlierOf F 1) .shared
          F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
      ∀ L ∈ G.second, ∀ base skip,
        (L.withField 2 F.lastChainFirstTreeNumber F.second.blocksInOrder base skip).goodAt (earlierOf F 2) .own
          F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (hW : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      PartsStand G k R)
    (hbud : BudDebts F Bk G)
    (hon : ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) ρ r, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
      (∀ L ∈ G.first, OnAtRun₁ (T w₀ rc x hrel k R hR) ρ r L) ∧
      (∀ L ∈ G.shared, OnAtRun₂ (T w₀ rc x hrel k R hR) ρ r L) ∧
      ∀ L ∈ G.second, OnAtRun₃ (T w₀ rc x hrel k R hR) ρ r L) :
    Owed F Bk H G Rel where
  plan := plan
  book := book
  places := ((F.planOk_ok).1 plan).places
  seats := seats
  good := good
  input := input
  runs := runs_at_run plan hq hroot hst hready T
  owed := owed_at_run plan hroot hst hready T hW hbud hon

/-- **`owed_of_threads` again**: `OnDebts` of every list, through the rule above. -/
theorem owed_of_onDebts
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (good : (∀ L ∈ G.first, (L.withField 0 0 F.first.blocksInOrder [] 0).goodAt (earlierOf F 0) .own
          F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
      (∀ L ∈ G.shared, (L.withField 1 0 F.shared.blocksInOrder [] 0).goodAt (earlierOf F 1) .shared
          F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
      ∀ L ∈ G.second, ∀ base skip,
        (L.withField 2 F.lastChainFirstTreeNumber F.second.blocksInOrder base skip).goodAt (earlierOf F 2) .own
          F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (hW : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      PartsStand G k R)
    (hbud : BudDebts F Bk G)
    (hon : ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R), OnDebts (T w₀ rc x hrel k R hR)) :
    Owed F Bk H G Rel :=
  owed_of_threads_at_run plan book seats hq hroot good input hst hready T hW hbud
    fun w₀ rc x hrel k R hR ρ r hρ _ _ =>
      ⟨onAtRun₁_of_onDebts (hon w₀ rc x hrel k R hR) hρ r,
        onAtRun₂_of_onDebts (hon w₀ rc x hrel k R hR) hρ r,
        onAtRun₃_of_onDebts (hon w₀ rc x hrel k R hR) hρ r⟩

/-- **The same at the muted lists**: of each side `Good` at any A and B. Its end is `Owed` at
`G.mute`, which is what `rule_views_mute` and `one_exact_at_mute` (Honest/Law/Rule/Mute.lean) take.
All its other premises are at `G`. -/
theorem owed_mute_of_threads_at_run
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (hand₁ : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder L.place) .own σ Bk (orderOf F) 0 0 A' B'
        L.On L.bud)
    (hand₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
        A' B' L.On L.bud)
    (hand₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk
        (orderOf F) 2 F.lastChainFirstTreeNumber A' B' L.On L.bud)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (hW : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      PartsStand G k R)
    (hbud : BudDebts F Bk G)
    (hon : ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) ρ r, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
      (∀ L ∈ G.first, OnAtRun₁ (T w₀ rc x hrel k R hR) ρ r L) ∧
      (∀ L ∈ G.shared, OnAtRun₂ (T w₀ rc x hrel k R hR) ρ r L) ∧
      ∀ L ∈ G.second, OnAtRun₃ (T w₀ rc x hrel k R hR) ρ r L) :
    Owed F Bk H G.mute Rel where
  plan := plan
  book := book
  places := ((F.planOk_ok).1 plan).places
  seats := (seated_mute G).trans seats
  good :=
    ⟨fun L hL => by
        obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
        exact goodAt_mute (hand₁ L₀ h₀),
      fun L hL => by
        obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
        exact goodAt_mute (hand₂ L₀ h₀),
      fun L hL base skip => by
        obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
        exact goodAt_mute (hand₃ L₀ h₀)⟩
  input := input
  runs := by
    rw [prover_mute]
    exact runs_at_run plan hq hroot hst hready T
  owed := by
    rw [prover_mute]
    intro w₀ rc x hrel k ρ r hρ hsil hrun
    obtain ⟨a, b, c⟩ := owed_at_run plan hroot hst hready T hW hbud hon w₀ rc x hrel k ρ r hρ hsil hrun
    refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_⟩
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact a L₀ h₀
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact b L₀ h₀
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact c L₀ h₀

end

end ProofFile.Honest

#print axioms ProofFile.Honest.Lettered.atRun
#print axioms ProofFile.Honest.OnAtRun₁
#print axioms ProofFile.Honest.OnAtRun₂
#print axioms ProofFile.Honest.OnAtRun₃
#print axioms ProofFile.Honest.onAtRun₁_of_onDebts
#print axioms ProofFile.Honest.onAtRun₂_of_onDebts
#print axioms ProofFile.Honest.onAtRun₃_of_onDebts
#print axioms ProofFile.Honest.runs_at_run
#print axioms ProofFile.Honest.owed_at_run
#print axioms ProofFile.Honest.owed_of_threads_at_run
#print axioms ProofFile.Honest.owed_of_onDebts
#print axioms ProofFile.Honest.owed_mute_of_threads_at_run
