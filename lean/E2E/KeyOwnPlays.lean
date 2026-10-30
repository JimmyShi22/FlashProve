-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnPlays.lean: the frame's sentence "it plays", whole, at a member that seats a proximity test behind the guard: the
twin of `playsS_k12_below` (K12/SeatedPlaysS.lean) at the half `needsField`, over `playsOn_guarded`
(K12/FieldGuardLift.lean). `PlayedTo` and `tableBy` take the state at which the chain begins as a parameter: at a start
whose field is some, the guard lets the moves through.

Main names.
  `playsS_mono`: `PlaysS` at one letter gives it at a stronger one.
  `K12PlayedGuarded`: `K12PlayedSBelow` with the guarded half, and a start whose field is some.
  `opened_of_played`: a state that play reaches from such a start has its field.
  `playsS_guarded`: `K12PlayedGuarded` gives 'PlaysS T (PlayedTo T start) b'.

What stays open. `K12PlayedGuarded` is asked; no thread is shown to meet it.
Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.K12.SeatedPlaysS
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (PlayedTo tableBy sentAt sent_of_tableBy playsS_by_play_below sentIn Listed)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **`PlaysS` at one letter gives it at a stronger one.** -/
theorem playsS_mono {T : Thread Bk S Cl V W X Pb} {Said Said' : ℕ → Coins Bk → Mid W X → Prop} {b : ℕ}
    (hS : ∀ k m, Said b k m → Said' b k m) (h : PlaysS T Said' b) : PlaysS T Said b :=
  fun blk hb k s m E ds l hT hd hst hl => h blk hb k s m E ds l ⟨hT.1, hS k m hT.2⟩ hd hst hl

/-- **The premises, at the half behind the guard.** -/
structure K12PlayedGuarded (T : Thread Bk S Cl V W X Pb)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (sent : ℕ) : Prop where
  member : ∃ blk, T.bs[b]? = some blk ∧ SeatOf blk J enter leave
  half : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J : Placed V W X).needsField
  startOpen : ∀ k w h, (start k w h).opened.isSome = true
  stages : ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g ∧
    PlanPlays J s (t :: rest) sent
  stands : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]),
    ThrS T (PlayedTo T start) b k st m E →
    drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c →
    RunPlays J sent m E c
  tables : ∀ j, j < treesTo T.bs T.bs.length → ∀ k w h u, h.length = T.fixed (.own j) →
    sentAt T start j k w h = some u →
    u.1 = (T.table (.own j) k w h).1 ∧ u.2.same (T.table (.own j) k w h).2 = true
  fixed : ∀ j, j < treesTo T.bs T.bs.length →
    T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j
  listed : ∀ x ∈ T.bs, Listed x
  laid : ∀ (k : Coins Bk) (w : W), ∃ Lall,
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs = .ok Lall

/-- **A state that `play` reaches from a start with its field has it.** -/
theorem opened_of_played {T : Thread Bk S Cl V W X Pb} {start : Coins Bk → W → List Fmt.Drawn → Mid W X}
    (h : ∀ k w h, (start k w h).opened.isSome = true) {b : ℕ} {k : Coins Bk} {m : Mid W X}
    (hp : PlayedTo T start b k m) : m.opened.isSome = true := by
  obtain ⟨L, ps, -, hy⟩ := hp
  have e := play_opened _ _ _ _ _ hy
  have e' : m.opened = (start k m.st.input (m.st.heard.take T.front)).opened := e
  rw [e']
  exact h _ _ _

/-- **It plays, and its new trees are the thread's tables, behind the guard.** -/
theorem playsS_guarded (T : Thread Bk S Cl V W X Pb)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (sent : ℕ) (h : K12PlayedGuarded (V := V) T start b J enter leave sent) :
    PlaysS T (PlayedTo T start) b := by
  obtain ⟨s, t, rest, hst, hk, P⟩ := h.stages
  obtain ⟨blk, hblk, hseat⟩ := h.member
  have hpl := hseat.place
  have hp : ((proverSideOfProximityTest J : Placed V W X).place == J.p.place) = true := by
    show (J.p.place == J.p.place) = true
    exact beq_self_eq_true _
  have f1 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J : Placed V W X) := by
    simp [List.find?, hp]
  have f2 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J : Placed V W X) := by
    rw [hpl]
    exact f1
  have hf : (T.hs.find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J : Placed V W X).needsField := by
    rw [hpl]
    exact h.half
  have hP := playsOn_guarded (hs := T.hs) (hs' := [(proverSideOfProximityTest J : Placed V W X)])
    (proverSideOfProximityTest J) hf f2 (fun k s m E hT => opened_of_played h.startOpen hT.2)
    (playsOn_k12 T.φ Bk T.chain T.ft [proverSideOfProximityTest J] blk J enter leave hseat
      (ThrS T (PlayedTo T start) b) (fun _ _ _ _ => True) s t rest hst hk f1 sent P h.stands
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
  refine playsS_by_play_below T start h.tables h.fixed h.listed hblk
    (g := (proverSideOfProximityTest J : Placed V W X).needsField) hf h.laid fun k st m E ds l hT hd hstop hl => ?_
  obtain ⟨y, cols, hy, hc, -⟩ := hP k st m E ds l hT hd hstop hl
  exact ⟨y, cols, ⟨l, hl, hy⟩, hc⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.playsS_mono
#print axioms ProofFile.Honest.K12.opened_of_played
#print axioms ProofFile.Honest.K12.playsS_guarded
