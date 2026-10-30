-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSharedSixOwed.lean: the second clause of what the field `owed` of `OwedRest`
(E2E/OfflineClauses.lean) concludes, at six of the eight rows of the offline prover's shared chain: at
a run of `runC` that has returned, at due challenges, On and bud hold at the run's own values. No
invariant of a thread is taken.

  `rounds_before_sending`   in front of either sending the shared list has a round
  `heard_at_sending`        so the state at which a called sending begins has heard a challenge
  `shared_six_owedAt`       `owedAt` at the six rows
  `shared_six_owed_mute`    the same at the muted rows, in the form of the field's second clause

By what. bud: AtFullSide/K14/Sim/AtKeyBud.lean's `six_bud_key`, the count of the key's written rounds,
at the run's challenges and positions in their closed form (`shared_part_at_run`,
E2E/OfflineOwedChains.lean). On: at the four own rows it asks nothing; at the two sendings it asks that
"LIN point" is not the round at which the part begins, and the state there has heard the shared
chain's challenges in front (`frame_at_run`, Honest/K12/Sim/FrameAtRun.lean).

Premises that stay. `KeySourced`, scope, that the public files' test says yes; the book's tests
(`ProverCoinCounts.word`); `K.AtAll`; `KeySendersAtTheDescription K`; what is laid at the six places;
`SharedSixLetters`. That `runC` returns is a premise of the clause itself. Nothing on any property.
-/
import E2E.OfflineSharedSixGood
import E2E.OfflineOwedChains
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Source LaterPlaces sharedPar beforeSharedPoint)
open Desc.K14 (St P14 blocks)
open Desc.K14.Honest (FlatOf)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver randK14)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK par_sourced plan2_full)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **In front of either sending the list has a round**: "LIN point"'s. -/
theorem rounds_before_sending {Cl : Type} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {xs : List (Block St Cl)}
    (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pre t : List (Block St Cl))
    (b : Block St Cl) (hx : xs = pre ++ b :: t)
    (hp : b.place = sendPlace 2 ∨ b.place = sendPlace 5) :
    0 < (pre.flatMap (·.rounds)).length := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨p1, -, -, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, r1, o1, -, -, -, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  have q1 : x1.place = place 1 := l1.place.trans p1
  match pre, hx with
  | [], hx =>
    have e : x0 = b := (List.cons.inj hx).1
    rw [← e, q0] at hp
    rcases hp with hp | hp <;> exact absurd hp (by decide)
  | [a], hx =>
    have e : x1 = b := (List.cons.inj (List.cons.inj hx).2).1
    rw [← e, q1] at hp
    rcases hp with hp | hp <;> exact absurd hp (by decide)
  | a :: a' :: pre', hx =>
    have e : x1 = a' := (List.cons.inj (List.cons.inj hx).2).1
    subst e
    simp [l1.rounds, r1]

section Letters
variable {W₀ Rc Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **`owedAt` at the six rows of the shared chain**, at a run that has returned, at due challenges. -/
theorem shared_six_owedAt {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {Bk : ProverCoinCounts} (book : Bk.word (keyFileDescription Xs N Pl) = none)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtAll) (hQ : KeySendersAtTheDescription K)
    (S : OfflineSimulators) (hS : SimsAtSix K S.byChain.shared)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SharedSixLetters K c) (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit)
    (w₀ : W₀) (rc : Rc) (x : KeyInst) (k : Coins Bk) (ρ : Draws)
    (r : RunC (keyFileDescription Xs N Pl)) (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) (st : List (Nat × Nat × List UInt64)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, SixPlace L.place →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ a)) r.run st r.called := by
  have plan := hs.named.plan
  intro L hL hp
  obtain ⟨g, hg, eL⟩ := List.mem_map.1 hL
  have hp' : SixPlace g.place := by rw [← eL] at hp; exact hp
  rw [keyRows_half] at hg
  have hrow : ∃ q ∈ keyRows K, L.place = q.place ∧ L.row = q.row ∧ L.On = q.On ∧ L.bud = q.bud := by
    rcases List.mem_append.1 hg with g' | g'
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 g'
      refine ⟨q, hq, ?_, ?_, ?_, ?_⟩
      · rw [← eL]; rfl
      · rw [← eL]; exact shared_row_is K _ hS hA.splits q hq
      · rw [← eL]; exact (hc.each q hq).1
      · rw [← eL]; exact (hc.each q hq).2
    · exfalso
      have apart : ∀ p : Place, p.kind = .K12 → ¬ SixPlace p := by
        intro p hk hs'
        rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at g'
      rcases g' with rfl | rfl
      · exact apart _ (by rw [hA.onU]; rfl) hp'
      · exact apart _ (by rw [hA.onOmega]; rfl) hp'
  obtain ⟨q, hq, c1, c2, c3, c4⟩ := hrow
  have hqQ := keyRows_mem_QK K hQ q hq
  refine owedAt_shared_at plan book h hL st ?_ ?_
  · -- On
    intro σ hσ u hu hcall ca m _ hm
    rw [c3]
    rcases List.mem_append.1 hqQ with o | o
    · have e : q.On = k14On := by
        unfold ownRows at o
        rcases List.mem_append.1 o with o | o
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at o
          rcases o with rfl | rfl | rfl <;> rfl
        · split at o
          · obtain rfl := List.mem_singleton.1 o
            rfl
          · cases o
      rw [e]
      trivial
    · have hplace : q.place = sendPlace 2 ∨ q.place = sendPlace 5 := by
        unfold sendingRows at o
        simp only [List.mem_cons, List.not_mem_nil, or_false] at o
        rcases o with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hOn : q.On u ca m (r.run.beforeAt st ⟨L.place, u.number⟩) =
          pointApart ⟨QK, 0⟩ m.st.heard := by
        unfold sendingRows at o
        simp only [List.mem_cons, List.not_mem_nil, or_false] at o
        rcases o with rfl | rfl <;> rfl
      rw [hOn]
      obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, -⟩ := runC_parts h
      obtain ⟨-, hst⟩ := shared_stands plan book hR L hL σ hσ
      obtain ⟨⟨pre, t, St'⟩, -⟩ := hst u hu
      have hbp := side_place hσ
      obtain ⟨m', hm', -, hheard, -⟩ := ProofFile.Honest.K12.Light.frame_at_run plan hR h σ u pre t
        (σ.roundsTo u.number) _ St' rfl (by rw [hbp]; exact hcall) st
      rw [hbp] at hm'
      have em : m = m' := by
        have := orRefused_some hm'
        exact Except.ok.inj (hm.symm.trans this)
      have e := par_sourced hs scope
      obtain ⟨layO, hP⟩ := plan2_full
      obtain ⟨B⟩ := hP.eight
      have hb : blocks (sharedPar Xs.chains (beforeSharedPoint Pl)) =
          some [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
        rw [e]
        exact B.made
      have hpos := rounds_before_sending (flatOf_key Xs.chains Pl hb) hb pre t σ.block St'.cut
        (by rw [hbp, c1]; exact hplace)
      have hlen : ρ.shared.length = ((keyFileDescription Xs N Pl).shared.blocksInOrder.flatMap (·.rounds)).length := by
        unfold Draws.due at hρ
        simp only [Bool.and_eq_true] at hρ
        exact drawsFit_length _ _ hρ.1.1.2
      have hlen' : 0 < ρ.shared.length := by
        rw [hlen, St'.cut, List.flatMap_append, List.length_append]
        exact Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ _)
      show (0 : Nat) ≠ m.st.heard.length
      rw [em, hheard, List.length_take]
      exact Nat.ne_of_lt (Nat.lt_min.2
        ⟨Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ _), hlen'⟩)
  · -- bud
    intro σ hσ u hu
    obtain ⟨-, ⟨pre, t, hcut, hd, ha⟩, -⟩ := shared_part_at_run plan book h hL hσ hu
    rw [hd, ha]
    exact six_bud_key hs scope live K.lin Bk K.weights (fun c => randK14 (K.rand c)) q hqQ L c1 c2 c4
      σ hσ u hu pre t _ hcut rfl ρ hρ

/-- **The six rows in the form of the second clause of what `OwedRest.owed` concludes.** -/
theorem shared_six_owed_mute {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {Bk : ProverCoinCounts} (book : Bk.word (keyFileDescription Xs N Pl) = none)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtAll) (hQ : KeySendersAtTheDescription K)
    (S : OfflineSimulators) (hS : SimsAtSix K S.byChain.shared)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SharedSixLetters K c) (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit)
    (w₀ : W₀) (rc : Rc) (x : KeyInst) (k : Coins Bk) (ρ : Draws)
    (r : RunC (keyFileDescription Xs N Pl)) (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x
      k ρ = .ok r) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.shared, SixPlace L.place →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  rw [prover_mute] at h ⊢
  intro L hL hp
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  exact (owedAt_mute L' _ _ _ _ _ _ _).2
    (shared_six_owedAt hs scope live book K hA hQ S hS c hc H w₀ rc x k ρ r hρ h _ L' hL' hp)

end Letters

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.rounds_before_sending
#print axioms AtPublicFiles.OfflineRows.shared_six_owedAt
#print axioms AtPublicFiles.OfflineRows.shared_six_owed_mute
