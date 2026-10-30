-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FileOwedMute.lean: `Owed` (Honest/Owed.lean) at the muted rows
`G.mute` (Honest/Law/Rule/Mute.lean), from the threads' debts without `YesS`. `file_owed`
(Honest/Thread/FileOwed.lean) gives `Owed` at rows `G` from the threads' debts and from `Good` at
every row's own letters. Where the rows' letters are the threads' own sentences, `Good.acc` at these
letters wants the debt `YesS`, that the sub-protocols' steps accept (`file_owed_hands`,
Honest/Thread/Hands.lean). At the muted rows `Good.plays` and `Good.acc` hold for nothing, so what
an owner hands in of `Good` at any letters serves, and `YesS` is not asked.

  1  `budDebts_mute`, `goodAt_mute_plain`   the debts on `bud` do not see the muting; `goodAt` at a
     muted list, from `Good` at any letters
  2  `file_owed_mute`   the rule

Limits.
  * The statement of `file_owed_mute` is that of `file_owed`, made by program: the premise `good`
    gives way to the three premises `hand₁`, `hand₂`, `hand₃` of `file_owed_hands`; every other
    premise stays, at `G`; the end is `Owed F Bk H G.mute Rel`.
  * The debts `OwesS` (`PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`), `SaidNext`, the seams (those
    on `Said` at the states as `ChainProgress.start` lays them), `OnFromS` and the debts on `bud` are
    premises as before. None is proved here.
  * Among the premises that stay and that the prose above does not name, in `file_owed_mute`: `plan`
    (`FileDescription.planOk`, the library's executable test); `book` (`ProverCoinCounts.word … = none`: every test on
    the book passes); `hq` (`sealPlain`: the first chain's last declared round lists no item but
    `.root`, and its entry's count of roots is 0); `hone` (`ready` is `.ok` at ONE input and one
    list of coins: some run can be made ready).
  * At the muted rows `plays` and `acc` are made idle on purpose. Whoever wants them takes `G`.
  * All limits of Honest/Thread/FileOwed.lean hold here. Its end is a record of premises of ours,
    and none of the library's goals.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FileOwed
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- The debts on `bud` do not see the muting. -/
theorem budDebts_mute {F : FileDescription Xi} {G : Sides F Bk W₀ Rc Ky Tr X₀ X} (h : BudDebts F Bk G) :
    BudDebts F Bk G.mute where
  bud₁ := fun L hL => by
    obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact h.bud₁ L₀ h₀
  bud₂ := fun L hL => by
    obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact h.bud₂ L₀ h₀
  bud₃ := fun L hL => by
    obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact h.bud₃ L₀ h₀

/-- `goodAt` at a muted list, from `Good` at any parameters: `fits`, `exact` and `fresh` are taken;
`plays` and `acc` hold vacuously. `goodAt_mute` (Honest/Law/Rule/Mute.lean) says the same with what
the field holds beside the muted list's A and B; `file_owed` takes the form without. -/
theorem goodAt_mute_plain {S Cl V W Y Pb : Type} {L : Lettered Bk S Cl V W Y Pb} {φ : Face V W Pb}
    {bs : List (Block S Cl)} {ord : List Place} {chain ft : Nat} {fs : List (Fall S)}
    {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (h : ∀ σ, L.side bs fs = some σ →
      ∃ A' B', Good (preOf chain ft earlier bs L.place) φ σ Bk ord chain ft A' B' L.On L.bud) :
    L.mute.goodAt earlier φ bs ord chain ft fs := by
  intro σ hσ
  obtain ⟨A', B', g⟩ := h σ hσ
  exact
    { fits := g.fits
      plays := fun _ _ _ _ _ hA => hA.elim
      acc := fun _ _ _ _ _ hA => hA.elim
      exact := g.exact
      fresh := g.fresh }

/-- **The rule at the muted rows**: `file_owed` without `Good` at the rows' own letters, and so
without `YesS`. A conditional lemma on our own definitions. Its end is a record of premises. -/
theorem file_owed_mute {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (T₁ : W₀ → Rc → Xi → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : W₀ → Rc → Xi → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : W₀ → Rc → Xi → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : W₀ → Rc → Xi → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : W₀ → Rc → Xi → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : W₀ → Rc → Xi → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (len : Nat → Nat → Nat)
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
    {w₁ : W₀} {rc₁ : Rc} {x₁ : Xi} {k₁ : Coins Bk} {R₁ : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hone : ready F Bk (G.prover H) w₁ rc₁ x₁ k₁ = .ok R₁)
    (hbud : BudDebts F Bk G)
    (htrue : ∀ w₀ rc x, Rel w₀ rc x → TrueLaid F (H.storedWords w₀ rc) len)
    (sits : ∀ w₀ rc x, Rel w₀ rc x →
      Sits F (G.prover H) (T₁ w₀ rc x) (T₂ w₀ rc x) (T₃ w₀ rc x))
    (o₁ : ∀ w₀ rc x, Rel w₀ rc x → OwesS (T₁ w₀ rc x) (S₁ w₀ rc x))
    (o₂ : ∀ w₀ rc x, Rel w₀ rc x → OwesS (T₂ w₀ rc x) (S₂ w₀ rc x))
    (o₃ : ∀ w₀ rc x, Rel w₀ rc x → OwesS (T₃ w₀ rc x) (S₃ w₀ rc x))
    (n₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ b, SaidNext (T₁ w₀ rc x) (S₁ w₀ rc x) b)
    (n₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ b, SaidNext (T₂ w₀ rc x) (S₂ w₀ rc x) b)
    (n₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ b, SaidNext (T₃ w₀ rc x) (S₃ w₀ rc x) b)
    (a₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₁ F (G.prover H) (T₁ w₀ rc x) w₀ rc x k R)
    (a₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₂ F (G.prover H) (T₂ w₀ rc x) w₀ rc x k R)
    (a₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehind F (G.prover H) (T₁ w₀ rc x) (T₂ w₀ rc x) (T₃ w₀ rc x) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ w₀ rc x 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ w₀ rc x 0 k { R.start₂ (G.prover H) with opened := some [] })
    (e₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ m₁ m₂ o₁ o₂, S₁ w₀ rc x F.first.blocksInOrder.length k m₁ →
        S₂ w₀ rc x F.shared.blocksInOrder.length k m₂ →
        m₁.opened = some o₁ → m₂.opened = some o₂ →
        S₃ w₀ rc x 0 k { R.start₃ (G.prover H) m₁ m₂
          with opened := some (o₁ ++ o₂) })
    (on₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₁ w₀ rc x) (S₁ w₀ rc x) L b len)
    (on₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₂ w₀ rc x) (S₂ w₀ rc x) L b len)
    (on₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₃ w₀ rc x) (S₃ w₀ rc x) L b len) :
    Owed F Bk H G.mute Rel := by
  have e := prover_mute G H
  refine file_owed (G := G.mute) T₁ T₂ T₃ S₁ S₂ S₃ len plan book ((seated_mute G).trans seats) hq ?_
    ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_⟩ input hst (w₁ := w₁) (rc₁ := rc₁) (x₁ := x₁)
    (k₁ := k₁) (R₁ := R₁) ?_ (budDebts_mute hbud) htrue ?_ o₁ o₂ o₃ n₁ n₂ n₃ ?_ ?_ ?_ ?_ ?_ ?_
    (fun w₀ rc x hr L hL b blk hb hp => ?_) (fun w₀ rc x hr L hL b blk hb hp => ?_)
    (fun w₀ rc x hr L hL b blk hb hp => ?_)
  · rw [e]
    exact hroot
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact goodAt_mute_plain (hand₁ L₀ h₀)
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact goodAt_mute_plain (hand₂ L₀ h₀)
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact goodAt_mute_plain (hand₃ L₀ h₀)
  · rw [e]
    exact hone
  · rw [e]
    exact sits
  · rw [e]
    exact a₁
  · rw [e]
    exact a₂
  · rw [e]
    exact a₃
  · rw [e]
    exact e₁
  · rw [e]
    exact e₂
  · rw [e]
    exact e₃
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact on₁ w₀ rc x hr L₀ h₀ b blk hb hp
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact on₂ w₀ rc x hr L₀ h₀ b blk hb hp
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact on₃ w₀ rc x hr L₀ h₀ b blk hb hp

end ProofFile.Honest

#print axioms ProofFile.Honest.budDebts_mute
#print axioms ProofFile.Honest.goodAt_mute_plain
#print axioms ProofFile.Honest.file_owed_mute
