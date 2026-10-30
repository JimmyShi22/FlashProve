-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RowsMute.lean: `Owed` (Honest/Owed.lean) at the muted rows, in
the two forms in which owners hand in: from what is handed in at every row (`file_owed_hands`,
Honest/Thread/Hands.lean), and at rows that are laid (`file_owed_rows`, Honest/Thread/Rows.lean).
Both without `YesS`. They call `file_owed_mute` (Honest/Thread/FileOwedMute.lean).

  1  `file_owed_hands_mute`   from what is handed in at every row
  2  `file_owed_rows_mute`   at rows that are laid

Limits.
  * Both statements are made by program. `file_owed_hands_mute` is the statement of
    `file_owed_hands` with its premises `y₁`, `y₂`, `y₃` (`YesS`) and `let₁`, `let₂`, `let₃` (how
    the rows' letters are laid) struck. `file_owed_rows_mute` is the statement of `file_owed_rows`
    with `y₁`, `y₂`, `y₃` struck. The end of both is `Owed F Bk H G.mute Rel`. Nothing else turns.
  * The proof of the first is the last call of the proof of `file_owed_hands`, at `file_owed_mute`.
  * At the muted rows `Good.plays` and `Good.acc` are made idle on purpose
    (Honest/Law/Rule/Mute.lean). Whoever wants them takes `G`.
  * All other premises stay premises. None is proved here. All limits of the two files named above
    hold here.
  * Among the premises that stay and that the prose above does not name, in both theorems: `hand₁`
    to `hand₃` (`Good` at `preOf` of the row's place); `e₁` to `e₃` (at the states as `ChainProgress.start`
    lays them); `plan` (`FileDescription.planOk`, the library's executable test); `book`
    (`ProverCoinCounts.word … = none`: every test on the book passes); `hq` (`sealPlain`: the first chain's last
    declared round lists no item but `.root`, and its entry's count of roots is 0); `hone` (`ready`
    is `.ok` at ONE input and one list of coins: some run can be made ready).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Rows
import Johnson.Desc.ProofFile.Honest.Thread.FileOwedMute

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- **The rule at the muted rows, from what is handed in at every row**, without `YesS`. A
conditional lemma on our own definitions. Its end is a record of premises. -/
theorem file_owed_hands_mute {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
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
    (sits : ∀ w w', Sits F (G.prover H) (T₁ w) (T₂ w') (T₃ w))
    (o₁ : ∀ w, OwesS (T₁ w) (S₁ w)) (o₂ : ∀ w, OwesS (T₂ w) (S₂ w))
    (o₃ : ∀ w, OwesS (T₃ w) (S₃ w))
    (n₁ : ∀ w b, SaidNext (T₁ w) (S₁ w) b) (n₂ : ∀ w b, SaidNext (T₂ w) (S₂ w) b)
    (n₃ : ∀ w b, SaidNext (T₃ w) (S₃ w) b)
    (a₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₁ F (G.prover H) (T₁ R.own) w₀ rc x k R)
    (a₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₂ F (G.prover H) (T₂ R.common) w₀ rc x k R)
    (a₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehind F (G.prover H) (T₁ R.own) (T₂ R.common) (T₃ R.own) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ R.own 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ R.common 0 k { R.start₂ (G.prover H) with opened := some [] })
    (e₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ m₁ m₂ o₁ o₂, S₁ R.own F.first.blocksInOrder.length k m₁ →
        S₂ R.common F.shared.blocksInOrder.length k m₂ →
        m₁.opened = some o₁ → m₂.opened = some o₂ →
        S₃ R.own 0 k { R.start₃ (G.prover H) m₁ m₂
          with opened := some (o₁ ++ o₂) })
    (on₁ : ∀ w, ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₁ w) (S₁ w) L b (depthAt F))
    (on₂ : ∀ w, ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₂ w) (S₂ w) L b (depthAt F))
    (on₃ : ∀ w, ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₃ w) (S₃ w) L b (depthAt F)) :
    Owed F Bk H G.mute Rel := by
  exact file_owed_mute (fun w₀ rc x => T₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
    (fun w₀ rc x => T₂ ((G.prover H).commonOf w₀ rc x))
    (fun w₀ rc x => T₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
    (fun w₀ rc x => S₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
    (fun w₀ rc x => S₂ ((G.prover H).commonOf w₀ rc x))
    (fun w₀ rc x => S₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x)) (depthAt F)
    plan book seats hq hroot hand₁ hand₂ hand₃ input hst hone hbud
    (fun w₀ rc _ _ => ⟨fun ρ p _ => trueTo_one F _ ρ p, fun ρ p _ => trueTo_two F _ ρ p,
      fun ρ p₀ p₁ p _ => trueTo_three F _ ρ p₀ p₁ p⟩)
    (fun _ _ _ _ => sits _ _) (fun _ _ _ _ => o₁ _) (fun _ _ _ _ => o₂ _) (fun _ _ _ _ => o₃ _)
    (fun _ _ _ _ => n₁ _) (fun _ _ _ _ => n₂ _) (fun _ _ _ _ => n₃ _)
    (fun w₀ rc x h k R hR => by
      show Enters₁ F (G.prover H) (T₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x)) w₀ rc x k R
      rw [← own_of_ready hR]
      exact a₁ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show Enters₂ F (G.prover H) (T₂ ((G.prover H).commonOf w₀ rc x)) w₀ rc x k R
      rw [← common_of_ready hR]
      exact a₂ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show DoorBehind F (G.prover H) (T₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
        (T₂ ((G.prover H).commonOf w₀ rc x)) (T₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x)) x k R
      rw [← own_of_ready hR, ← common_of_ready hR]
      exact a₃ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show S₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x) 0 k
        { R.start₁ (G.prover H) with opened := some [] }
      rw [← own_of_ready hR]
      exact e₁ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show S₂ ((G.prover H).commonOf w₀ rc x) 0 k { R.start₂ (G.prover H) with opened := some [] }
      rw [← common_of_ready hR]
      exact e₂ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show ∀ m₁ m₂ o₁ o₂, S₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x) F.first.blocksInOrder.length k m₁ →
        S₂ ((G.prover H).commonOf w₀ rc x) F.shared.blocksInOrder.length k m₂ →
        m₁.opened = some o₁ → m₂.opened = some o₂ →
        S₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x) 0 k { R.start₃ (G.prover H) m₁ m₂
          with opened := some (o₁ ++ o₂) }
      rw [← own_of_ready hR, ← common_of_ready hR]
      exact e₃ w₀ rc x h k R hR)
    (fun _ _ _ _ => on₁ _) (fun _ _ _ _ => on₂ _) (fun _ _ _ _ => on₃ _)

/-- **The rule at the muted rows, at rows that are laid**, without `YesS`. A conditional lemma on
our own definitions. Its end is a record of premises. -/
theorem file_owed_rows_mute {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (r₁ : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi))
    (r₂ : List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky))
    (r₃ : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi))
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hG : G = laySides F T₁ T₂ T₃ S₁ S₂ S₃ r₁ r₂ r₃ f₁ f₂ f₃)
    (plan : F.planOk = true) (book : Bk.word F = none)
    (seat₁ : ∀ r ∈ r₁, F.first.blocksInOrder.any (fun b => b.place == r.place) = true)
    (seat₂ : ∀ r ∈ r₂, F.shared.blocksInOrder.any (fun b => b.place == r.place) = true)
    (seat₃ : ∀ r ∈ r₃, F.second.blocksInOrder.any (fun b => b.place == r.place) = true)
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
    (sits : ∀ w w', Sits F (G.prover H) (T₁ w) (T₂ w') (T₃ w))
    (o₁ : ∀ w, OwesS (T₁ w) (S₁ w)) (o₂ : ∀ w, OwesS (T₂ w) (S₂ w))
    (o₃ : ∀ w, OwesS (T₃ w) (S₃ w))
    (n₁ : ∀ w b, SaidNext (T₁ w) (S₁ w) b) (n₂ : ∀ w b, SaidNext (T₂ w) (S₂ w) b)
    (n₃ : ∀ w b, SaidNext (T₃ w) (S₃ w) b)
    (a₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₁ F (G.prover H) (T₁ R.own) w₀ rc x k R)
    (a₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₂ F (G.prover H) (T₂ R.common) w₀ rc x k R)
    (a₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehind F (G.prover H) (T₁ R.own) (T₂ R.common) (T₃ R.own) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ R.own 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ R.common 0 k { R.start₂ (G.prover H) with opened := some [] })
    (e₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ m₁ m₂ o₁ o₂, S₁ R.own F.first.blocksInOrder.length k m₁ →
        S₂ R.common F.shared.blocksInOrder.length k m₂ →
        m₁.opened = some o₁ → m₂.opened = some o₂ →
        S₃ R.own 0 k { R.start₃ (G.prover H) m₁ m₂
          with opened := some (o₁ ++ o₂) })
    (on₁ : ∀ w, ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₁ w) (S₁ w) L b (depthAt F))
    (on₂ : ∀ w, ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₂ w) (S₂ w) L b (depthAt F))
    (on₃ : ∀ w, ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₃ w) (S₃ w) L b (depthAt F)) :
    Owed F Bk H G.mute Rel := by
  subst hG
  exact file_owed_hands_mute T₁ T₂ T₃ S₁ S₂ S₃ plan book (seated_lay seat₁ seat₂ seat₃) hq hroot
    hand₁ hand₂ hand₃ input hst hone hbud sits o₁ o₂ o₃ n₁ n₂ n₃ a₁ a₂ a₃ e₁ e₂ e₃ on₁ on₂ on₃

end ProofFile.Honest

#print axioms ProofFile.Honest.file_owed_hands_mute
#print axioms ProofFile.Honest.file_owed_rows_mute
