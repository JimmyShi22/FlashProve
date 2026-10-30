-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OwedAtTheDoor.lean: the rule for Owed at the muted rows, with the premise at the second chain's start asked from the pair of
thread and what is said (DoorBehindS, Honest/Thread/FileD.lean), in the place of the pair DoorBehind and e₃.

1.  The proofs are those of Honest/Thread/FileOwed.lean, FileOwedMute.lean and RowsMute.lean, with that one change. threadsS built its field
    a₃ from DoorBehind and e₃; that field is DoorBehindS to the letter. So the premise d₃ stands in their place, and that pair
    gives it (doorBehindS_of).
2.  All other premises stay, by name. Nothing here proves DoorBehindS of any description.
3.  A conditional lemma on this library's definitions. Its end is a record of premises.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RowsMute
import Johnson.Desc.ProofFile.Honest.Thread.FileD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-! ## 3 The rule's structure, from the `Thread`s' hypotheses and the conditions where the chains
begin and meet -/

section
variable {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
  (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
  (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
  {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- The invariants are `ThrS`: a `Thread`'s invariant together with `Said`; `PlaysOn` is obtained
from the four hypotheses that say nothing of a fall, asked from `ThrS`, and from `SaidNext`; the
starts from the conditions where the chains begin and meet, `Said`'s (e₁, e₂) at the states as
`ChainProgress.start` lays them. -/
def threadsD (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true)
    (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃)
    (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (d₃ : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R)
    (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ H with opened := some [] }) : ThreadsP F Bk H w₀ rc x k R where
  I₁ := ThrS T₁ S₁
  I₂ := ThrS T₂ S₂
  I₃ := ThrS T₃ S₃
  h₁ := by
    intro j b hj
    obtain ⟨⟨p1, c1, f1, b1, h1⟩, -, -, t1, -, -⟩ := hS
    have hj' : T₁.bs[j]? = some b := by rw [b1]; exact hj
    have q := playsOn_of_owesS T₁ S₁ (by rw [b1]; exact t1)
      (by rw [b1]; exact (planOk_all hp).1) o₁ n₁ j b hj'
    rw [p1, c1, f1, h1] at q
    exact q
  h₂ := by
    intro j b hj
    obtain ⟨-, ⟨p2, c2, f2, b2, h2⟩, -, -, t2, -⟩ := hS
    have hj' : T₂.bs[j]? = some b := by rw [b2]; exact hj
    have q := playsOn_of_owesS T₂ S₂ (by rw [b2]; exact t2)
      (by rw [b2]; exact (planOk_all hp).2.1) o₂ n₂ j b hj'
    rw [p2, c2, f2, h2] at q
    exact q
  h₃ := by
    intro j b hj
    obtain ⟨-, -, ⟨p3, c3, f3, b3, h3⟩, -, -, t3⟩ := hS
    have hj' : T₃.bs[j]? = some b := by rw [b3]; exact hj
    have q := playsOn_of_owesS T₃ S₃ (by rw [b3]; exact t3)
      (by rw [b3]; exact (planOk_all hp).2.2) o₃ n₃ j b hj'
    rw [p3, c3, f3, h3] at q
    exact q
  a₁ := ⟨a₁, e₁⟩
  a₂ := ⟨a₂, e₂⟩
  a₃ := d₃

end

/-! ## 4 The rule's hypothesis on On -/

section
variable {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
  (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
  (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
  (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
  (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
  {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

theorem onDebts_of_onFromD {len : Nat → Nat → Nat} (hS : Sits F (G.prover H) T₁ T₂ T₃)
    (hp : F.planOk = true) (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃)
    (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (a₁ : Enters₁ F (G.prover H) T₁ w₀ rc x k R) (a₂ : Enters₂ F (G.prover H) T₂ w₀ rc x k R)
    (d₃ : DoorBehindS F (G.prover H) T₁ T₂ T₃ S₁ S₂ S₃ x k R)
    (e₁ : S₁ 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ (G.prover H) with opened := some [] })
    (htrue : TrueLaid F (H.storedWords w₀ rc) len)
    (on₁ : ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS T₁ S₁ L b len)
    (on₂ : ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS T₂ S₂ L b len)
    (on₃ : ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS T₃ S₃ L b len) :
    OnDebts (G := G) (H := H)
      (threadsD T₁ T₂ T₃ S₁ S₂ S₃ hS hp o₁ o₂ o₃ n₁ n₂ n₃ a₁ a₂ d₃ e₁ e₂) := by
  obtain ⟨⟨p1, c1, f1, b1, h1⟩, ⟨p2, c2, f2, b2, h2⟩, ⟨p3, c3, f3, b3, h3⟩, -, -, -⟩ := id hS
  exact {
  on₁ := by
    intro L hL σ hσ u hu pre t hcut ρ p m ca hρ hin hseen hca
    have hb : F.first.blocksInOrder[pre.length]? = some σ.block := by
      rw [hcut]
      simp
    refine on₁ L hL pre.length σ.block hb (side_place hσ) σ (by rw [b1]; exact hσ) u hu k m _ ca _
      (insideS_of_insideOf T₁ S₁ (by rw [b1]; exact hb)
        (by rw [p1, c1, h1]; exact hin)) (by rw [c1]; exact hca) ?_
    rw [c1, hseen]
    exact htrue.one ρ p hρ
  on₂ := by
    intro L hL σ hσ u hu pre t hcut ρ p m ca hρ hin hseen hca
    have hb : F.shared.blocksInOrder[pre.length]? = some σ.block := by
      rw [hcut]
      simp
    refine on₂ L hL pre.length σ.block hb (side_place hσ) σ (by rw [b2]; exact hσ) u hu k m _ ca _
      (insideS_of_insideOf T₂ S₂ (by rw [b2]; exact hb)
        (by rw [p2, c2, h2]; exact hin)) (by rw [c2]; exact hca) ?_
    rw [c2, hseen]
    exact htrue.two ρ p hρ
  on₃ := by
    intro L hL σ hσ u hu pre t hcut ρ p₀ p₁ p m ca hρ hin hseen hca
    have hb : F.second.blocksInOrder[pre.length]? = some σ.block := by
      rw [hcut]
      simp
    refine on₃ L hL pre.length σ.block hb (side_place hσ) σ (by rw [b3]; exact hσ) u hu k m _ ca _
      (insideS_of_insideOf T₃ S₃ (by rw [b3]; exact hb)
        (by rw [p3, c3, h3]; exact hin)) (by rw [c3]; exact hca) ?_
    rw [c3, hseen]
    exact htrue.three ρ p₀ p₁ p hρ }

end

/-- **The rule for `Owed` at a file, at the `Thread`s.** A conditional lemma on this library's
definitions. Its conclusion is a definition of this folder, a structure of hypotheses: no property,
and none of the library's goals. The ways to meet it trivially are in the head of Honest/Thread/FileOwed.lean; `TrueLaid`
is a hypothesis that no kind's author has to prove. -/
theorem file_owedD {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
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
    (good : (∀ L ∈ G.first, L.goodAt (earlierOf F 0) .own F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
      (∀ L ∈ G.shared, L.goodAt (earlierOf F 1) .shared F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
      ∀ L ∈ G.second,
        L.goodAt (earlierOf F 2) .own F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃)
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
    (d₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehindS F (G.prover H) (T₁ w₀ rc x) (T₂ w₀ rc x) (T₃ w₀ rc x) (S₁ w₀ rc x) (S₂ w₀ rc x)
        (S₃ w₀ rc x) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ w₀ rc x 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ w₀ rc x 0 k { R.start₂ (G.prover H) with opened := some [] })
    (on₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₁ w₀ rc x) (S₁ w₀ rc x) L b len)
    (on₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₂ w₀ rc x) (S₂ w₀ rc x) L b len)
    (on₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₃ w₀ rc x) (S₃ w₀ rc x) L b len) :
    Owed F Bk H G Rel :=
  owed_rule_one plan book seats hq hroot good input hst hone
    (fun w₀ rc x h k R hR => threadsD (T₁ w₀ rc x) (T₂ w₀ rc x) (T₃ w₀ rc x) (S₁ w₀ rc x)
      (S₂ w₀ rc x) (S₃ w₀ rc x) (sits w₀ rc x h) plan (o₁ w₀ rc x h) (o₂ w₀ rc x h) (o₃ w₀ rc x h)
      (n₁ w₀ rc x h) (n₂ w₀ rc x h) (n₃ w₀ rc x h) (a₁ w₀ rc x h k R hR) (a₂ w₀ rc x h k R hR)
      (d₃ w₀ rc x h k R hR) (e₁ w₀ rc x h k R hR) (e₂ w₀ rc x h k R hR))
    hbud
    fun w₀ rc x h k R hR => onDebts_of_onFromD (T₁ w₀ rc x) (T₂ w₀ rc x) (T₃ w₀ rc x)
      (S₁ w₀ rc x) (S₂ w₀ rc x) (S₃ w₀ rc x) (sits w₀ rc x h) plan (o₁ w₀ rc x h) (o₂ w₀ rc x h)
      (o₃ w₀ rc x h) (n₁ w₀ rc x h) (n₂ w₀ rc x h) (n₃ w₀ rc x h) (a₁ w₀ rc x h k R hR)
      (a₂ w₀ rc x h k R hR) (d₃ w₀ rc x h k R hR) (e₁ w₀ rc x h k R hR) (e₂ w₀ rc x h k R hR)
      (htrue w₀ rc x h) (on₁ w₀ rc x h) (on₂ w₀ rc x h) (on₃ w₀ rc x h)

/-- **The rule at the muted rows**: `file_owed` without `Good` at the rows' own letters, and so
without `YesS`. A conditional lemma on this library's definitions. Its end is a record of premises. -/
theorem file_owed_muteD {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
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
    (d₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehindS F (G.prover H) (T₁ w₀ rc x) (T₂ w₀ rc x) (T₃ w₀ rc x) (S₁ w₀ rc x) (S₂ w₀ rc x)
        (S₃ w₀ rc x) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ w₀ rc x 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ w₀ rc x 0 k { R.start₂ (G.prover H) with opened := some [] })
    (on₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₁ w₀ rc x) (S₁ w₀ rc x) L b len)
    (on₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₂ w₀ rc x) (S₂ w₀ rc x) L b len)
    (on₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS (T₃ w₀ rc x) (S₃ w₀ rc x) L b len) :
    Owed F Bk H G.mute Rel := by
  have e := prover_mute G H
  refine file_owedD (G := G.mute) T₁ T₂ T₃ S₁ S₂ S₃ len plan book ((seated_mute G).trans seats) hq ?_
    ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_⟩ input hst (w₁ := w₁) (rc₁ := rc₁) (x₁ := x₁)
    (k₁ := k₁) (R₁ := R₁) ?_ (budDebts_mute hbud) htrue ?_ o₁ o₂ o₃ n₁ n₂ n₃ ?_ ?_ ?_ ?_ ?_
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
    exact d₃
  · rw [e]
    exact e₁
  · rw [e]
    exact e₂
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact on₁ w₀ rc x hr L₀ h₀ b blk hb hp
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact on₂ w₀ rc x hr L₀ h₀ b blk hb hp
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact on₃ w₀ rc x hr L₀ h₀ b blk hb hp

/-- **The rule at the muted rows, from what is handed in at every row**, without `YesS`. A
conditional lemma on this library's definitions. Its end is a record of premises. -/
theorem file_owed_hands_muteD {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
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
    (d₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehindS F (G.prover H) (T₁ R.own) (T₂ R.common) (T₃ R.own) (S₁ R.own) (S₂ R.common)
        (S₃ R.own) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ R.own 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ R.common 0 k { R.start₂ (G.prover H) with opened := some [] })
    (on₁ : ∀ w, ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₁ w) (S₁ w) L b (depthAt F))
    (on₂ : ∀ w, ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₂ w) (S₂ w) L b (depthAt F))
    (on₃ : ∀ w, ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₃ w) (S₃ w) L b (depthAt F)) :
    Owed F Bk H G.mute Rel := by
  exact file_owed_muteD (fun w₀ rc x => T₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
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
      show DoorBehindS F (G.prover H) (T₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
        (T₂ ((G.prover H).commonOf w₀ rc x)) (T₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x))
        (S₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x)) (S₂ ((G.prover H).commonOf w₀ rc x))
        (S₃ ((G.prover H).ownOf R₁.own.trace w₀ rc x)) x k R
      rw [← own_of_ready hR, ← common_of_ready hR]
      exact d₃ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show S₁ ((G.prover H).ownOf R₁.own.trace w₀ rc x) 0 k
        { R.start₁ (G.prover H) with opened := some [] }
      rw [← own_of_ready hR]
      exact e₁ w₀ rc x h k R hR)
    (fun w₀ rc x h k R hR => by
      show S₂ ((G.prover H).commonOf w₀ rc x) 0 k { R.start₂ (G.prover H) with opened := some [] }
      rw [← common_of_ready hR]
      exact e₂ w₀ rc x h k R hR)
    (fun _ _ _ _ => on₁ _) (fun _ _ _ _ => on₂ _) (fun _ _ _ _ => on₃ _)

/-- **The rule at the muted rows, at rows that are laid**, without `YesS`. A conditional lemma on
this library's definitions. Its end is a record of premises. -/
theorem file_owed_rows_muteD {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
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
    (d₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehindS F (G.prover H) (T₁ R.own) (T₂ R.common) (T₃ R.own) (S₁ R.own) (S₂ R.common)
        (S₃ R.own) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ R.own 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ R.common 0 k { R.start₂ (G.prover H) with opened := some [] })
    (on₁ : ∀ w, ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₁ w) (S₁ w) L b (depthAt F))
    (on₂ : ∀ w, ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₂ w) (S₂ w) L b (depthAt F))
    (on₃ : ∀ w, ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₃ w) (S₃ w) L b (depthAt F)) :
    Owed F Bk H G.mute Rel := by
  subst hG
  exact file_owed_hands_muteD T₁ T₂ T₃ S₁ S₂ S₃ plan book (seated_lay seat₁ seat₂ seat₃) hq hroot
    hand₁ hand₂ hand₃ input hst hone hbud sits o₁ o₂ o₃ n₁ n₂ n₃ a₁ a₂ d₃ e₁ e₂ on₁ on₂ on₃

end ProofFile.Honest

#print axioms ProofFile.Honest.threadsD
#print axioms ProofFile.Honest.onDebts_of_onFromD
#print axioms ProofFile.Honest.file_owedD
#print axioms ProofFile.Honest.file_owed_muteD
#print axioms ProofFile.Honest.file_owed_hands_muteD
#print axioms ProofFile.Honest.file_owed_rows_muteD
