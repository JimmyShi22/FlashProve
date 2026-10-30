-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FileOwed.lean: the rule for `Owed` at a file, at the `Thread`s.
`Owed` (Honest/Owed.lean) is the structure of hypotheses that a statement on lists of parts takes.
The rule at parameters is `owed_of_threads` (Honest/Law/OwedRule.lean), in the form `owed_rule_one`
(Honest/Law/StandsFile.lean), which proves generally where the parts' rounds are, and that `ready`
returns at all coins from one return of it. Here it is applied at the `Thread`s: so that what a
kind's author supplies at its sub-protocol is said in the hypotheses of Honest/Thread/: from the
executable tests; one return of `ready`; `Good` at every side, at the value of its parameter `pre`
that the list's place gives (`preOf`, Honest/Rule.lean, at `earlierOf F`, Honest/Owed.lean); the
four hypotheses that say nothing of a fall, and `SaidNext`, at every sub-protocol of the three
chains; the conditions where the chains begin and meet (those on `Said`, e₁ to e₃, at the states as
`ChainProgress.start` lays them: e₁, e₂ where no column has been opened; e₃ where the two ends' fields
`opened` are `some o₁` and `some o₂`, at `some (o₁ ++ o₂)`; those on the invariants, a₁ to a₃, at
the states that `ready` gives: `Thr` does not read the field); and two hypotheses for each side: its
bound at every list of challenges that the rounds can draw, and `OnFromS`: On follows from the
invariant and `Said`. Its conclusion is a definition of this folder, no property, and none of the
library's goals.

  1  `TrueLaid`   a hypothesis that no kind's author has to prove: the `front` that a run's rounds
     give is true to these rounds
  2  `insideS_of_insideOf`   `InsideOf` (Honest/Law/Inside.lean), at `ThrS`, is `InsideS`
  3  `threadsS`   the rule's structure of invariants and of `PlaysOn`, from the `Thread`s'
     hypotheses and the conditions where the chains begin and meet
  4  `onDebts_of_onFromS`   the rule's hypothesis on On (`OnDebts`), from `OnFromS` and `TrueLaid`
  5  `file_owed`   the rule at the `Thread`s

The `Thread`s are a family in (what all requests share, the stored tables' pads and encoding
randomness, the instance), and so are the parameters `Said`: the conditions where the chains begin
and meet can be met only at `Thread`s that fix the input to the run's own (the head of
Honest/Thread/File.lean).

What a kind's author then supplies, at its sub-protocol number b with its list L: of `Good`: `fits`,
`exact`, `fresh`; `Plays`, `Behind`, its part of `Exchange` and of `RidesPast`; `SaidNext` for its
own clause of the chain's `Said`, at the one sub-protocol that establishes it
(Honest/Thread/Said.lean: `SaidAt`); `OnFromS` at the same On, at len := `depthAt F`, with: depthAt
F c j is at most the logLength of its `Thread`'s table at each tree (c, j) that its On reads; its
bound. `Good` and `OnFromS` count together, at one On, or not at all. Where the part's simulator
reads nothing of `front`: On := True: `OnFromS`, its clause of `Said` and len then ask nothing. Of
`Good.plays` and `Good.acc`: this file's hypothesis `good` asks them at the list's own parameters
L.A, L.B (`Owed.good` asks them with the field's clause beside both, `Lettered.withField`;
`owed_of_threads` goes from the one to the other by `Lettered.goodAt_withField`,
Honest/FieldFree.lean), which are fields of one structure for all inputs, while the `Thread`s are a
family in the input: this file's proofs name neither field, and at L.A := False they hold vacuously:
what really states them is `Plays` and, for acceptance, `Accepted`.

Met trivially: the seven ways of the head of Honest/Law/OwedRule.lean; those of the heads of
Honest/Thread/OnFrom.lean, Honest/Thread/OnSaid.lean and Honest/Thread/Said.lean. `TrueLaid` is a
hypothesis here, which no kind's author has to prove: it is a theorem at len := `depthAt F`
(Honest/Law/Rule/TrueLaid.lean: `trueTo_one`, `trueTo_two`, `trueTo_three`; joined in
Honest/Thread/Hands.lean), it is proved at no other len in this folder. One way in for On: `OnFromS`
at every list: an author whose On reads more of `front` than `TrueTo` says proves the clause of the
rule at parameters itself (`OnDebts`): no rule is stated that takes some lists the one way and some
the other. Two more hypotheses, which no kind's author proves at a sub-protocol: on the inputs
(`input`: in range, with a trace): whoever supplies Rel; on the stored columns (`hst`): whoever
fills `Prover.stored`.

Limits.
  * Applications of other lemmas alone.
  * Nothing of `acc` but what `good` passes through, and nothing of a stop's measure, is in it; this
    file's proofs read no fall's test or share.
  * Among the hypotheses that the prose above does not name: `FileDescription.planOk` (the library's
    executable test): `onDebts_of_onFromS`, `file_owed`; `sealPlain` (the first chain's last
    declared round declares no item except roots, and no root): `file_owed`; `ProverCoinCounts.word … = none`
    (every test on the book passes): `file_owed`.
  * `OwesS` and `OnFromS` are asked at every value of the state's field `opened` that `Said` allows
    (`Thr` does not read it): unless `Said` shuts them out, at `none` and at lists of columns that
    no run opens. At a prover with a part that reads the columns and errs at `none` (its duty:
    Honest/Frame.lean, `Seen.opened`), `PlaysS` at a `Said` that lets `none` through before that
    part's sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits). Of the field
    `OnFromS` has in hand only what `Said` says of it at the border before the sub-protocol. The
    same of `good`: `plays` and `acc` are asked at every value of the field that L.A allows
    (Honest/FieldFree.lean, Limits).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OnSaid
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Law.StandsFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-! ## 1 A hypothesis that no kind's author has to prove -/

/-- **The `front` that rounds as produced give is true to these rounds**, chain by chain, at every
list of challenges that the rounds can draw: the closed form of what a part is shown (`laidOf`,
Honest/Law/Rule/Words.lean) against `TrueTo` (Honest/Thread/OnFrom.lean). `stored`: the stored
tables' columns. `len`: the depth at which the plan opens a tree. It is a structure of hypotheses:
generic: no kind's author has to prove it. Nothing is claimed of it. -/
structure TrueLaid (F : FileDescription Xi) (stored : Nat → Nat → Option (List UInt64))
    (len : Nat → Nat → Nat) : Prop where
  one : ∀ (ρ : Draws) (p : List Played), ρ.due F = true →
    TrueTo 0 len ((laidOf F ρ p [] []).front 0 (storedShown stored (storedAsks F ρ))) (roundsOf p)
      (envOf stored (fun _ _ => none) p)
  two : ∀ (ρ : Draws) (p : List Played), ρ.due F = true →
    TrueTo 1 len ((laidOf F ρ [] p []).front 1 (storedShown stored (storedAsks F ρ))) (roundsOf p)
      (envOf stored (fun _ _ => none) p)
  three : ∀ (ρ : Draws) (p₀ p₁ p : List Played), ρ.due F = true →
    TrueTo 2 len ((laidOf F ρ p₀ p₁ p).front 2 (storedShown stored (storedAsks F ρ)))
      (roundsOf p₀ ++ roundsOf p₁ ++ roundsOf p) (envOf stored (taken₃ p₀ p₁) p)

/-! ## 2 The two definitions of "inside a sub-protocol" -/

theorem insideS_of_insideOf {S Cl V W Y Pb : Type} (T : Thread Bk S Cl V W Y Pb)
    (Said : Nat → Coins Bk → Mid W Y → Prop) {b n : Nat} {blk : Block S Cl} {k : Coins Bk}
    {m : Mid W Y} {E : Env} (hblk : T.bs[b]? = some blk)
    (h : InsideOf T.φ Bk T.chain T.hs blk (ThrS T Said b) n k m E) : InsideS T Said b n k m E := by
  unfold InsideOf at h
  obtain ⟨s, m₀, E₀, l, ds, y, ⟨hT, hs₀⟩, h2, h3, h4, h5, h6⟩ := h
  unfold InsideS
  exact ⟨blk, s, m₀, E₀, l, ds, y, hblk, hT, hs₀, h2, h3, h4, h5, h6⟩

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
starts from the conditions where the chains begin and meet, `Said`'s (e₁, e₂, e₃) at the states as
`ChainProgress.start` lays them. -/
def threadsS (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true)
    (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃)
    (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (a₃ : DoorBehind F H T₁ T₂ T₃ x k R)
    (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ H with opened := some [] })
    (e₃ : ∀ m₁ m₂ o₁ o₂, S₁ F.first.blocksInOrder.length k m₁ →
      S₂ F.shared.blocksInOrder.length k m₂ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃ 0 k { R.start₃ H m₁ m₂
        with opened := some (o₁ ++ o₂) }) : ThreadsP F Bk H w₀ rc x k R where
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
  a₃ := fun v₁ m₁ E₁ v₂ m₂ E₂ s₃ q₁ q₂ u₁ u₂ hs g₁ g₂ =>
    ⟨a₃ v₁ m₁ E₁ v₂ m₂ E₂ s₃ u₁.1 u₂.1 hs, e₃ m₁ m₂ q₁ q₂ u₁.2 u₂.2 g₁ g₂⟩

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

theorem onDebts_of_onFromS {len : Nat → Nat → Nat} (hS : Sits F (G.prover H) T₁ T₂ T₃)
    (hp : F.planOk = true) (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃)
    (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (a₁ : Enters₁ F (G.prover H) T₁ w₀ rc x k R) (a₂ : Enters₂ F (G.prover H) T₂ w₀ rc x k R)
    (a₃ : DoorBehind F (G.prover H) T₁ T₂ T₃ x k R)
    (e₁ : S₁ 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ (G.prover H) with opened := some [] })
    (e₃ : ∀ m₁ m₂ o₁ o₂, S₁ F.first.blocksInOrder.length k m₁ →
      S₂ F.shared.blocksInOrder.length k m₂ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃ 0 k { R.start₃ (G.prover H) m₁ m₂
        with opened := some (o₁ ++ o₂) })
    (htrue : TrueLaid F (H.storedWords w₀ rc) len)
    (on₁ : ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS T₁ S₁ L b len)
    (on₂ : ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS T₂ S₂ L b len)
    (on₃ : ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS T₃ S₃ L b len) :
    OnDebts (G := G) (H := H)
      (threadsS T₁ T₂ T₃ S₁ S₂ S₃ hS hp o₁ o₂ o₃ n₁ n₂ n₃ a₁ a₂ a₃ e₁ e₂ e₃) := by
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

/-! ## 5 The rule at the `Thread`s -/

/-- **The rule for `Owed` at a file, at the `Thread`s.** A conditional lemma on this folder's own
definitions. Its conclusion is a definition of this folder, a structure of hypotheses: no property,
and none of the library's goals. The ways to meet it trivially are in this file's head; `TrueLaid`
is a hypothesis that no kind's author has to prove. -/
theorem file_owed {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
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
    Owed F Bk H G Rel :=
  owed_rule_one plan book seats hq hroot good input hst hone
    (fun w₀ rc x h k R hR => threadsS (T₁ w₀ rc x) (T₂ w₀ rc x) (T₃ w₀ rc x) (S₁ w₀ rc x)
      (S₂ w₀ rc x) (S₃ w₀ rc x) (sits w₀ rc x h) plan (o₁ w₀ rc x h) (o₂ w₀ rc x h) (o₃ w₀ rc x h)
      (n₁ w₀ rc x h) (n₂ w₀ rc x h) (n₃ w₀ rc x h) (a₁ w₀ rc x h k R hR) (a₂ w₀ rc x h k R hR)
      (a₃ w₀ rc x h k R hR) (e₁ w₀ rc x h k R hR) (e₂ w₀ rc x h k R hR) (e₃ w₀ rc x h k R hR))
    hbud
    fun w₀ rc x h k R hR => onDebts_of_onFromS (T₁ w₀ rc x) (T₂ w₀ rc x) (T₃ w₀ rc x)
      (S₁ w₀ rc x) (S₂ w₀ rc x) (S₃ w₀ rc x) (sits w₀ rc x h) plan (o₁ w₀ rc x h) (o₂ w₀ rc x h)
      (o₃ w₀ rc x h) (n₁ w₀ rc x h) (n₂ w₀ rc x h) (n₃ w₀ rc x h) (a₁ w₀ rc x h k R hR)
      (a₂ w₀ rc x h k R hR) (a₃ w₀ rc x h k R hR) (e₁ w₀ rc x h k R hR) (e₂ w₀ rc x h k R hR)
      (e₃ w₀ rc x h k R hR) (htrue w₀ rc x h) (on₁ w₀ rc x h) (on₂ w₀ rc x h) (on₃ w₀ rc x h)

end ProofFile.Honest

#print axioms ProofFile.Honest.insideS_of_insideOf
#print axioms ProofFile.Honest.onDebts_of_onFromS
#print axioms ProofFile.Honest.file_owed
#print axioms ProofFile.Honest.TrueLaid
#print axioms ProofFile.Honest.threadsS
