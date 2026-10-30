-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/DoorWalk.lean: THE DOOR AND `FromThreads` AT THE LETTERS THAT FIX
THE STAND. `door_field` (Honest/Thread/FromThreadsField.lean) asks the plain `DoorBehind` at every
state under `Thr`. Where the last chain's `begun` reads a function of the run, `Thr` alone does not
fix the state, and the plain form can fail. Here each premise is asked wherever the two earlier
invariants hold together with what is said of the run. The first and the shared chain stand at
`SaidWalk` (Honest/Thread/WalkedTo.lean), the last at `SaidField` with `BaseTied`.

  `doorBehindS_cut_field`   `DoorBehindS`, cut into premises on the last chain's `Thread`
  `said₃_tied`   the last chain's letter at its start
  `firstStand`, `sharedStand`   the two first stands
  `fromThreads_walk`   `FromThreads` at the letters

What these are. Conditional lemmas on our own definitions. None is one of the library's goals.
`doorBehindS_cut_field`'s proof is that of a lemma in a file that is not in this library, turned for
the field of the present frame.

Limits.
  * All limits of Honest/Thread/FromThreads.lean and Honest/Thread/WalkedTo.lean stand.
  * `htrees`, `hbeg`, `hForm`, `hItems`, `hr`, `hv` are premises. None is shown here of any thread.
  * `R` is a letter: nothing here says `ready … = .ok R`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.WalkedTo
import Johnson.Desc.ProofFile.Honest.Thread.BaseTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)} {f₃ : List (Fall F.S₃)}
  {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}

/-- **The door, cut into premises on the last chain's `Thread`**, each asked wherever the two earlier
invariants hold with what is said of the run. `e₃`: what is said at the last chain's start. -/
theorem doorBehindS_cut_field (hah₁ : T₁.ahead = []) (hn₁ : T₁.near = 0) (hah₂ : T₂.ahead = [])
    (hah : T₃.ahead =
      declsTo T₁.bs F.first.blocksInOrder.length ++ declsTo T₂.bs F.shared.blocksInOrder.length)
    (hnear : T₃.near = (declsTo T₁.bs F.first.blocksInOrder.length).length)
    (hst : ∀ v, T₁.valid v → ∀ i p, T₁.stored v i p = T₃.stored R.own i p)
    (htrees : ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      T₃.Trees T₃.taken k (R.start₃ H m₁ m₂) (envThird E₁ E₂))
    (hbeg : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.begun k R.own (m₁.st.heard ++ m₂.st.heard) s₃)
    (hForm : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.Form 0 k s₃ (R.start₃ H m₁ m₂))
    (hItems : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.Items (T₃.opened 0) k s₃ (R.start₃ H m₁ m₂) (envThird E₁ E₂))
    (hr : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.rides 0 R.own s₃)
    (hv : T₃.valid R.own)
    (e₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃ 0 k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) }) :
    DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ v₁ v₂ hs g₁ g₂
  have u₁ := v₁.1
  have u₂ := v₂.1
  refine ⟨?_, e₃ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ v₁ v₂ hs g₁ g₂⟩
  show Thr T₃ 0 k s₃ (R.start₃ H m₁ m₂) (envThird E₁ E₂)
  have u₁' := u₁
  have u₂' := u₂
  unfold Thr Thread.Hand Thread.Fit Thread.Made at u₁' u₂'
  obtain ⟨⟨hst₁, -⟩, hF₁, -, -, ⟨hseen₁, hloc₁, -, -, -⟩, -, hv₁⟩ := u₁'
  obtain ⟨-, hF₂, -, -, ⟨hseen₂, -, -, -, -⟩, -, -⟩ := u₂'
  rw [hah₁, List.nil_append] at hF₁
  rw [hah₂, List.nil_append] at hF₂
  have l₁ := drawsFit_length _ _ hF₁
  have l₂ := drawsFit_length _ _ hF₂
  have hloc : T₁.locOf m₁.st.heard = m₁.st.heard := by
    simp [Thread.locOf, Thread.front, hn₁, hah₁]
  have hfr : T₃.front = (m₁.st.heard ++ m₂.st.heard).length := by
    unfold Thread.front
    rw [hah, List.length_append, List.length_append, l₁, l₂]
  have hs12 : (m₁.seen ++ m₂.seen).map (·.drawn) = m₁.st.heard ++ m₂.st.heard := by
    rw [List.map_append, hseen₁, hseen₂]
  have hh : T₃.hand 0 = T₃.taken := List.append_nil _
  unfold Thr
  refine ⟨⟨fun i p => ?_, ?_⟩, ?_, hForm e₁ m₁ E₁ e₂ m₂ E₂ s₃ v₁ v₂ hs,
    hItems e₁ m₁ E₁ e₂ m₂ E₂ s₃ v₁ v₂ hs, ?_, hr e₁ m₁ E₁ e₂ m₂ E₂ s₃ v₁ v₂ hs, hv⟩
  · show E₁.stored i p = T₃.stored R.own i p
    rw [hst₁ i p]
    exact hst _ hv₁ i p
  · rw [hh]
    exact htrees e₁ m₁ E₁ e₂ m₂ E₂ v₁ v₂
  · unfold Thread.Fit
    show drawsFit (T₃.ahead ++ []) (m₁.st.heard ++ m₂.st.heard) = true
    rw [List.append_nil, hah, drawsFit_append, List.take_left' l₁, List.drop_left' l₁, hF₁, hF₂]
    rfl
  · unfold Thread.Made
    refine ⟨hs12, ?_, rfl, fun _ _ => rfl, s₃, [], ?_, rfl, ?_⟩
    · show m₁.loc = T₃.locOf (m₁.st.heard ++ m₂.st.heard)
      unfold Thread.locOf
      rw [hfr, List.drop_length, List.append_nil, hnear, List.take_left' l₁]
      exact hloc₁.trans hloc
    · show T₃.begun k R.own ((m₁.st.heard ++ m₂.st.heard).take T₃.front) s₃
      rw [hfr, List.take_length]
      exact hbeg e₁ m₁ E₁ e₂ m₂ E₂ s₃ v₁ v₂ hs
    · show foldBlocks T₃.ft (T₃.bs.take 0) s₃ ((m₁.seen ++ m₂.seen).drop T₃.front) [] =
        .ok (s₃, [], [])
      have e1 : (m₁.seen ++ m₂.seen).length = T₃.front := by
        rw [hfr, ← hs12, List.length_map]
      rw [← e1, List.drop_length]
      rfl

/-- **The last chain's letter at its start.** -/
theorem said₃_tied (H : Prover W₀ Rc Xi Ky Tr X₀ X) (k : Coins Bk)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) (hS₁ : ∀ k m, S₁ F.first.blocksInOrder.length k m →
      SaidField T₁ BaseNil F.first.blocksInOrder.length k m)
    (hS₂ : ∀ k m, S₂ F.shared.blocksInOrder.length k m → SaidField T₂ BaseNil F.shared.blocksInOrder.length k m)
    {e₁ : F.S₁} {m₁ : Mid (Local W₀ Rc Xi Tr) X} {E₁ : Env} {e₂ : F.S₂}
    {m₂ : Mid (Common W₀ Rc Ky) X₀} {E₂ : Env} {o₁ o₂ : List OpenedColumn}
    (u₁ : ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂)
    (hB : BaseTied F T₃ k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (o₁ ++ o₂)) :
    SaidField T₃ (BaseTied F T₃) 0 k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } :=
  ⟨said₃_ok H k R (o₁ ++ o₂) (hS₁ _ _ u₁.2).1 (hS₂ _ _ u₂.2).1, o₁ ++ o₂, hB,
    fun E _ => T₃.field_start (o₁ ++ o₂) _ E⟩

/-- The first chain's first stand, at every run's coins: the start that `ready` gives, with the field
laid. It reads no coin. -/
def firstStand (H : Prover W₀ Rc Xi Ky Tr X₀ X) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (_ : Coins Bk) :
    Mid (Local W₀ Rc Xi Tr) X :=
  { R.start₁ H with opened := some [] }

/-- The shared chain's first stand, likewise. -/
def sharedStand (H : Prover W₀ Rc Xi Ky Tr X₀ X) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (_ : Coins Bk) :
    Mid (Common W₀ Rc Ky) X₀ :=
  { R.start₂ H with opened := some [] }

/-- **`FromThreads` at the letters.** A conditional lemma on this folder's own definitions. It is none
of the library's goals. The two first stands are the starts that `ready` gives, at every run's
coins, so every stand of the letter has the run's own input. -/
theorem fromThreads_walk (sits : Sits F H T₁ T₂ T₃)
    (o₁ : OwesS T₁ (SaidWalk T₁ BaseNil (firstStand H R)))
    (o₂ : OwesS T₂ (SaidWalk T₂ BaseNil (sharedStand H R)))
    (o₃ : OwesS T₃ (SaidField T₃ (BaseTied F T₃)))
    (n₁ : ∀ b, SaidNext T₁ (SaidWalk T₁ BaseNil (firstStand H R)) b)
    (n₂ : ∀ b, SaidNext T₂ (SaidWalk T₂ BaseNil (sharedStand H R)) b)
    (n₃ : ∀ b, SaidNext T₃ (SaidField T₃ (BaseTied F T₃)) b)
    (y₁ : YesS T₁ (SaidWalk T₁ BaseNil (firstStand H R)) (fallsBy f₁ F.first.blocksInOrder))
    (y₂ : YesS T₂ (SaidWalk T₂ BaseNil (sharedStand H R)) (fallsBy f₂ F.shared.blocksInOrder))
    (y₃ : YesS T₃ (SaidField T₃ (BaseTied F T₃)) (fallsBy f₃ F.second.blocksInOrder))
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (door : DoorBehindS F H T₁ T₂ T₃ (SaidWalk T₁ BaseNil (firstStand H R))
      (SaidWalk T₂ BaseNil (sharedStand H R)) (SaidField T₃ (BaseTied F T₃)) x k R)
    (doorYes : DoorYesS F T₁ T₂ (SaidWalk T₁ BaseNil (firstStand H R))
      (SaidWalk T₂ BaseNil (sharedStand H R)) x k)
    (finYes : FinYesS F T₁ T₂ T₃ (SaidWalk T₁ BaseNil (firstStand H R))
      (SaidWalk T₂ BaseNil (sharedStand H R)) (SaidField T₃ (BaseTied F T₃)) x k) :
    FromThreads F H T₁ T₂ T₃ (SaidWalk T₁ BaseNil (firstStand H R))
      (SaidWalk T₂ BaseNil (sharedStand H R)) (SaidField T₃ (BaseTied F T₃)) f₁ f₂ f₃ w₀ rc x k R
    where
  sits := sits
  owes₁ := o₁
  owes₂ := o₂
  owes₃ := o₃
  next₁ := n₁
  next₂ := n₂
  next₃ := n₃
  yes₁ := y₁
  yes₂ := y₂
  yes₃ := y₃
  enters₁ := a₁
  enters₂ := a₂
  said₁ := saidWalk_start T₁ rfl rfl
  said₂ := saidWalk_start T₂ rfl rfl
  door := door
  doorYes := doorYes
  finYes := finYes

end ProofFile.Honest

#print axioms ProofFile.Honest.doorBehindS_cut_field
#print axioms ProofFile.Honest.said₃_tied
#print axioms ProofFile.Honest.firstStand
#print axioms ProofFile.Honest.sharedStand
#print axioms ProofFile.Honest.fromThreads_walk
