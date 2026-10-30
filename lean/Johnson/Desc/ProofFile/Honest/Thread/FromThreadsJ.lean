-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FromThreadsJ.lean: A VALUE OF `ThreadsCJ` FROM THREE THREADS. The
twin of Honest/Thread/FromThreads.lean with the third family: at each member the yes is `AcceptedJ`
and `J` is carried by `NextJ` (Honest/Thread/ShapeJ.lean), each under «no stop, no fall». The debts
that make the run return (`owes`, `next`, `door`) are those of `FromThreads`: they are owed at all
draws.

  `saysYesJ_of_acceptedJ`, `carriesOn_of_nextJ`   a member's two debts in the rule's own forms
  `saysJ₁`, `saysJ₂`, `saysJ₃`, `carriesJ₁`, `carriesJ₂`, `carriesJ₃`   the same at the pairs, in the
    letters of the description and the prover
  `FromThreadsJ`, `FromThreadsJ.threadsCJ`   the structure of hypotheses and the value

What these are. A structure of hypotheses and conditional lemmas on our own definitions. None is one
of the library's goals. `saysYesJ_of_acceptedJ` and `carriesOn_of_nextJ` are taken over from our
trial Thread/FileJ.lean.

Limits.
  * All limits of Honest/Thread/FromThreads.lean and Honest/Thread/ShapeJ.lean stand.
  * The fields are shown here of no thread.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FromThreads
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJ
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratCJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop)

theorem saysYesJ_of_acceptedJ {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (hA : AcceptedJ T Said J fall b) :
    SaysYesJ T.φ Bk T.chain T.ft T.hs blk (fall b) (ThrS T Said b) (J b) := by
  intro k s m E ds l y cols h0 hJ hd hst hf hl hy hc
  have hMv : T.Moved blk k m E ds y cols := by
    unfold Thread.Moved
    exact ⟨⟨l, hl, hy⟩, hc⟩
  obtain ⟨s', hS⟩ := hA blk hblk k s m E ds y cols h0 hJ hd hst hf hMv
  unfold Thread.Stepped at hS
  exact ⟨s', cols.length, hS.2⟩

theorem carriesOn_of_nextJ {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (hN : NextJ T Said J fall b) :
    CarriesOn T.φ Bk T.chain T.ft T.hs blk (fall b) (ThrS T Said b) (J b) (J (b + 1)) := by
  intro k s m E ds l y cols s' n h0 hJ hd hst hf hl hy hc hs
  have hn : n = cols.length :=
    step_takes (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc hs
  subst hn
  have hSt : T.Stepped blk k s m E ds y cols s' := by
    unfold Thread.Stepped Thread.Moved
    exact ⟨⟨⟨l, hl, hy⟩, hc⟩, hs⟩
  exact hN blk hblk k s m E ds y cols s' h0 hJ hd hst hf hSt

end

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)} {f₃ : List (Fall F.S₃)}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {J₁ : Nat → F.S₁ → Prop} {J₂ : Nat → F.S₂ → Prop} {J₃ : Nat → F.S₃ → Prop}

/-! ## 1 The two debts at every sub-protocol, in the letters of description and prover -/

theorem saysJ₁ (hS : Sits F H T₁ T₂ T₃)
    (y : ∀ b, b < T₁.bs.length → AcceptedJ T₁ S₁ J₁ (fallsBy f₁ F.first.blocksInOrder) b) :
    ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYesJ .own Bk 0 0 H.first b (fallOf f₁ b.place) (ThrS T₁ S₁ j) (J₁ j) := by
  obtain ⟨⟨p, c, f, e, h⟩, -, -, -⟩ := hS
  intro j m hm
  have hb : T₁.bs[j]? = some m := by
    rw [e]
    exact hm
  have z := saysYesJ_of_acceptedJ T₁ S₁ J₁ hb (y j (lt_of_member T₁ hb))
  rw [p, c, f, h, fallsBy_at f₁ F.first.blocksInOrder hm] at z
  exact z

theorem saysJ₂ (hS : Sits F H T₁ T₂ T₃)
    (y : ∀ b, b < T₂.bs.length → AcceptedJ T₂ S₂ J₂ (fallsBy f₂ F.shared.blocksInOrder) b) :
    ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYesJ .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (ThrS T₂ S₂ j) (J₂ j) := by
  obtain ⟨-, ⟨p, c, f, e, h⟩, -, -⟩ := hS
  intro j m hm
  have hb : T₂.bs[j]? = some m := by
    rw [e]
    exact hm
  have z := saysYesJ_of_acceptedJ T₂ S₂ J₂ hb (y j (lt_of_member T₂ hb))
  rw [p, c, f, h, fallsBy_at f₂ F.shared.blocksInOrder hm] at z
  exact z

theorem saysJ₃ (hS : Sits F H T₁ T₂ T₃)
    (y : ∀ b, b < T₃.bs.length → AcceptedJ T₃ S₃ J₃ (fallsBy f₃ F.second.blocksInOrder) b) :
    ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYesJ .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (ThrS T₃ S₃ j) (J₃ j) := by
  obtain ⟨-, -, ⟨p, c, f, e, h⟩, -⟩ := hS
  intro j m hm
  have hb : T₃.bs[j]? = some m := by
    rw [e]
    exact hm
  have z := saysYesJ_of_acceptedJ T₃ S₃ J₃ hb (y j (lt_of_member T₃ hb))
  rw [p, c, f, h, fallsBy_at f₃ F.second.blocksInOrder hm] at z
  exact z

theorem carriesJ₁ (hS : Sits F H T₁ T₂ T₃)
    (n : ∀ b, b < T₁.bs.length → NextJ T₁ S₁ J₁ (fallsBy f₁ F.first.blocksInOrder) b) :
    ∀ j b, F.first.blocksInOrder[j]? = some b →
      CarriesOn .own Bk 0 0 H.first b (fallOf f₁ b.place) (ThrS T₁ S₁ j) (J₁ j) (J₁ (j + 1)) := by
  obtain ⟨⟨p, c, f, e, h⟩, -, -, -⟩ := hS
  intro j m hm
  have hb : T₁.bs[j]? = some m := by
    rw [e]
    exact hm
  have z := carriesOn_of_nextJ T₁ S₁ J₁ hb (n j (lt_of_member T₁ hb))
  rw [p, c, f, h, fallsBy_at f₁ F.first.blocksInOrder hm] at z
  exact z

theorem carriesJ₂ (hS : Sits F H T₁ T₂ T₃)
    (n : ∀ b, b < T₂.bs.length → NextJ T₂ S₂ J₂ (fallsBy f₂ F.shared.blocksInOrder) b) :
    ∀ j b, F.shared.blocksInOrder[j]? = some b →
      CarriesOn .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (ThrS T₂ S₂ j) (J₂ j)
        (J₂ (j + 1)) := by
  obtain ⟨-, ⟨p, c, f, e, h⟩, -, -⟩ := hS
  intro j m hm
  have hb : T₂.bs[j]? = some m := by
    rw [e]
    exact hm
  have z := carriesOn_of_nextJ T₂ S₂ J₂ hb (n j (lt_of_member T₂ hb))
  rw [p, c, f, h, fallsBy_at f₂ F.shared.blocksInOrder hm] at z
  exact z

theorem carriesJ₃ (hS : Sits F H T₁ T₂ T₃)
    (n : ∀ b, b < T₃.bs.length → NextJ T₃ S₃ J₃ (fallsBy f₃ F.second.blocksInOrder) b) :
    ∀ j b, F.second.blocksInOrder[j]? = some b →
      CarriesOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (ThrS T₃ S₃ j) (J₃ j)
        (J₃ (j + 1)) := by
  obtain ⟨-, -, ⟨p, c, f, e, h⟩, -⟩ := hS
  intro j m hm
  have hb : T₃.bs[j]? = some m := by
    rw [e]
    exact hm
  have z := carriesOn_of_nextJ T₃ S₃ J₃ hb (n j (lt_of_member T₃ hb))
  rw [p, c, f, h, fallsBy_at f₃ F.second.blocksInOrder hm] at z
  exact z

/-! ## 2 The hypotheses as one structure -/

/-- **What three threads owe for a value of `ThreadsCJ`**, at one input, one run's coins and a letter
`R` for what `ready` returns. It is a structure of hypotheses. Nothing is claimed of it, and it is
none of the library's goals. -/
structure FromThreadsJ (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (J₁ : Nat → F.S₁ → Prop) (J₂ : Nat → F.S₂ → Prop) (J₃ : Nat → F.S₃ → Prop)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (w₀ : W₀) (rc : Rc) (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Prop where
  sits : Sits F H T₁ T₂ T₃
  owes₁ : OwesS T₁ S₁
  owes₂ : OwesS T₂ S₂
  owes₃ : OwesS T₃ S₃
  next₁ : ∀ b, SaidNext T₁ S₁ b
  next₂ : ∀ b, SaidNext T₂ S₂ b
  next₃ : ∀ b, SaidNext T₃ S₃ b
  /-- the yes at every sub-protocol, with the third family in hand, outside the falls -/
  yes₁ : ∀ b, b < T₁.bs.length → AcceptedJ T₁ S₁ J₁ (fallsBy f₁ F.first.blocksInOrder) b
  yes₂ : ∀ b, b < T₂.bs.length → AcceptedJ T₂ S₂ J₂ (fallsBy f₂ F.shared.blocksInOrder) b
  yes₃ : ∀ b, b < T₃.bs.length → AcceptedJ T₃ S₃ J₃ (fallsBy f₃ F.second.blocksInOrder) b
  /-- the third family one member on, outside the stops and the falls -/
  carry₁ : ∀ b, b < T₁.bs.length → NextJ T₁ S₁ J₁ (fallsBy f₁ F.first.blocksInOrder) b
  carry₂ : ∀ b, b < T₂.bs.length → NextJ T₂ S₂ J₂ (fallsBy f₂ F.shared.blocksInOrder) b
  carry₃ : ∀ b, b < T₃.bs.length → NextJ T₃ S₃ J₃ (fallsBy f₃ F.second.blocksInOrder) b
  enters₁ : Enters₁ F H T₁ w₀ rc x k R
  enters₂ : Enters₂ F H T₂ w₀ rc x k R
  said₁ : S₁ 0 k { R.start₁ H with opened := some [] }
  said₂ : S₂ 0 k { R.start₂ H with opened := some [] }
  /-- the third family at the three starts -/
  j₁ : J₁ 0 (F.start₁ (F.pub x))
  j₂ : J₂ 0 (F.start₂ (F.pub x))
  j₃ : ∀ e₁ e₂ s₃, J₁ F.first.blocksInOrder.length e₁ → J₂ F.shared.blocksInOrder.length e₂ →
    F.start₃ (F.pub x) e₁ e₂ = .ok s₃ → J₃ 0 s₃
  /-- from the two ends to the second chain's start, behind its yes: at all draws -/
  door : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R
  /-- the second chain's start says yes, with the third family in hand -/
  doorYes : ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → J₁ F.first.blocksInOrder.length e₁ →
    J₂ F.shared.blocksInOrder.length e₂ → ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃
  /-- the file's last test says yes, with the third family in hand -/
  finYes : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → ThrS T₃ S₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
    J₁ F.first.blocksInOrder.length e₁ → J₂ F.shared.blocksInOrder.length e₂ → J₃ F.second.blocksInOrder.length e₃ →
    F.fin x e₁ e₂ e₃ = true

variable {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **The value, from the structure.** -/
def FromThreadsJ.threadsCJ
    (D : FromThreadsJ F H T₁ T₂ T₃ S₁ S₂ S₃ J₁ J₂ J₃ f₁ f₂ f₃ w₀ rc x k R)
    (hp : F.planOk = true) : ThreadsCJ F Bk H w₀ rc x k R where
  I₁ := ThrS T₁ S₁
  I₂ := ThrS T₂ S₂
  I₃ := ThrS T₃ S₃
  f₁ := f₁
  f₂ := f₂
  f₃ := f₃
  J₁ := J₁
  J₂ := J₂
  J₃ := J₃
  h₁ := playsS₁ D.sits hp D.owes₁ D.next₁
  h₂ := playsS₂ D.sits hp D.owes₂ D.next₂
  h₃ := playsS₃ D.sits hp D.owes₃ D.next₃
  y₁ := saysJ₁ D.sits D.yes₁
  y₂ := saysJ₂ D.sits D.yes₂
  y₃ := saysJ₃ D.sits D.yes₃
  c₁ := carriesJ₁ D.sits D.carry₁
  c₂ := carriesJ₂ D.sits D.carry₂
  c₃ := carriesJ₃ D.sits D.carry₃
  a₁ := ⟨D.enters₁, D.said₁⟩
  a₂ := ⟨D.enters₂, D.said₂⟩
  j₁ := D.j₁
  j₂ := D.j₂
  b₃ := D.door
  d₃ := D.doorYes
  j₃ := D.j₃
  fin := D.finYes

/-- **A value of `ThreadsCJ` with the given lists of falls, from three threads.** A conditional lemma
on this folder's own definitions. It is none of the library's goals. -/
theorem threadsCJ_of_threads (hp : F.planOk = true)
    (D : FromThreadsJ F H T₁ T₂ T₃ S₁ S₂ S₃ J₁ J₂ J₃ f₁ f₂ f₃ w₀ rc x k R) :
    ∃ Thr : ThreadsCJ F Bk H w₀ rc x k R, Thr.f₁ = f₁ ∧ Thr.f₂ = f₂ ∧ Thr.f₃ = f₃ :=
  ⟨D.threadsCJ hp, rfl, rfl, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.saysYesJ_of_acceptedJ
#print axioms ProofFile.Honest.carriesOn_of_nextJ
#print axioms ProofFile.Honest.saysJ₁
#print axioms ProofFile.Honest.saysJ₂
#print axioms ProofFile.Honest.saysJ₃
#print axioms ProofFile.Honest.carriesJ₁
#print axioms ProofFile.Honest.carriesJ₂
#print axioms ProofFile.Honest.carriesJ₃
#print axioms ProofFile.Honest.FromThreadsJ
#print axioms ProofFile.Honest.FromThreadsJ.threadsCJ
#print axioms ProofFile.Honest.threadsCJ_of_threads
