-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/ThreadStratCJ.lean: THE RULES OF Honest/Law/ThreadStratC.lean WITH
A THIRD FAMILY. At a member whose law holds only at a state of the run's shape, the yes is asked with
a sentence `J` on the verifier's state in hand, and `J` is carried one member on under «no stop, no
fall» alone (Honest/Law/AcceptJ.lean). `ThreadsC` has no place for that, since what it asks of its
invariants it asks at all draws. Here are its twin and the twin of `yes_at_stratC`.

  `runC_accepts_viewsJ`   the twin of `runC_accepts_views` (Honest/Law/FallFree.lean)
  `ThreadsCJ`   the twin of `ThreadsC`: `y₁` to `y₃` with `J` in hand; `c₁` to `c₃` carry `J`;
    `j₁`, `j₂`, `j₃` say it at the starts; `b₃` is the second chain's start behind its yes, `d₃` its
    yes; the last test has `J` in hand
  `yes_at_stratCJ`   the twin of `yes_at_stratC`

What these are. A structure of hypotheses and conditional lemmas on this folder's own functions. At
`J₁`, `J₂`, `J₃` that hold of every state these say what `ThreadsC` and `yes_at_stratC`
(Honest/Law/ThreadStratC.lean) say. None is one of the library's goals. The conclusion is that
`FileDescription.run` accepts: not a verifier's acceptance.

Limits.
  * All limits of Honest/Law/ThreadStratC.lean and Honest/Law/AcceptJ.lean stand.
  * A `J` that holds of nothing makes `y` and `c` cost nothing; `j₁` and `j₂` then cannot be met.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC
import Johnson.Desc.ProofFile.Honest.Law.AcceptJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD chainsOf view₁ view₂ view₃)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-- **The rule for a file's acceptance with the third family, where the executable test on the views
meets no fall.** A conditional lemma on this folder's own functions, pointwise. Its conclusion is
that `FileDescription.run` accepts: not a verifier's acceptance. It is none of the library's goals. -/
theorem runC_accepts_viewsJ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hp : F.planOk = true) (hx : F.okStart x = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none)
    (I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (J₁ : Nat → F.S₁ → Prop) (J₂ : Nat → F.S₂ → Prop) (J₃ : Nat → F.S₃ → Prop)
    (h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1)))
    (h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      PlaysOn .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1)))
    (h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1)))
    (y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYesJ .own Bk 0 0 H.first b (fallOf f₁ b.place) (I₁ j) (J₁ j))
    (y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYesJ .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (I₂ j) (J₂ j))
    (y₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYesJ .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (I₃ j) (J₃ j))
    (c₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
      CarriesOn .own Bk 0 0 H.first b (fallOf f₁ b.place) (I₁ j) (J₁ j) (J₁ (j + 1)))
    (c₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      CarriesOn .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (I₂ j) (J₂ j) (J₂ (j + 1)))
    (c₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      CarriesOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (I₃ j) (J₃ j) (J₃ (j + 1)))
    (a₁ : I₁ 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₂ : I₂ 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (j₁ : J₁ 0 (F.start₁ (F.pub x))) (j₂ : J₂ 0 (F.start₂ (F.pub x)))
    (a₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → J₁ F.first.blocksInOrder.length e₁ →
      J₂ F.shared.blocksInOrder.length e₂ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
        I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂) ∧ J₃ 0 s₃)
    (fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
      J₁ F.first.blocksInOrder.length e₁ → J₂ F.shared.blocksInOrder.length e₂ → J₃ F.second.blocksInOrder.length e₃ →
      F.fin x e₁ e₂ e₃ = true)
    (hv : viewsFall F f₁ f₂ f₃ x r.run.views = none) :
    (∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨n₁, n₂, n₃⟩ := fallFree_of_views h f₁ f₂ f₃ hv
  refine runC_acceptsJ h hR hp hx hρ hsil I₁ I₂ I₃ (fallsBy f₁ F.first.blocksInOrder)
    (fallsBy f₂ F.shared.blocksInOrder) (fallsBy f₃ F.second.blocksInOrder) J₁ J₂ J₃ h₁ h₂ h₃ ?_ ?_ ?_ ?_ ?_ ?_ a₁ a₂
    j₁ j₂ a₃ fin n₁ n₂ n₃
  · intro j b hj
    have e : fallsBy f₁ F.first.blocksInOrder j = fallOf f₁ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact y₁ j b hj
  · intro j b hj
    have e : fallsBy f₂ F.shared.blocksInOrder j = fallOf f₂ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact y₂ j b hj
  · intro j b hj
    have e : fallsBy f₃ F.second.blocksInOrder j = fallOf f₃ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact y₃ j b hj
  · intro j b hj
    have e : fallsBy f₁ F.first.blocksInOrder j = fallOf f₁ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact c₁ j b hj
  · intro j b hj
    have e : fallsBy f₂ F.shared.blocksInOrder j = fallOf f₂ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact c₂ j b hj
  · intro j b hj
    have e : fallsBy f₃ F.second.blocksInOrder j = fallOf f₃ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact c₃ j b hj

/-- **What `ThreadsC` asks, with the third family.** It is a structure of hypotheses. Nothing is
claimed of it, and it is none of the library's goals. -/
structure ThreadsCJ (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀)
    (rc : Rc) (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) where
  I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop
  I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop
  I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop
  f₁ : List (Fall F.S₁)
  f₂ : List (Fall F.S₂)
  f₃ : List (Fall F.S₃)
  J₁ : Nat → F.S₁ → Prop
  J₂ : Nat → F.S₂ → Prop
  J₃ : Nat → F.S₃ → Prop
  h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1))
  h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b → PlaysOn .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1))
  h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
    PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1))
  y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
    SaysYesJ .own Bk 0 0 H.first b (fallOf f₁ b.place) (I₁ j) (J₁ j)
  y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
    SaysYesJ .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (I₂ j) (J₂ j)
  y₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
    SaysYesJ .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (I₃ j) (J₃ j)
  c₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
    CarriesOn .own Bk 0 0 H.first b (fallOf f₁ b.place) (I₁ j) (J₁ j) (J₁ (j + 1))
  c₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
    CarriesOn .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (I₂ j) (J₂ j) (J₂ (j + 1))
  c₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
    CarriesOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (I₃ j) (J₃ j) (J₃ (j + 1))
  a₁ : I₁ 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
    (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])
  a₂ : I₂ 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
    (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])
  j₁ : J₁ 0 (F.start₁ (F.pub x))
  j₂ : J₂ 0 (F.start₂ (F.pub x))
  b₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
    m₁.opened = some o₁ → m₂.opened = some o₂ →
    I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂)
  d₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → J₁ F.first.blocksInOrder.length e₁ →
    J₂ F.shared.blocksInOrder.length e₂ → ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃
  j₃ : ∀ e₁ e₂ s₃, J₁ F.first.blocksInOrder.length e₁ → J₂ F.shared.blocksInOrder.length e₂ →
    F.start₃ (F.pub x) e₁ e₂ = .ok s₃ → J₃ 0 s₃
  fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
    J₁ F.first.blocksInOrder.length e₁ → J₂ F.shared.blocksInOrder.length e₂ → J₃ F.second.blocksInOrder.length e₃ →
    F.fin x e₁ e₂ e₃ = true

/-- **At the strategy of `honestBatchProverOfFile`, with the third family.** A conditional lemma on this folder's own functions and
strategies, pointwise. Its conclusion is that `FileDescription.run` accepts, at a parameter F, and three
equations. It says nothing of a verifier's acceptance, and it is none of the library's goals.
`hfall`: no fall fires at the views of the run that `runC` returns at these arguments. -/
theorem yes_at_stratCJ (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
    [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
    (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (w : W₀ × Rc × Sd)
    (x : Xi) (c : (Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3))
    (y : (Iop.oneExternalString (2 ^ D.a) SgX).Str) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R)
    (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
    (h4 : halvedAll F H = true) (h0 : F.okStart x = true) (hP : PlanServes H w.1 w.2.1 R)
    (hk : ∀ r2 r3, (J r2 r3).keyOf w.1 w.2.1 w.2.2 = H.key x)
    (hsh : sh (H.key x) = F.start₂ (F.pub x))
    (hy : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, ∀ (p : Nat) (h : p < 2 ^ D.a),
      H.storedWords w.1 w.2.1 s.item p = some (y ⟨p, h⟩).2)
    (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hw : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.withheld w x)
    (Thr : ThreadsCJ F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (hfall : ∀ r, runC F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) =
      .ok r → viewsFall F Thr.f₁ Thr.f₂ Thr.f₃ x r.run.views = none) :
    F.run x
      (view₁ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1)
      (view₂ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1)
      (view₃ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1) = true ∧
    ((chainsOf C D tF tJ t3).msgF
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 c.2.2).front w.1 w.2.1 w.2.2 x ∧
    ((chainsOf C D tF tJ t3).msgJ
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 default).join w.1 w.2.1 w.2.2 ∧
    ((chainsOf C D tF tJ t3).msg3
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 c.2.2).seam w.1 w.2.1 w.2.2 x := by
  obtain ⟨-, tr, htr, -⟩ := ready_ok hR
  have hsil : silentAt F H w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ) = none := by
    have h1 := (withheldC_iff C D tF tJ t3 F silent Bk H J sh ext w x (by rw [htr]; rfl) ρ).not.1
      hw
    cases hs : silentAt F H w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ) with
    | none => rfl
    | some z =>
      rw [hs] at h1
      exact absurd rfl h1
  obtain ⟨r, hr⟩ := runC_returns hR hq hdue hsil hP Thr.I₁ Thr.I₂ Thr.I₃ Thr.h₁ Thr.h₂ Thr.h₃
    Thr.a₁ Thr.a₂ Thr.b₃
  obtain ⟨-, hyes⟩ := runC_accepts_viewsJ hr hR hp h0 hdue hsil Thr.I₁ Thr.I₂ Thr.I₃ Thr.f₁ Thr.f₂
    Thr.f₃ Thr.J₁ Thr.J₂ Thr.J₃ Thr.h₁ Thr.h₂ Thr.h₃ Thr.y₁ Thr.y₂ Thr.y₃ Thr.c₁ Thr.c₂ Thr.c₃
    Thr.a₁ Thr.a₂ Thr.j₁ Thr.j₂ (fun e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ i1 i2 q1 q2 g1 g2 => by
      obtain ⟨s₃, hs⟩ := Thr.d₃ e₁ m₁ E₁ e₂ m₂ E₂ i1 i2 q1 q2
      exact ⟨s₃, hs, Thr.b₃ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ i1 i2 hs g1 g2, Thr.j₃ e₁ e₂ s₃ q1 q2 hs⟩)
    Thr.fin (hfall r hr)
  obtain ⟨v1, v2, v3, m1, m2, m3⟩ := views_of_stratC C D tF tJ t3 F Bk H (J c.1.2 default)
    (J c.1.2 c.2.2) sh w c.1.1 x c.2.1 y ρ hr hp hD h4 (hk _ _) (hk _ _) hsh hy
  have e : (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1 =
      trAtC C D tF tJ t3 F Bk H (J c.1.2 default) (J c.1.2 c.2.2) sh w c.1.1 x c.2.1 ρ := rfl
  rw [e, v1, v2, v3]
  exact ⟨hyes, m1, m2, m3⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.runC_accepts_viewsJ
#print axioms ProofFile.Honest.ThreadsCJ
#print axioms ProofFile.Honest.yes_at_stratCJ
