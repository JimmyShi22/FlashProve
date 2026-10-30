-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastLayerS.lean: A LAYER ON THE LAST CHAIN's OWN STATE, BESIDE THE LAST TABLE's
BOOK-KEEPING. The like of `besideL` (Johnson/Desc/Last/BesideL.lean), which lays a
test on the shared chain's last state beside it. THE DEFINITION `besideS` LIES IN
PlmCode.lean (so that a walk can load it
lightly); this file imports it and holds the lemmas.
Why. A fact on the last chain's own state that a sub-protocol's accepting run lays, and that a later
row spends, can be asked of no statement "inside the promise" unless the promise holds it. The
table's letter PL is a test with code on (border, what is handed, the shared end, the state): so
such a fact, where it has code, rides as a conjunct.
  `besideS PL Y`: shape k q e s := PL.shape k q e s && Y k s. `onQ₃_besideS`: the promise at the
    layer is the promise, with Y's yes of the state beside.
  `ownLiftS`: a piece's own law between the promises at two borders lifts to the layer, where its
    accepting run EARNS Y at the border behind (from the promise and Y in front). `framesLiftS`: so
    does "what rides". `rowOne_besideS`, `rowThree_besideS`: the two quiet rows' debts.
Limits. Rules over letters. Nothing on soundness.
-/
import Johnson.LLT25R.PlmCode
import Johnson.Desc.Last.BesideLifts
import Johnson.Desc.Sound.QuietRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last

section
variable {P S₁ S₂ S₃' Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃' (P × S₁)) (Oc : P × S₁ → Strs → Prop) (Y : ℕ → S₃' → Bool)

/-- The promise at the layer is the promise, with the test's yes beside. -/
theorem onQ₃_besideS (k : ℕ) (a : ((P × S₁ × S₂) × S₃') × Fr.E.Str) :
    onQ₃ N Mg Pm (besideS PL Y) Oc k a ↔ onQ₃ N Mg Pm PL Oc k a ∧ Y k a.1.2 = true := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨h4a, h4b⟩ := Bool.and_eq_true_iff.1 h4
    exact ⟨⟨h1, h2, h3, h4a, h5⟩, h4b⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, hx⟩
    exact ⟨h1, h2, h3, Bool.and_eq_true_iff.2 ⟨h4, hx⟩, h5⟩

/-- **A piece's own law lifts to the layer, where its accepting run earns the test behind.** -/
theorem ownLiftS (k : ℕ) (x : Piece C Fr ((P × S₁ × S₂) × S₃') Cl Wt) (In Out : ItemL → Prop)
    (earn : ∀ a τ b, onQ₃ N Mg Pm PL Oc k a → Y k a.1.2 = true → x.ior.red.out a τ = some b →
      Y (k + 1) b.1.2 = true)
    (h : x.Own (onQ₃ N Mg Pm PL Oc k) (onQ₃ N Mg Pm PL Oc (k + 1)) (meansQ₃ N Mg ML) In Out) :
    x.Own (onQ₃ N Mg Pm (besideS PL Y) Oc k) (onQ₃ N Mg Pm (besideS PL Y) Oc (k + 1))
      (meansQ₃ N Mg ML) In Out := by
  intro a ha
  obtain ⟨h1, hY⟩ := (onQ₃_besideS N Mg Pm PL Oc Y k a).1 ha
  refine _root_.Iop.Doomed.mono _ _ ?_ (h a h1)
  intro τ hτ b hb
  obtain ⟨hon, hw⟩ := hτ b hb
  exact ⟨(onQ₃_besideS N Mg Pm PL Oc Y (k + 1) b).2 ⟨hon, earn a τ b h1 hY hb⟩, hw⟩

/-- So does "what rides". -/
theorem framesLiftS (k : ℕ) (x : Piece C Fr ((P × S₁ × S₂) × S₃') Cl Wt) (Open In : ItemL → Prop)
    (h : x.Frames (onQ₃ N Mg Pm PL Oc k) (onQ₃ N Mg Pm PL Oc (k + 1)) (meansQ₃ N Mg ML) Open In) :
    x.Frames (onQ₃ N Mg Pm (besideS PL Y) Oc k) (onQ₃ N Mg Pm (besideS PL Y) Oc (k + 1))
      (meansQ₃ N Mg ML) Open In := by
  intro a τ b w i ha hb hb' hO hI hm
  exact h a τ b w i ((onQ₃_besideS N Mg Pm PL Oc Y k a).1 ha).1 hb
    ((onQ₃_besideS N Mg Pm PL Oc Y (k + 1) b).1 hb').1 hO hI hm

/-- Row 1's debt at the layer: the state goes on as it is, so the test at border 2 is the one at 1.
-/
theorem rowOne_besideS (x : Piece C Fr ((P × S₁ × S₂) × S₃') Cl Wt) (y12 : ∀ s, Y 2 s = Y 1 s)
    (h : RowOneOwed N Mg ML Pm PL Oc x) : RowOneOwed N Mg ML Pm (besideS PL Y) Oc x where
  same := fun a τ b ha hb => h.same a τ b ((onQ₃_besideS N Mg Pm PL Oc Y 1 a).1 ha).1 hb
  idle := h.idle
  prom := fun a τ b ha hb => by
    obtain ⟨h1, hY⟩ := (onQ₃_besideS N Mg Pm PL Oc Y 1 a).1 ha
    refine (onQ₃_besideS N Mg Pm PL Oc Y 2 b).2 ⟨h.prom a τ b h1 hb, ?_⟩
    rw [h.same a τ b h1 hb, y12]
    exact hY
  pins := h.pins

/-- Row 3's debt at the layer, where the test at border 4 says yes of every state. -/
theorem rowThree_besideS (x : Piece C Fr ((P × S₁ × S₂) × S₃') Cl Wt) (y4 : ∀ s, Y 4 s = true)
    (h : RowThreeOwed N Mg Pm PL Oc x) : RowThreeOwed N Mg Pm (besideS PL Y) Oc x :=
  fun a τ b ha hb => (onQ₃_besideS N Mg Pm PL Oc Y 4 b).2
    ⟨h a τ b ((onQ₃_besideS N Mg Pm PL Oc Y 3 a).1 ha).1 hb, y4 _⟩

end

end LLT25

#print axioms LLT25.ownLiftS
#print axioms LLT25.rowOne_besideS
#print axioms LLT25.rowThree_besideS
