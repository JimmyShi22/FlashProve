-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/BelowOfPieces.lean: THE PREMISE ON THE ERRORS' SIZE, FROM ONE BOUND FOR EACH
BLOCK.

The setting. `KeySoundOfBlocks` (Johnson/Desc/Sound/KeyRule.lean) and what is made of it
(Johnson/Desc/Sound/KeyPaid.lean, TypedLists.lean) ask, as their last premise, that the three
chains' errors in a row, a shared round's taken once for each leaf of the call's request tree, are
shares of at most εs. These errors are the blocks' own, one list behind the other, behind an error 0
for each silent round.

What is said. `rowErr_below`, `rowErr_below_times`: a row's errors are below a bound (N times: the
like) if each block's are. `BelowOfPieces`, `belowOfPieces`: the premise, from: every block of the
first and of the third chain has its errors below εs; every block of the second chain has its
errors, N times, below εs, N the number of leaves.
`below_trial`: the bound bites: a block with a round in which more values of the challenge
than εs allows are counted does not meet it.

Limits. Nothing bounds any block's errors here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyPaid
import OnBytes.Flat.CarrySFileN
import OnBytes.Maker.WholeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {S Cl W : Type} {C : CK} {F : Frame}

theorem times_app (N : ℕ) : ∀ {s t : Shape} (a : Err s) (b : Err t),
    Err.times N (Err.app a b) = Err.app (Err.times N a) (Err.times N b)
  | [], _, _, _ => rfl
  | _ :: _, _, (e, a), b => congrArg (Prod.mk (N * e)) (times_app N a b)

/-- A row's errors are below c if each block's are. -/
theorem rowErr_below (c : ℝ≥0∞) : ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W),
    (∀ q ∈ p :: l, Err.Below q.err c) → Err.Below (rowErr p l) c
  | [], p, h => h p (List.mem_cons_self)
  | q :: l, p, h =>
    Err.Below.app (h p (List.mem_cons_self))
      (rowErr_below c l q fun r hr => h r (List.mem_cons_of_mem p hr))

/-- The like for the errors N times. -/
theorem rowErr_below_times (N : ℕ) (c : ℝ≥0∞) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W),
    (∀ q ∈ p :: l, Err.Below (Err.times N q.err) c) → Err.Below (Err.times N (rowErr p l)) c
  | [], p, h => h p (List.mem_cons_self)
  | q :: l, p, h => by
    show Err.Below (Err.times N (Err.app p.err (rowErr q l))) c
    rw [times_app]
    exact Err.Below.app (h p (List.mem_cons_self))
      (rowErr_below_times N c l q fun r hr => h r (List.mem_cons_of_mem p hr))

theorem below_cast {s t : Shape} (h : s = t) (ε : Err s) (c : ℝ≥0∞) (hb : Err.Below ε c) :
    Err.Below (cast (congrArg Err h) ε) c := by
  subst h
  exact hb

theorem below_times_cast {s t : Shape} (h : s = t) (N : ℕ) (ε : Err s) (c : ℝ≥0∞)
    (hb : Err.Below (Err.times N ε) c) : Err.Below (Err.times N (cast (congrArg Err h) ε)) c := by
  subst h
  exact hb

/-- **The premise on the errors' size, from one bound for each block.** -/
def BelowOfPieces : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type) (tF : TF)
    (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W)
    (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃) (N : ℕ) (εs : ℝ≥0∞),
    (∀ q ∈ T.p₁ :: T.l₁, Err.Below q.err εs) →
    (∀ q ∈ T.p₂ :: T.l₂, Err.Below (Err.times N q.err) εs) →
    (∀ q ∈ T.p₃ :: T.l₃, Err.Below q.err εs) →
    Err.Below (Err.timesShared N (chainsOf C D tF tJ t3).ann
      ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).err) εs

theorem belowOfPieces : BelowOfPieces := by
  intro C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N εs b₁ b₂ b₃
  exact below_file_shared (chainsOf_laws C D tF tJ t3) N
    (below_cast h₁ _ εs (rowErr_below εs T.l₁ T.p₁ b₁))
    (below_times_cast h₂ N _ εs (rowErr_below_times N εs T.l₂ T.p₂ b₂))
    (below_cast h₃ _ εs (rowErr_below εs T.l₃ T.p₃ b₃))

/-- A CHECK. The bound bites: errors whose first entry, as a share of the round's challenges, is
above c are not below c. -/
theorem below_trial {r : Iop.Round} {s : Shape} (e : ℕ) (ε : Err s) (c : ℝ≥0∞)
    (h : c * (Fintype.card r.Chal : ℝ≥0∞) < (e : ℝ≥0∞)) : ¬ Err.Below (s := r :: s) (e, ε) c :=
  fun hb => absurd hb.1 (not_le.2 h)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.rowErr_below
#print axioms VerifiableInference.Desc.Sound.rowErr_below_times
#print axioms VerifiableInference.Desc.Sound.belowOfPieces
#print axioms VerifiableInference.Desc.Sound.below_trial
