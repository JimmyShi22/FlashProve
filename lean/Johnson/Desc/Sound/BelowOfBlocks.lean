-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/BelowOfBlocks.lean: THE THREE BOUNDS ON A FILE's CHAINS' ERRORS, FROM ONE BOUND A
BLOCK. At the rule of composition's value (`Three.snd`, Johnson/Desc/Sound/FileRule.lean) a chain's
list of errors is 0 for the silent round and then the blocks' own errors appended. So "every error
of the chain, as a share of the round's challenges, is at most c" (`Err.Below`, Iop/InteractiveOracleProof.lean) is
just: every block's own errors are. Statements, written as `def … : Prop`, with their proofs.

Why. The named hypotheses on soundness ask the three bounds of the chains' lists
(Johnson/Flat/ProofOfLaws.lean: 18, 19, 20). A kind's files state its rounds' errors block by
block. For a block of the shared chain with its law in two parts (`Piece.LostBothAt`,
Johnson/Desc/Sound/FoldSlots.lean) whose own errors ARE εK + N · εO the bound is had from a bound on
each part: cK + N · cO ≤ c.

Main names.
  `EachBelow c l`: every block of l has its own errors at most c, as shares.
  `RowBelow`, `rowBelow`: then so have the blocks' errors appended (`rowErr`).
  `OwnBelow`, `ownBelow`: and carried to the chain's own list of rounds (`errOwn`).
  `SndBelow`, `sndBelow`: the three bounds at `Three.snd`.
  `BelowTimes`, `belowTimes`: N times a list that is at most c is at most N · c.
  `BelowBoth`, `belowBoth`: εK at most cK, εO at most cO, cK + N · cO ≤ c: εK + N · εO is at most c.

Every "there is", walked. None of the statements has one.

Limits. Arithmetic on lists of numbers: no round is evaluated, and no block of the protocol is
named. Nothing says that c is small. `Err.Below` counts a round's bad challenges against ALL its
challenges. A ROUND's PROOF OF WORK CAN BE COUNTED IN THAT SHARE, BY WHOEVER STATES THE BLOCK's
ERRORS: a round's challenge holds the work's test bits (OnBytes/TypedOracleCompiler/Run/PlanQS.lean), and a piece's
own reduction refuses where they fail (`stageIOR`'s tests, OnBytes/Maker/Stage.lean): so only
challenges that pass the work's test can be bad, and a kind's files may state its bare count divided
by 2 ^ work.
Nothing of that is shown in this file.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileRule
import Ior.BatchSeq

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- Every block of the list has its own errors at most c, as shares of its rounds' challenges. -/
def EachBelow {S Cl W : Type} {C : CK} {F : Frame} (c : ℝ≥0∞) (l : List (Piece C F S Cl W)) :
    Prop :=
  ∀ q ∈ l, Err.Below q.err c

def RowBelow : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (c : ℝ≥0∞) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)), EachBelow c (p :: l) → Err.Below (rowErr p l) c

theorem rowBelow : RowBelow := by
  intro S Cl W C F c p l
  induction l generalizing p with
  | nil => exact fun h => h p List.mem_cons_self
  | cons q l ih =>
    intro h
    exact Err.Below.app (h p List.mem_cons_self) (ih q fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- A list of errors carried along an equation of lists of rounds keeps its bound. -/
theorem belowAlongCast {s t : Shape} (h : s = t) (ε : Err s) (c : ℝ≥0∞) (hb : Err.Below ε c) :
    Err.Below (cast (congrArg Err h) ε) c := by
  subst h
  exact hb

def OwnBelow : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (c : ℝ≥0∞) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (ds : List RDT) (h : (rowIOR p l).shape = uLT C ds),
    EachBelow c (p :: l) → Err.Below (errOwn p l ds h) c

theorem ownBelow : OwnBelow := fun S Cl W C F c p l _ h hb =>
  belowAlongCast h _ c (rowBelow S Cl W C F c p l hb)

/-- **The three bounds at the rule of composition's value, from one bound a block.** -/
def SndBelow : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type) (tF : TF)
    (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W)
    (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃) (c : ℝ≥0∞),
    EachBelow c (T.p₁ :: T.l₁) → EachBelow c (T.p₂ :: T.l₂) → EachBelow c (T.p₃ :: T.l₃) →
    Err.Below (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).ε₁ c ∧
      Err.Below (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).ε₂ c ∧
      Err.Below (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).ε₃ c

theorem sndBelow : SndBelow := by
  intro C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ c b₁ b₂ b₃
  exact ⟨⟨by simp, ownBelow _ _ _ _ _ c T.p₁ T.l₁ D.ds₁ h₁ b₁⟩,
    ⟨by simp, ownBelow _ _ _ _ _ c T.p₂ T.l₂ D.ds₂ h₂ b₂⟩,
    ⟨by simp, ownBelow _ _ _ _ _ c T.p₃ T.l₃ D.ds₃ h₃ b₃⟩⟩

def BelowTimes : Prop :=
  ∀ (s : Shape) (ε : Err s) (N : ℕ) (c : ℝ≥0∞), Err.Below ε c →
    Err.Below (Err.times N ε) ((N : ℝ≥0∞) * c)

theorem belowTimes : BelowTimes := by
  intro s
  induction s with
  | nil => exact fun _ _ _ _ => trivial
  | cons r s ih =>
    rintro ⟨e, ε⟩ N c ⟨h, h'⟩
    refine ⟨?_, ih ε N c h'⟩
    show ((N * e : ℕ) : ℝ≥0∞) ≤ (N : ℝ≥0∞) * c * (Fintype.card r.Chal : ℝ≥0∞)
    rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul_right h _

/-- **A shared block's errors in two parts**: what is paid once at most cK, what is paid once for
each slot at most cO, and cK + N · cO ≤ c. -/
def BelowBoth : Prop :=
  ∀ (s : Shape) (εK εO : Err s) (N : ℕ) (cK cO c : ℝ≥0∞), Err.Below εK cK → Err.Below εO cO →
    cK + (N : ℝ≥0∞) * cO ≤ c → Err.Below (Err.add εK (Err.times N εO)) c

theorem belowBoth : BelowBoth := fun s _ εO N _ cO _ hK hO hc =>
  Err.Below.mono_bound hc (Err.Below.add hK (belowTimes s εO N cO hO))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.rowBelow
#print axioms VerifiableInference.Desc.Sound.sndBelow
#print axioms VerifiableInference.Desc.Sound.belowTimes
#print axioms VerifiableInference.Desc.Sound.belowBoth
