-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachPub.lean: "reached", WITH A CONDITION ON THE PUBLIC PART: the three
families of ReachAt.lean and ReachThree.lean, each beside "Pp holds of the statement's public part".

Why. RchAt F k a says that a's state is reached from F.start₁ of a's OWN public part: that holds at
every public part. Whoever lays the family beside a table's promise wants more: that the public part
of a reached statement is a typed instance's. It is so at the chain's start, and a piece's accepting
step leaves the public part (piece_step_below's first clause, Reach.lean). Pp: a letter. Meant:
fun p => ∃ z, p = (instanceAsPlainRecord z).pub: ONE family for all instances; fun p => p = p₀ is a member too.

  pub_kept, pub_kept₂, pub_kept₃   a piece of each of the three rows leaves the public part
  RchPub, RchPub₂, RchPub₃   RchAt | RchAt₂ | RchAt₃, and Pp of the public part
  rchPub_zero       at the first chain's start
  rchPub_hand, rchPub₂_hand, rchPub₃_hand   THE HAND-ONS
  rchPub₂_start, rchPub₃_start   from a chain's last border to the next chain's first
  handsOn_pub …, eachHandsOn_pub …   in the letters of Johnson/Desc/Sound/ChainOfPromisesR.lean (the
                    first three with an extractor laid in)

Limits. Nothing is said of Pp. No soundness statement.

-/
import Johnson.Top.H0.Walk.ReachHands
import Johnson.Top.H0.Walk.ReachLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type} {F : FileDescription Xi}
  {T : ThreeAt C D all F X₁ X₂ W}

/-- A piece of the first row leaves the public part. -/
theorem pub_kept (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) : b.1.1 = a.1.1 := by
  obtain ⟨B, hB⟩ := block_at hT hq
  exact (piece_step_below q B (OfDesc.pieceAt hT hq hB) a b τ h).1

/-- A piece of the shared chain's row leaves what stands in front of its own state. -/
theorem pub_kept₂ (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₂ T.ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl W}
    (hq : (T.p₂ :: T.l₂)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) : b.1.1 = a.1.1 := by
  obtain ⟨B, _, hb⟩ := held_at hT.b₂ hq
  exact (piece_step_below q B hb a b τ h).1

/-- A piece of the second chain's row leaves what stands in front of its own state. -/
theorem pub_kept₃ (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₃ T.ft₃) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl W}
    (hq : (T.p₃ :: T.l₃)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) : b.1.1 = a.1.1 := by
  obtain ⟨B, _, hb⟩ := held_at hT.b₃ hq
  exact (piece_step_below q B hb a b τ h).1

/-- **Reached at the first chain, and Pp of the public part.** -/
def RchPub {Str : Type} (F : FileDescription Xi) (Pp : F.XiPub → Prop) (k : ℕ)
    (a : (F.XiPub × F.S₁) × Str) : Prop := RchAt F k a ∧ Pp a.1.1

/-- The like at the shared chain. -/
def RchPub₂ {Str : Type} (F : FileDescription Xi) (Pp : F.XiPub → Prop) (k : ℕ)
    (a : ((F.XiPub × F.S₁) × F.S₂) × Str) : Prop := RchAt₂ F k a ∧ Pp a.1.1.1

/-- The like at the second chain. -/
def RchPub₃ {Str : Type} (F : FileDescription Xi) (Pp : F.XiPub → Prop) (k : ℕ)
    (a : ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × Str) : Prop := RchAt₃ F k a ∧ Pp a.1.1.1

theorem rchPub_zero {Str : Type} {Pp : F.XiPub → Prop} (z : F.XiPub) (hz : Pp z) (y : Str) :
    RchPub F Pp 0 ((z, F.start₁ z), y) := ⟨rchAt_zero z y, hz⟩

/-- **THE HAND-ON at the first chain.** -/
theorem rchPub_hand (hT : OfDesc F T) {Pp : F.XiPub → Prop} {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) (hr : RchPub F Pp k a) : RchPub F Pp (k + 1) b :=
  ⟨rchAt_hand hT hq h hr.1, by rw [pub_kept hT hq h]; exact hr.2⟩

/-- **THE HAND-ON at the shared chain.** -/
theorem rchPub₂_hand (hT : OfDesc F T) {Pp : F.XiPub → Prop} {k : ℕ}
    {q : Piece C (frameAt D all D.key₂ T.ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl W}
    (hq : (T.p₂ :: T.l₂)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) (hr : RchPub₂ F Pp k a) : RchPub₂ F Pp (k + 1) b :=
  ⟨rchAt₂_hand hT hq h hr.1, by rw [pub_kept₂ hT hq h]; exact hr.2⟩

/-- **THE HAND-ON at the second chain.** -/
theorem rchPub₃_hand (hT : OfDesc F T) {Pp : F.XiPub → Prop} {k : ℕ}
    {q : Piece C (frameAt D all D.key₃ T.ft₃) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl W}
    (hq : (T.p₃ :: T.l₃)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) (hr : RchPub₃ F Pp k a) : RchPub₃ F Pp (k + 1) b :=
  ⟨rchAt₃_hand hT hq h hr.1, by rw [pub_kept₃ hT hq h]; exact hr.2⟩

/-- From the first chain's last border to the shared chain's first. -/
theorem rchPub₂_start {Str Str' : Type} {Pp : F.XiPub → Prop} {a : (F.XiPub × F.S₁) × Str}
    (h : RchPub F Pp F.first.blocksInOrder.length a) (y : Str') :
    RchPub₂ F Pp 0 ((a.1, F.start₂ a.1.1), y) := ⟨rchAt₂_start h.1 y, h.2⟩

/-- From the shared chain's last border to the second chain's first. -/
theorem rchPub₃_start {Str Str' : Type} {Pp : F.XiPub → Prop} {a : ((F.XiPub × F.S₁) × F.S₂) × Str}
    (h : RchPub₂ F Pp F.shared.blocksInOrder.length a) {s : F.S₃}
    (hs : F.start₃ a.1.1.1 a.1.1.2 a.1.2 = .ok s) (y : Str') :
    RchPub₃ F Pp 0 (((a.1.1.1, a.1.1.2, a.1.2), s), y) := ⟨rchAt₃_start h.1 hs y, h.2⟩

theorem handsOn_pub (hT : OfDesc F T) (Pp : F.XiPub → Prop) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) (E) : HandsOn (RchPub F Pp) k (q.withMap E) :=
  fun _ τ _ hr h => rchPub_hand hT hq (τ := τ) h hr

theorem handsOn_pub₂ (hT : OfDesc F T) (Pp : F.XiPub → Prop) {k : ℕ}
    {q : Piece C (frameAt D all D.key₂ T.ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl W}
    (hq : (T.p₂ :: T.l₂)[k]? = some q) (E) : HandsOn (RchPub₂ F Pp) k (q.withMap E) :=
  fun _ τ _ hr h => rchPub₂_hand hT hq (τ := τ) h hr

theorem handsOn_pub₃ (hT : OfDesc F T) (Pp : F.XiPub → Prop) {k : ℕ}
    {q : Piece C (frameAt D all D.key₃ T.ft₃) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl W}
    (hq : (T.p₃ :: T.l₃)[k]? = some q) (E) : HandsOn (RchPub₃ F Pp) k (q.withMap E) :=
  fun _ τ _ hr h => rchPub₃_hand hT hq (τ := τ) h hr

theorem eachHandsOn_pub (hT : OfDesc F T) (Pp : F.XiPub → Prop) :
    EachHandsOn (RchPub F Pp) 0 (T.p₁ :: T.l₁) :=
  eachHandsOn_of _ _ 0 fun i q hq => by
    rw [Nat.zero_add]
    exact fun _ _ _ hr h => rchPub_hand hT hq h hr

theorem eachHandsOn_pub₂ (hT : OfDesc F T) (Pp : F.XiPub → Prop) :
    EachHandsOn (RchPub₂ F Pp) 0 (T.p₂ :: T.l₂) :=
  eachHandsOn_of _ _ 0 fun i q hq => by
    rw [Nat.zero_add]
    exact fun _ _ _ hr h => rchPub₂_hand hT hq h hr

theorem eachHandsOn_pub₃ (hT : OfDesc F T) (Pp : F.XiPub → Prop) :
    EachHandsOn (RchPub₃ F Pp) 0 (T.p₃ :: T.l₃) :=
  eachHandsOn_of _ _ 0 fun i q hq => by
    rw [Nat.zero_add]
    exact fun _ _ _ hr h => rchPub₃_hand hT hq h hr

end

#print axioms pub_kept
#print axioms rchPub_hand
#print axioms rchPub₂_hand
#print axioms rchPub₃_hand
#print axioms eachHandsOn_pub
#print axioms eachHandsOn_pub₂
#print axioms eachHandsOn_pub₃

end Johnson.Desc.First.Walk.Tied
