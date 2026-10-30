-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachThree.lean: "REACHED" FOR ALL THREE CHAINS of an IOP as written in Lean
(FileDescription): one family a chain. A state of the shared chain is reached from its first state, beside
a reached end of the first chain; a state of the second chain from a first state that start₃ has
accepted, beside two reached ends. Each is handed on by every piece's yes, kind-free, from OfDesc
alone, as at the first chain (ReachAt.lean). ALL FAMILIES STEP BY THE WRAPPED SUB-PROTOCOLS ("below
B": what a piece holds): "reached by steps that a piece can accept"; the fold lemmas speak of the
sub-protocols themselves, by reach_raw.

  ReachR ft bs Start k (z, s)   Reach (Reach.lean) with the first state as a RELATION Start z s (the
                    second chain's first state may be refused); reach_iff: Reach is its instance
  reachR_hand, ReachR.fold   the hand-on; the bridge to the fold, forward
  EndAt₁, EndAt₂    the first | the shared chain's last state is reached, at the flat list's length
  RchAt₂ F k a, RchAt₃ F k a   the two families; rchAt₂_zero, rchAt₃_zero: true at the first states
  rchAt₂_hand, rchAt₃_hand (and _map: with another extractor laid in)   THE HAND-ONS
  rchAt₂_fold, rchAt₃_fold   what a law that spends them gets

Limits. As Reach.lean's. The two earlier chains' ends stand in the statement's public part, which
every piece's yes leaves: so they are carried for nothing; that the ends are the runs' own is what
whoever states the first states owes. No soundness statement.

-/
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.Sound

section
variable {S Cl P : Type}

/-- Reached, with the first state as a relation. -/
inductive ReachR (ft : ℕ) (bs : List (Block S Cl)) (Start : P → S → Prop) : ℕ → P × S → Prop
  | zero {z : P} {s : S} : Start z s → ReachR ft bs Start 0 (z, s)
  | succ {k : ℕ} {z : P} {s s' : S} {b : Block S Cl} : ReachR ft bs Start k (z, s) →
      bs[k]? = some b → StepYes ft b s s' → ReachR ft bs Start (k + 1) (z, s')

/-- Reach is its instance. -/
theorem reach_iff {ft : ℕ} {bs : List (Block S Cl)} {start : P → S} {k : ℕ} {a : P × S} :
    Reach ft bs start k a ↔ ReachR ft bs (fun z s => s = start z) k a := by
  constructor
  · intro h
    induction h with
    | zero z => exact ReachR.zero rfl
    | succ _ hb hy ih => exact ReachR.succ ih hb hy
  · intro h
    induction h with
    | zero e => subst e; exact Reach.zero _
    | succ _ hb hy ih => exact Reach.succ ih hb hy

/-- The bridge to the fold, forward. -/
theorem ReachR.fold {ft : ℕ} {bs : List (Block S Cl)} {Start : P → S → Prop} {k : ℕ} {a : P × S}
    (h : ReachR ft bs Start k a) :
    k ≤ bs.length ∧ ∃ s₀ rs cols, Start a.1 s₀ ∧
      foldBlocks ft (bs.take k) s₀ rs cols = .ok (a.2, [], []) := by
  induction h with
  | @zero z s e =>
    refine ⟨Nat.zero_le _, s, [], [], e, ?_⟩
    rw [List.take_zero]
    unfold foldBlocks
    rfl
  | @succ k z s s' b _ hb hy ih =>
    obtain ⟨_, s₀, rs, cols, e, hf⟩ := ih
    obtain ⟨R, c, hR, hs⟩ := hy
    have hk : k < bs.length := (List.getElem?_eq_some_iff.1 hb).1
    refine ⟨hk, s₀, rs ++ R, cols ++ c, e, ?_⟩
    rw [List.take_add_one, hb]
    have h2 := fold_more ft R c _ _ _ _ _ _ _ hf
    rw [List.nil_append, List.nil_append] at h2
    exact fold_snoc _ _ _ _ _ h2 hR hs

end

/-- The hand-on. -/
theorem reachR_hand {Cl P W S : Type} {C : CK} {Fr : Frame} {bs : List (Block S Cl)}
    {Start : P → S → Prop} {k : ℕ} {q : Piece C Fr (P × S) Cl W} {B : Block S Cl}
    (hB : bs[k]? = some B) (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    {a b : (P × S) × Fr.E.Str} {τ : Iop.Tr (uLT C q.ds)} (h : q.ior.red.out a τ = some b)
    (hr : ReachR Fr.ft bs Start k a.1) : ReachR Fr.ft bs Start (k + 1) b.1 := by
  obtain ⟨e, hy⟩ := piece_step q B hq a b τ h
  have ea : a.1 = (a.1.1, a.1.2) := rfl
  have eb : b.1 = (a.1.1, b.1.2) := Prod.ext e rfl
  rw [eb]
  rw [ea] at hr
  exact ReachR.succ hr hB hy

/-- The hand-on at the wrapped list. -/
theorem reachR_hand_below {Cl P W S : Type} {C : CK} {Fr : Frame} {bs : List (Block S Cl)}
    {Start : P → S → Prop} {k : ℕ} {q : Piece C Fr (P × S) Cl W} {B : Block S Cl}
    (hB : bs[k]? = some B) (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    {a b : (P × S) × Fr.E.Str} {τ : Iop.Tr (uLT C q.ds)} (h : q.ior.red.out a τ = some b)
    (hr : ReachR Fr.ft (bs.map below) Start k a.1) :
    ReachR Fr.ft (bs.map below) Start (k + 1) b.1 := by
  obtain ⟨e, hy⟩ := piece_step_below q B hq a b τ h
  have ea : a.1 = (a.1.1, a.1.2) := rfl
  have eb : b.1 = (a.1.1, b.1.2) := Prod.ext e rfl
  rw [eb]
  rw [ea] at hr
  exact ReachR.succ hr (by rw [List.getElem?_map, hB]; rfl) hy

/-- What is reached by the wrapped sub-protocols' steps is reached by their own. -/
theorem reachR_raw {S Cl P : Type} {ft : ℕ} {bs : List (Block S Cl)} {Start : P → S → Prop} {k : ℕ}
    {a : P × S} (h : ReachR ft (bs.map below) Start k a) : ReachR ft bs Start k a := by
  induction h with
  | zero e => exact ReachR.zero e
  | @succ k z s s' b _ hb hy ih =>
    rw [List.getElem?_map] at hb
    cases hB : bs[k]? with
    | none => rw [hB] at hb; cases hb
    | some B =>
      rw [hB] at hb
      obtain rfl : below B = b := Option.some.inj hb
      exact ReachR.succ ih hB (stepYes_raw hy)

/-- Entry number k of a row of pieces holds entry number k of the flat list, lifted. -/
theorem held_at {Cl P W S : Type} {C : CK} {Fr : Frame} {l : List (Piece C Fr (P × S) Cl W)}
    {bs : List (Block S Cl)}
    (h : l.map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s))) {k : ℕ}
    {q : Piece C Fr (P × S) Cl W} (hq : l[k]? = some q) :
    ∃ B, bs[k]? = some B ∧ q.b = (below B).lift Prod.snd fun t s => (t.1, s) := by
  have hl : l.length = bs.length := by
    have e := congrArg List.length h
    simpa using e
  have hk : k < bs.length := by
    rw [← hl]
    exact (List.getElem?_eq_some_iff.1 hq).1
  refine ⟨bs[k], List.getElem?_eq_getElem hk, ?_⟩
  have e := congrArg (·[k]?) h
  simp only [List.getElem?_map, hq, List.getElem?_eq_getElem hk, Option.map_some] at e
  exact Option.some.inj e

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type} {F : FileDescription Xi}
  {T : ThreeAt C D all F X₁ X₂ W}

/-- The first chain's last state is reached. -/
def EndAt₁ (F : FileDescription Xi) (p : F.XiPub × F.S₁) : Prop :=
  Reach 0 (F.first.blocksInOrder.map below) F.start₁ F.first.blocksInOrder.length p

/-- **Reached, at the shared chain**: beside a reached end of the first chain. -/
def RchAt₂ {Str : Type} (F : FileDescription Xi) (k : ℕ) (a : ((F.XiPub × F.S₁) × F.S₂) × Str) : Prop :=
  Reach 0 (F.shared.blocksInOrder.map below) (fun p : F.XiPub × F.S₁ => F.start₂ p.1) k a.1 ∧
    EndAt₁ F a.1.1

/-- The shared chain's last state is reached, beside a reached end of the first chain. -/
def EndAt₂ (F : FileDescription Xi) (p : F.XiPub × F.S₁ × F.S₂) : Prop :=
  Reach 0 (F.shared.blocksInOrder.map below) (fun p : F.XiPub × F.S₁ => F.start₂ p.1) F.shared.blocksInOrder.length
    ((p.1, p.2.1), p.2.2) ∧ EndAt₁ F (p.1, p.2.1)

/-- **Reached, at the second chain**: from a first state that start₃ has accepted, beside two
reached ends. -/
def RchAt₃ {Str : Type} (F : FileDescription Xi) (k : ℕ)
    (a : ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × Str) : Prop :=
  ReachR F.lastChainFirstTreeNumber (F.second.blocksInOrder.map below)
    (fun (p : F.XiPub × F.S₁ × F.S₂) s => F.start₃ p.1 p.2.1 p.2.2 = .ok s) k a.1 ∧ EndAt₂ F a.1.1

theorem rchAt₂_zero {Str : Type} (p : F.XiPub × F.S₁) (y : Str) (h : EndAt₁ F p) :
    RchAt₂ F 0 ((p, F.start₂ p.1), y) := ⟨Reach.zero p, h⟩

theorem rchAt₃_zero {Str : Type} (p : F.XiPub × F.S₁ × F.S₂) (s : F.S₃) (y : Str)
    (hs : F.start₃ p.1 p.2.1 p.2.2 = .ok s) (h : EndAt₂ F p) : RchAt₃ F 0 ((p, s), y) :=
  ⟨ReachR.zero hs, h⟩

/-- **THE HAND-ON at the shared chain.** -/
theorem rchAt₂_hand (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₂ T.ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl W}
    (hq : (T.p₂ :: T.l₂)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) (hr : RchAt₂ F k a) : RchAt₂ F (k + 1) b := by
  obtain ⟨B, hB, hb⟩ := held_at hT.b₂ hq
  have e : (frameAt D all D.key₂ T.ft₂).ft = 0 := hT.ft₂
  obtain ⟨h1, h2⟩ := hr
  refine ⟨?_, ?_⟩
  · rw [← e] at h1 ⊢
    exact reach_hand_below hB hb h h1
  · rw [(piece_step q B hb a b τ h).1]
    exact h2

/-- **THE HAND-ON at the second chain.** -/
theorem rchAt₃_hand (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₃ T.ft₃) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl W}
    (hq : (T.p₃ :: T.l₃)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) (hr : RchAt₃ F k a) : RchAt₃ F (k + 1) b := by
  obtain ⟨B, hB, hb⟩ := held_at hT.b₃ hq
  have e : (frameAt D all D.key₃ T.ft₃).ft = F.lastChainFirstTreeNumber := hT.ft₃
  obtain ⟨h1, h2⟩ := hr
  refine ⟨?_, ?_⟩
  · rw [← e] at h1 ⊢
    exact reachR_hand_below hB hb h h1
  · rw [(piece_step q B hb a b τ h).1]
    exact h2

theorem rchAt₂_hand_map (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₂ T.ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl W}
    (hq : (T.p₂ :: T.l₂)[k]? = some q) (E) {a b} {τ : Iop.Tr (uLT C (q.withMap E).ds)}
    (h : (q.withMap E).ior.red.out a τ = some b) (hr : RchAt₂ F k a) : RchAt₂ F (k + 1) b :=
  rchAt₂_hand hT hq (τ := τ) h hr

theorem rchAt₃_hand_map (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₃ T.ft₃) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl W}
    (hq : (T.p₃ :: T.l₃)[k]? = some q) (E) {a b} {τ : Iop.Tr (uLT C (q.withMap E).ds)}
    (h : (q.withMap E).ior.red.out a τ = some b) (hr : RchAt₃ F k a) : RchAt₃ F (k + 1) b :=
  rchAt₃_hand hT hq (τ := τ) h hr

/-- What a law that spends it gets, at the shared chain. -/
theorem rchAt₂_fold {Str : Type} {k : ℕ} {a : ((F.XiPub × F.S₁) × F.S₂) × Str}
    (h : RchAt₂ F k a) :
    (k ≤ F.shared.blocksInOrder.length ∧ ∃ rs cols,
      foldBlocks 0 (F.shared.blocksInOrder.take k) (F.start₂ a.1.1.1) rs cols = .ok (a.1.2, [], [])) ∧
    ∃ rs cols, foldBlocks 0 F.first.blocksInOrder (F.start₁ a.1.1.1) rs cols = .ok (a.1.1.2, [], []) := by
  refine ⟨Reach.fold (reach_raw h.1), ?_⟩
  obtain ⟨_, rs, cols, e⟩ := Reach.fold (reach_raw h.2)
  rw [List.take_length] at e
  exact ⟨rs, cols, e⟩

/-- What a law that spends it gets, at the second chain. -/
theorem rchAt₃_fold {Str : Type} {k : ℕ} {a : ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × Str}
    (h : RchAt₃ F k a) :
    (k ≤ F.second.blocksInOrder.length ∧ ∃ s₀ rs cols, F.start₃ a.1.1.1 a.1.1.2.1 a.1.1.2.2 = .ok s₀ ∧
      foldBlocks F.lastChainFirstTreeNumber (F.second.blocksInOrder.take k) s₀ rs cols = .ok (a.1.2, [], [])) ∧
    (∃ rs cols, foldBlocks 0 F.shared.blocksInOrder (F.start₂ a.1.1.1) rs cols =
      .ok (a.1.1.2.2, [], [])) ∧
    ∃ rs cols, foldBlocks 0 F.first.blocksInOrder (F.start₁ a.1.1.1) rs cols =
      .ok (a.1.1.2.1, [], []) := by
  refine ⟨ReachR.fold (reachR_raw h.1), ?_, ?_⟩
  · obtain ⟨_, rs, cols, e⟩ := Reach.fold (reach_raw h.2.1)
    rw [List.take_length] at e
    exact ⟨rs, cols, e⟩
  · obtain ⟨_, rs, cols, e⟩ := Reach.fold (reach_raw h.2.2)
    rw [List.take_length] at e
    exact ⟨rs, cols, e⟩

end

#print axioms reach_iff
#print axioms ReachR.fold
#print axioms rchAt₂_hand
#print axioms rchAt₃_hand
#print axioms rchAt₂_fold
#print axioms rchAt₃_fold

end Johnson.Desc.First.Walk.Tied
