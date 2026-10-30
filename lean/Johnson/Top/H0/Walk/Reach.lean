-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/Reach.lean: "REACHED": the verifier's state at a border is one that the chain's
own blocks hand on from the state at the start of the statement's own public part. One family of
conditions, border by border, true at the start and handed on by every piece's yes, whatever the
kind: so a theorem along the fold can be spent inside any kind's law.

  StepYes ft b s s'   the block's own step says yes from s to s', at as many rounds as it declares
                      and at columns all of which it reads
  Reach ft bs start k (z, s)   inductive: at border 0 the state is start z; one border on by StepYes
                      of block number k. IT STARTS AT z, THE STATEMENT's OWN PUBLIC PART
  piece_step          THE ONE REAL LEMMA: a piece's yes from a to b is StepYes of the block that it
                      holds, from a's state to b's; the public part stays. The rounds: the
                      transcript's, with what the piece puts behind; the columns: what the stage's
                      view opened. By piece_lift_yes (Johnson/Desc/Sound/PieceYes.lean) and
                      step_ok_iff (RunIsDecide.lean)
  piece_step_below, reach_hand_below   THE SAME TWO AT THE WRAPPED SUB-PROTOCOL
                      "below B" (B behind the test that every word shown is below the prime), which
                      is what a piece holds: THE FAMILIES THAT ARE MEANT STEP BY THESE: "reached by
                      steps that a piece can accept"
  stepYes_raw, reach_raw   what is reached by the wrapped steps is reached by the sub-protocols' own
  reach_hand          THE HAND-ON, kind-free
  step_more, fold_more, fold_snoc   a yes of a step, and of the fold, stays a yes with the same
                      state when rounds and columns are laid behind its lists
  step_less, fold_split, reach_of_fold   backward: WHATEVER the fold leaves over
  reach_fold          THE ONE BRIDGE to foldBlocks (Johnson/Desc/Block.lean)

Limits. It says nothing of the tests on the plan, of "before", of the test on the instance or of the
test on the words: it is weaker than "the verifier has come here". The rounds and columns are bound
inside "there are": no law may speak of "the" rounds. It does not ask "no mark".

No soundness statement.

-/
import Johnson.Desc.Sound.PieceYes
import Johnson.Desc.K15.FoldInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_cons)
open VerifiableInference.Desc.Sound

section
variable {S Cl P : Type}

/-- The block's own step says yes from s to s', at as many rounds as it declares and at columns all
of which it reads. -/
def StepYes (ft : ℕ) (b : Block S Cl) (s s' : S) : Prop :=
  ∃ (R : List Fmt.RoundView) (c : List OpenedColumn), R.length = b.rounds.length ∧
    b.step ft s R c = .ok (s', c.length)

/-- **Reached.** -/
inductive Reach (ft : ℕ) (bs : List (Block S Cl)) (start : P → S) : ℕ → P × S → Prop
  | zero (z : P) : Reach ft bs start 0 (z, start z)
  | succ {k : ℕ} {z : P} {s s' : S} {b : Block S Cl} : Reach ft bs start k (z, s) →
      bs[k]? = some b → StepYes ft b s s' → Reach ft bs start (k + 1) (z, s')

/-- An accepting step of "below b" is one of b. -/
theorem stepYes_raw {ft : ℕ} {b : Block S Cl} {s s' : S} (h : StepYes ft (below b) s s') :
    StepYes ft b s s' := by
  obtain ⟨R, c, hR, e⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := (step_ok_iff ft (below b) s s' R c c.length).1 e
  exact ⟨R, c, hR, (step_ok_iff ft b s s' R c c.length).2 ⟨h1, h2, h3, (below_yes b _ _ _ _ h4).2⟩⟩

/-- **What is reached by the wrapped sub-protocols' steps is reached by their own**: so a fact that
is shown of the wider family holds of the narrower. -/
theorem reach_raw {ft : ℕ} {bs : List (Block S Cl)} {start : P → S} {k : ℕ} {a : P × S}
    (h : Reach ft (bs.map below) start k a) : Reach ft bs start k a := by
  induction h with
  | zero z => exact Reach.zero z
  | @succ k z s s' b _ hb hy ih =>
    rw [List.getElem?_map] at hb
    cases hB : bs[k]? with
    | none => rw [hB] at hb; cases hb
    | some B =>
      rw [hB] at hb
      obtain rfl : below B = b := Option.some.inj hb
      exact Reach.succ ih hB (stepYes_raw hy)

/-- A step's yes reads no more columns than it is handed, and stays when more are laid behind. -/
theorem step_more {ft : ℕ} {b : Block S Cl} {s s' : S} {R : List Fmt.RoundView} {c : List OpenedColumn} {k : ℕ}
    (h : b.step ft s R c = .ok (s', k)) (C : List OpenedColumn) :
    k ≤ c.length ∧ b.step ft s R (c ++ C) = .ok (s', k) := by
  obtain ⟨h1, h2, h3, h4⟩ := (step_ok_iff ft b s s' R c k).1 h
  have hk : k ≤ c.length := by
    have e := congrArg List.length h2
    rw [List.length_map, List.length_take, ← h3] at e
    omega
  have et : (c ++ C).take k = c.take k := List.take_append_of_le_length hk
  exact ⟨hk, (step_ok_iff ft b s s' R (c ++ C) k).2 ⟨h1, by rw [et]; exact h2, h3, by
    rw [et]; exact h4⟩⟩

/-- **A fold's yes stays a yes, with the same state, when rounds and columns are laid behind.** -/
theorem fold_more (ft : ℕ) (R : List Fmt.RoundView) (C : List OpenedColumn) : ∀ (l : List (Block S Cl)) (s t : S)
    (rs r : List Fmt.RoundView) (cols c : List OpenedColumn), foldBlocks ft l s rs cols = .ok (t, r, c) →
    foldBlocks ft l s (rs ++ R) (cols ++ C) = .ok (t, r ++ R, c ++ C)
  | [], s, t, rs, r, cols, c, h => by
    unfold foldBlocks at h ⊢
    injection h with h
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    rfl
  | b :: l, s, t, rs, r, cols, c, h => by
    obtain ⟨s', k, hl, hs, h'⟩ := foldBlocks_cons ft b l s rs cols _ h
    obtain ⟨hk, hs'⟩ := step_more hs C
    have hn : b.rounds.length ≤ rs.length := by
      rw [List.length_take] at hl
      omega
    have e1 : (rs ++ R).take b.rounds.length = rs.take b.rounds.length :=
      List.take_append_of_le_length hn
    have e2 : (rs ++ R).drop b.rounds.length = rs.drop b.rounds.length ++ R :=
      List.drop_append_of_le_length hn
    have e3 : (cols ++ C).drop k = cols.drop k ++ C := List.drop_append_of_le_length hk
    unfold foldBlocks
    simp only [List.splitAt_eq, e1, e2, hl, ne_eq, not_true_eq_false, if_false, hs', e3]
    exact fold_more ft R C l s' t _ r _ c h'

/-- The fold over a list and one block more. -/
theorem fold_snoc {ft : ℕ} {b : Block S Cl} {s' : S} {R : List Fmt.RoundView} {C : List OpenedColumn} :
    ∀ (l : List (Block S Cl)) (s t : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    foldBlocks ft l s rs cols = .ok (t, R, C) → R.length = b.rounds.length →
    b.step ft t R C = .ok (s', C.length) → foldBlocks ft (l ++ [b]) s rs cols = .ok (s', [], [])
  | [], s, t, rs, cols, h, hR, hs => by
    unfold foldBlocks at h
    injection h with h
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    show foldBlocks ft [b] s rs cols = _
    unfold foldBlocks
    simp only [List.splitAt_eq, ← hR, List.take_length, List.drop_length, ne_eq,
      not_true_eq_false, if_false, hs]
    unfold foldBlocks
    rfl
  | a :: l, s, t, rs, cols, h, hR, hs => by
    obtain ⟨u, k, hl, hu, h'⟩ := foldBlocks_cons ft a l s rs cols _ h
    show foldBlocks ft (a :: (l ++ [b])) s rs cols = _
    unfold foldBlocks
    simp only [List.splitAt_eq, hl, ne_eq, not_true_eq_false, if_false, hu]
    exact fold_snoc l u t _ _ h' hR hs

/-- **THE ONE BRIDGE**, forward. -/
theorem Reach.fold {ft : ℕ} {bs : List (Block S Cl)} {start : P → S} {k : ℕ} {a : P × S}
    (h : Reach ft bs start k a) :
    k ≤ bs.length ∧
      ∃ rs cols, foldBlocks ft (bs.take k) (start a.1) rs cols = .ok (a.2, [], []) := by
  induction h with
  | zero z =>
    refine ⟨Nat.zero_le _, [], [], ?_⟩
    rw [List.take_zero]
    unfold foldBlocks
    rfl
  | @succ k z s s' b _ hb hy ih =>
    obtain ⟨_, rs, cols, hf⟩ := ih
    obtain ⟨R, c, hR, hs⟩ := hy
    have hk : k < bs.length := (List.getElem?_eq_some_iff.1 hb).1
    refine ⟨hk, rs ++ R, cols ++ c, ?_⟩
    rw [List.take_add_one, hb]
    have h2 := fold_more ft R c _ _ _ _ _ _ _ hf
    rw [List.nil_append, List.nil_append] at h2
    exact fold_snoc _ _ _ _ _ h2 hR hs

/-- A step's yes reads its columns off the front alone. -/
theorem step_less {ft : ℕ} {b : Block S Cl} {s s' : S} {R : List Fmt.RoundView} {c : List OpenedColumn} {k : ℕ}
    (h : b.step ft s R c = .ok (s', k)) :
    b.step ft s R (c.take k) = .ok (s', (c.take k).length) := by
  obtain ⟨hk, _⟩ := step_more h []
  obtain ⟨h1, h2, h3, h4⟩ := (step_ok_iff ft b s s' R c k).1 h
  have el : (c.take k).length = k := by rw [List.length_take]; omega
  rw [el]
  have et : (c.take k).take k = c.take k := by rw [List.take_take, Nat.min_self]
  exact (step_ok_iff ft b s s' R (c.take k) k).2 ⟨h1, by rw [et]; exact h2, h3, by
    rw [et]; exact h4⟩

/-- The fold over two lists in a row, cut. -/
theorem fold_split (ft : ℕ) (l₂ : List (Block S Cl)) : ∀ (l₁ : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    foldBlocks ft (l₁ ++ l₂) s rs cols = .ok out →
    ∃ t r c, foldBlocks ft l₁ s rs cols = .ok (t, r, c) ∧ foldBlocks ft l₂ t r c = .ok out
  | [], s, rs, cols, out, h => ⟨s, rs, cols, by unfold foldBlocks; rfl, h⟩
  | b :: l₁, s, rs, cols, out, h => by
    obtain ⟨s', k, hl, hs, h'⟩ := foldBlocks_cons ft b (l₁ ++ l₂) s rs cols out h
    obtain ⟨t, r, c, h1, h2⟩ := fold_split ft l₂ l₁ _ _ _ _ h'
    refine ⟨t, r, c, ?_, h2⟩
    unfold foldBlocks
    simp only [List.splitAt_eq, hl, ne_eq, not_true_eq_false, if_false, hs]
    exact h1

/-- **THE ONE BRIDGE**, backward: whatever the fold leaves over. -/
theorem reach_of_fold {ft : ℕ} {bs : List (Block S Cl)} {start : P → S} {z : P} :
    ∀ (k : ℕ), k ≤ bs.length → ∀ (s : S) (rs r : List Fmt.RoundView) (cols c : List OpenedColumn),
    foldBlocks ft (bs.take k) (start z) rs cols = .ok (s, r, c) → Reach ft bs start k (z, s)
  | 0, _, s, rs, r, cols, c, h => by
    rw [List.take_zero] at h
    unfold foldBlocks at h
    injection h with h
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact Reach.zero z
  | k + 1, hk, s, rs, r, cols, c, h => by
    have hb : bs[k]? = some bs[k] := List.getElem?_eq_getElem hk
    rw [List.take_add_one, hb] at h
    obtain ⟨t, r₁, c₁, h1, h2⟩ := fold_split ft _ _ _ _ _ _ h
    obtain ⟨s', n, hl, hs, h3⟩ := foldBlocks_cons ft bs[k] [] t r₁ c₁ _ h2
    unfold foldBlocks at h3
    injection h3 with h3
    obtain ⟨rfl, _⟩ := Prod.mk.inj h3
    exact Reach.succ (reach_of_fold k (Nat.le_of_lt hk) t rs r₁ cols c₁ h1) hb
      ⟨_, _, hl, step_less hs⟩

/-- **THE ONE BRIDGE.** -/
theorem reach_fold {ft : ℕ} {bs : List (Block S Cl)} {start : P → S} {k : ℕ} {z : P} {s : S} :
    Reach ft bs start k (z, s) ↔
      k ≤ bs.length ∧ ∃ rs cols, foldBlocks ft (bs.take k) (start z) rs cols = .ok (s, [], []) :=
  ⟨fun h => h.fold, fun ⟨hk, rs, cols, h⟩ => reach_of_fold k hk s rs [] cols [] h⟩

end

section
variable {Cl P W : Type} {C : CK} {Fr : Frame} {S : Type}

/-- **THE ONE REAL LEMMA, AT THE WRAPPED SUB-PROTOCOL**: a piece's yes is an accepting step of
"below B": B behind the test that every word shown is below the prime. -/
theorem piece_step_below (q : Piece C Fr (P × S) Cl W) (B : Block S Cl)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT C q.ds)) (h : q.ior.red.out a τ = some b) :
    b.1.1 = a.1.1 ∧ StepYes Fr.ft (below B) a.1.2 b.1.2 := by
  obtain ⟨_, f1, f3, _⟩ := piece_yes q a b τ h
  rw [hq] at f1 f3
  obtain ⟨s', k1, k2⟩ := lift_yes Prod.snd (fun t s => (t.1, s)) (below B) _ _ _ _ f3
  have f1' : Shown Fr.ft (below B) (q.shownR τ) (sView C q.stage a.2 τ).opened := f1
  obtain ⟨g1, g2, g3⟩ := f1'
  refine ⟨by rw [k2], q.shownR τ, (sView C q.stage a.2 τ).opened, g1, ?_⟩
  rw [k2]
  refine (step_ok_iff Fr.ft (below B) a.1.2 s' _ _ _).2 ⟨g2, ?_, ?_, ?_⟩
  · rw [List.take_length]
    exact g3
  · rw [← g3, List.length_map]
  · rw [List.take_length]
    exact k1

/-- **THE ONE REAL LEMMA**, at the sub-protocol itself: through the wrapped form. -/
theorem piece_step (q : Piece C Fr (P × S) Cl W) (B : Block S Cl)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT C q.ds)) (h : q.ior.red.out a τ = some b) :
    b.1.1 = a.1.1 ∧ StepYes Fr.ft B a.1.2 b.1.2 :=
  ⟨(piece_step_below q B hq a b τ h).1, stepYes_raw (piece_step_below q B hq a b τ h).2⟩

/-- **THE HAND-ON AT THE WRAPPED LIST**, kind-free. -/
theorem reach_hand_below {bs : List (Block S Cl)} {start : P → S} {k : ℕ}
    {q : Piece C Fr (P × S) Cl W} {B : Block S Cl} (hB : bs[k]? = some B)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) {a b : (P × S) × Fr.E.Str}
    {τ : Iop.Tr (uLT C q.ds)} (h : q.ior.red.out a τ = some b)
    (hr : Reach Fr.ft (bs.map below) start k a.1) :
    Reach Fr.ft (bs.map below) start (k + 1) b.1 := by
  obtain ⟨e, hy⟩ := piece_step_below q B hq a b τ h
  have ea : a.1 = (a.1.1, a.1.2) := rfl
  have eb : b.1 = (a.1.1, b.1.2) := Prod.ext e rfl
  rw [eb]
  rw [ea] at hr
  exact Reach.succ hr (by rw [List.getElem?_map, hB]; rfl) hy

/-- **THE HAND-ON**, kind-free. -/
theorem reach_hand {bs : List (Block S Cl)} {start : P → S} {k : ℕ}
    {q : Piece C Fr (P × S) Cl W} {B : Block S Cl} (hB : bs[k]? = some B)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) {a b : (P × S) × Fr.E.Str}
    {τ : Iop.Tr (uLT C q.ds)} (h : q.ior.red.out a τ = some b)
    (hr : Reach Fr.ft bs start k a.1) : Reach Fr.ft bs start (k + 1) b.1 := by
  obtain ⟨e, hy⟩ := piece_step q B hq a b τ h
  have ea : a.1 = (a.1.1, a.1.2) := rfl
  have eb : b.1 = (a.1.1, b.1.2) := Prod.ext e rfl
  rw [eb]
  rw [ea] at hr
  exact Reach.succ hr hB hy

end

#print axioms fold_more
#print axioms Reach.fold
#print axioms reach_of_fold
#print axioms reach_fold
#print axioms reach_raw
#print axioms piece_step_below
#print axioms reach_hand_below
#print axioms piece_step
#print axioms reach_hand

end Johnson.Desc.First.Walk.Tied
