-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttSorts.lean: THE ATTENTION's SORTS OF CELLS GO ALIKE AT TWO RECORDS THAT
MEET SameRead, under RelX (Johnson/AtFull/Shape/Scope/Rel.lean).

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.AttChain
import Johnson.AtFull.Shape.Scope.AttLookLetters
import Johnson.AtFull.Shape.Scope.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape (ChainSh)
open ProofFile.Honest.K5 (k5Q k5GC k5StepC k5Of)

variable {X X₀ : Verify.Public}

theorem k5Of_strip (c : ChainSh) : k5Of (stripC c) = k5Of c := by
  have e1 : (stripC c).marked = c.marked := rfl
  have e2 : (stripC c).rowsOwed = c.rowsOwed := rfl
  have e3 : (stripC c).led = c.led := rfl
  have e4 : (stripC c).att = c.att := rfl
  have e5 : (stripC c).look = c.look.map stripH := rfl
  unfold k5Of
  rw [e1, e2, e3, e4, e5, Option.isSome_map]

theorem lay3_mk (m h tl led tb ro co rp im pl ae ck lk lo lh ow hd at' fi L T) :
    (((ChainSh.mk m h tl led tb ro co rp im pl ae ck lk lo lh ow hd at' fi).setRowsOwed none).layLed L).layAtt T =
      ChainSh.mk m h tl L tb none co rp im pl ae ck lk lo lh ow hd T fi := rfl

theorem k5StepC_strip (x : Params.AttentionRounds) (c : ChainSh) :
    k5StepC x (stripC c) = stripC (k5StepC x c) := by
  unfold k5StepC
  rw [k5Of_strip]
  generalize (H2K5.Honest.k5Step x (k5Of c)).led = L
  generalize (H2K5.Honest.k5Step x (k5Of c)).att = T
  rw [chain_eta c, stripC_mk, lay3_mk, lay3_mk, stripC_mk]

theorem k5Q_blind (x : Params.AttentionRounds) : BlindS (k5Q x) := by
  intro c
  unfold k5Q k5GC
  rw [k5Of_strip]
  split
  · show Except.ok (k5StepC x (stripC c)) = Except.ok (stripC (k5StepC x c))
    rw [k5StepC_strip]
  · rfl

/-- **The attention's own rounds.** -/
theorem k5_rel (S : SameRead X X₀) (g : Nat) {a a' : ShA} (h : RelX X X₀ a a') :
    Alike (RelX X X₀) ((TabL.k5 (LW X) g).1 a) ((TabL.k5 (LW X₀) g).1 a') := by
  unfold TabL.k5
  show Alike _ ((match X.A[g]? with
      | some a => (liftQ (k5Q a.own), ProofFile.Honest.K5.k5V)
      | none => noCell "K5: no plan").1 a) ((match X₀.A[g]? with
      | some a => (liftQ (k5Q a.own), ProofFile.Honest.K5.k5V)
      | none => noCell "K5: no plan").1 a')
  rcases plans_alike S g with ⟨h1, h2⟩ | ⟨p, q, h1, h2, e⟩
  · rw [h1, h2]
    exact Or.inr ⟨rfl, rfl⟩
  · rw [h1, h2]
    have eo : p.own = q.own := by
      have e1 := congrArg Attention.Plan.own e
      exact e1
    show Alike _ (liftQ (k5Q p.own) a) (liftQ (k5Q q.own) a')
    rw [eo]
    exact blind_alike (k5Q_blind q.own) h

theorem relAt_oddE {n : Nat} (h : oddAt n = true) : RelAt X X₀ n = RelX X X₀ := by
  funext a a'
  unfold RelAt
  rw [if_pos h]

/-- **The place of the attention's own rounds, in the joining's form.** -/
theorem k5_cell (S : SameRead X X₀) {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 3 + 1) (TabL.k5 (LW X) (l / 2)) (TabL.k5 (LW X₀) (l / 2)) := by
  have o1 : oddAt (14 * l + 3 + 1) = true := by
    rw [oddAt_place hl (by omega)]
    simp [ho]
  have o2 : oddAt (14 * l + 3 + 1 + 1) = true := by
    rw [oddAt_inside hl (by omega), o1]
  intro a a' h
  rw [relAt_oddE o1] at h
  rw [relAt_oddE o2]
  exact k5_rel S _ h

/-- **The place at the row's own spelling.** -/
theorem own_cell_att (S : SameRead X X₀) {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 3 + 1) ((TabL.linkRow (LW X) l).at 3)
      ((TabL.linkRow (LW X₀) l).at 3) := by
  have hb : ¬ ((l % 2 == 0) = true) := by
    simp [ho]
  have e : ∀ Y : Verify.Public, (TabL.linkRow (LW Y) l).at 3 = TabL.k5 (LW Y) (l / 2) := by
    intro Y
    show (if l % 2 == 0 then TabL.k4 (LW Y) (l / 2) else TabL.k5 (LW Y) (l / 2)) = _
    rw [if_neg hb]
  rw [e X, e X₀]
  exact k5_cell S hl ho

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.k5_rel
#print axioms Johnson.AtFull.Shape.Scope.k5_cell
#print axioms Johnson.AtFull.Shape.Scope.own_cell_att
