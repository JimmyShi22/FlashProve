-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/StatementGrows.lean: along the three folds of a file's decision the statement only
grows; and, joined with the chains' end's law: whatever stood in the statement at any record that a
fold passes through is covered at the end. Two statements, each a definition of Prop, each proved.

  Passes ft bs s v t    the fold over the blocks bs, from the record s at the view v, passes through
                        the record t: t is what the fold over some front part of bs returns.
  chainAt_passes        NO KIND NAMED: where the chain's decision says yes and every block keeps R,
                        each record passed through is related to the first, and the last to it.
  Spec.statement_grows  at a description whose three chains keep Grows, each at its own reading of
                        the statement: FileDescription.run = true gives the three ends and the second
                        chain's first record, and in each chain: the statement at every record
                        passed through has grown out of the chain's first, and the last out of it.
  Spec.file_covered     where beside that the second chain's start hands the first chain's last
                        statement on (it grows into the second chain's first), and the shared and
                        the second chain end in the end with untestedL's clauses among its own: WHAT
                        STOOD IN THE STATEMENT AT ANY RECORD OF THE FIRST OR THE SECOND CHAIN IS
                        COVERED AT THE SECOND CHAIN's END; of the shared chain at the shared
                        chain's.
THE PREMISES ARE OWED: ChainKeeps (GrowsBy st) c is one step for each kind whose blocks stand in the
chain; the premise on the second chain's start is the start's own.
BOTH A BLOCK THAT SAYS YES TO ALL AND WRITES NOTHING AND ONE THAT SAYS NO TO ALL KEEP Grows, AND
RIGHTLY: "keeps Grows" speaks of what a block writes, not of what it accepts. The members that must
fail it are those that write wrongly (Johnson/Desc/ChainEndCoveredControls.lean); what a last block
must accept and refuse is the end's law.
What is not claimed. NOTHING ON ROWS. "Covered" says that the test has begun, not that it was
carried through. Nothing on soundness as such, on an honest prover or on hiding.

-/
import Johnson.Desc.ChainEndCovered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps
open VerifiableInference.Desc

variable {S Cl : Type}

/-- The fold passes through the record t. -/
def Passes (ft : Nat) (bs : List (Block S Cl)) (s : S) (v : Fmt.View) (t : S) : Prop :=
  ∃ (l₁ l₂ : List (Block S Cl)) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    bs = l₁ ++ l₂ ∧ foldBlocks ft l₁ s v.rounds v.opened = .ok (t, rs, cols)

/-- Each record passed through is related to the first, and the last to it. -/
theorem chainAt_passes (R : S → S → Prop) (hr : ∀ s, R s s)
    (ht : ∀ a b c, R a b → R b c → R a c) (name : String) (ft : Nat) (bs : List (Block S Cl))
    (hb : ∀ b ∈ bs, Decides R b) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft bs s v = .ok s') (t : S) (hp : Passes ft bs s v t) :
    R s t ∧ R t s' := by
  obtain ⟨l₁, l₂, rs, cols, rfl, h1⟩ := hp
  obtain ⟨t', rs', cols', h1', g1, g2⟩ := chainAt_border R hr ht name ft l₁ l₂ hb s s' v h
  rw [h1] at h1'
  cases h1'
  exact ⟨g1, g2⟩

end VerifiableInference.Desc.Keeps

namespace VerifiableInference.Desc.ChainEnd
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.Keeps

/-- Grows, read by st, is reflexive. -/
theorem growsBy_refl {S : Type} (st : S → Statement) (s : S) : GrowsBy st s s := Grows.refl _

/-- Grows, read by st, is transitive. -/
theorem growsBy_trans {S : Type} (st : S → Statement) (a b c : S) (h : GrowsBy st a b)
    (k : GrowsBy st b c) : GrowsBy st a c := Grows.trans h k

/-- **Along the three folds the statement only grows.** -/
def Spec.statement_grows : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (st₁ : F.S₁ → Statement) (st₂ : F.S₂ → Statement)
    (st₃ : F.S₃ → Statement),
    ChainKeeps (GrowsBy st₁) F.first → ChainKeeps (GrowsBy st₂) F.shared →
    ChainKeeps (GrowsBy st₃) F.second →
    ∀ (x : Xi) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
      ∃ e₁ e₂ e₃ s₃, F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃) ∧
        F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
        (∀ t, Passes 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v₁) t →
          Grows (st₁ (F.start₁ (F.pub x))) (st₁ t) ∧ Grows (st₁ t) (st₁ e₁)) ∧
        (∀ t, Passes 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) v₂ t →
          Grows (st₂ (F.start₂ (F.pub x))) (st₂ t) ∧ Grows (st₂ t) (st₂ e₂)) ∧
        ∀ t, Passes F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ v₃ t →
          Grows (st₃ s₃) (st₃ t) ∧ Grows (st₃ t) (st₃ e₃)

/-- The statement holds: along a file's three folds the statement only grows. -/
theorem statement_grows : Spec.statement_grows := by
  intro Xi F st₁ st₂ st₃ k₁ k₂ k₃ x v₁ v₂ v₃ h
  unfold FileDescription.run at h
  cases hq : F.runEnd x v₁ v₂ v₃ with
  | error e => simp [hq, Except.isOk, Except.toBool] at h
  | ok r =>
    obtain ⟨e₁, e₂, e₃⟩ := r
    have hq' := hq
    unfold FileDescription.runEnd at hq'
    obtain ⟨j₁, j₂, ⟨s₃, j₀, j₃⟩, _⟩ := runCore_chains _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq'
    exact ⟨e₁, e₂, e₃, s₃, rfl, j₀,
      fun t => chainAt_passes _ (growsBy_refl st₁) (growsBy_trans st₁) _ _ _
        (chain_flat_keeps _ (growsBy_refl st₁) (growsBy_trans st₁) _ k₁) _ _ _ j₁ t,
      fun t => chainAt_passes _ (growsBy_refl st₂) (growsBy_trans st₂) _ _ _
        (chain_flat_keeps _ (growsBy_refl st₂) (growsBy_trans st₂) _ k₂) _ _ _ j₂ t,
      fun t => chainAt_passes _ (growsBy_refl st₃) (growsBy_trans st₃) _ _ _
        (chain_flat_keeps _ (growsBy_refl st₃) (growsBy_trans st₃) _ k₃) _ _ _ j₃ t⟩

/-- **What stood in the statement anywhere on the way is covered at the end.** -/
def Spec.file_covered : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (st₁ : F.S₁ → Statement) (st₂ : F.S₂ → Statement)
    (st₃ : F.S₃ → Statement) (a₂ : F.S₂ → Clauses) (a₃ : F.S₃ → Clauses),
    ChainKeeps (GrowsBy st₁) F.first → ChainKeeps (GrowsBy st₂) F.shared →
    ChainKeeps (GrowsBy st₃) F.second →
    (∀ p e₁ e₂ s₃, F.start₃ p e₁ e₂ = .ok s₃ → Grows (st₁ e₁) (st₃ s₃)) →
    EndsWith F.shared a₂ → EndsWith F.second a₃ → Asks st₂ a₂ → Asks st₃ a₃ →
    ∀ (x : Xi) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
      ∃ e₁ e₂ e₃ s₃, F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃) ∧
        F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
        (∀ t, Passes 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v₁) t →
          Covered (st₁ t) (st₃ e₃)) ∧
        (∀ t, Passes 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) v₂ t → Covered (st₂ t) (st₂ e₂)) ∧
        ∀ t, Passes F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ v₃ t → Covered (st₃ t) (st₃ e₃)

/-- The statement holds: whatever stood in a statement on the way is covered at the end. -/
theorem file_covered : Spec.file_covered := by
  intro Xi F st₁ st₂ st₃ a₂ a₃ k₁ k₂ k₃ hs h₂ h₃ q₂ q₃ x v₁ v₂ v₃ h
  obtain ⟨e₁, e₂, e₃, s₃, hq, j₀, g₁, g₂, g₃⟩ :=
    statement_grows Xi F st₁ st₂ st₃ k₁ k₂ k₃ x v₁ v₂ v₃ h
  have hq' := hq
  unfold FileDescription.runEnd at hq'
  obtain ⟨_, j₂, ⟨s₃', j₀', j₃⟩, _⟩ := runCore_chains _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq'
  obtain ⟨l₂, _, _, _, _, f₂⟩ := flat_of_endsWith _ _ h₂
  obtain ⟨l₃, _, _, _, _, f₃⟩ := flat_of_endsWith _ _ h₃
  rw [f₂] at j₂
  rw [f₃] at j₃
  have n₂ : NothingLeft (st₂ e₂) := chainAt_nothing_left _ _ _ _ _ _ st₂ a₂ q₂ l₂ _ _ _ j₂
  have n₃ : NothingLeft (st₃ e₃) := chainAt_nothing_left _ _ _ _ _ _ st₃ a₃ q₃ l₃ _ _ _ j₃
  have g₀ : Grows (st₃ s₃) (st₃ e₃) := (g₃ s₃ ⟨[], _, _, _, rfl, rfl⟩).2
  exact ⟨e₁, e₂, e₃, s₃, hq, j₀,
    fun t ht => covered_of _ _ (((g₁ t ht).2.trans (hs _ _ _ _ j₀)).trans g₀) n₃,
    fun t ht => covered_of _ _ (g₂ t ht).2 n₂, fun t ht => covered_of _ _ (g₃ t ht).2 n₃⟩

end VerifiableInference.Desc.ChainEnd
