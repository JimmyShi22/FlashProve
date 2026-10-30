-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ChainEndFold.lean: the chains' end's law at a chain's fold and at the whole file's
decision. Theorems.

  step_decide           a block's step that says yes rests on a yes of its decide, at the same
                        state.
  foldBlocks_last       what the last block's decide grants of the state that it returns holds of
                        the state that the fold over the whole list returns.
  chainAt_last          the same of chainAt.
  chainAt_nothing_left  **THE CORE**: for every list of blocks in front, every chain, piece, sealed,
                        inFront, every reading st of the statement and every clauses "ask" that hold
                        untestedL's among them: chainAt's yes, with the chain's end as last block,
                        gives NothingLeft at the state that it returns.
  runCore_chains        the file's decision's course, read back: its yes holds a yes of each of the
                        three folds, of the second chain's start and of the last test.
  runEnd_nothing_left   **THE COROLLARY AT THE FILE**: where a description's shared and second chain
                        end so, FileDescription.runEnd's yes gives NothingLeft at both chains' last states.
  run_nothing_left      the same from FileDescription.run = true.
THE FIRST CHAIN's END ASKS NO SUCH CLAUSE: its open groups go on to the second chain: so the
corollary speaks of two chains; that the first chain's groups arrive in the second chain's statement
is the second chain's start's matter.
WHAT OF `verify-on-bytes` IS USED: its plain record Statement. No routine in a
context is reached from a statement or a proof here.
What is not claimed: as in Johnson/Desc/ChainEndLaw.lean. "No round and no column is left" is
chainAt's own and is stated elsewhere; "no count of claims is owed" is not this file's.

-/
import Johnson.Desc.ChainEndLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.ChainEnd
open OnBytes VerifiableInference.Desc

variable {S Cl : Type}

/-- A block's step that says yes rests on a yes of its decide, at the same state. -/
theorem step_decide (ft : Nat) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (k : Nat) (h : b.step ft s rs cols = .ok (s', k)) :
    ∃ rs' gs', b.decide s rs' gs' = .ok s' := by
  unfold Block.step at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i _ _ _ _ t ht
        injection h with h
        injection h with h1 _
        subst h1
        exact ⟨_, _, ht⟩

/-- What the last block's decide grants holds of the state that the whole fold returns. -/
theorem foldBlocks_last (ft : Nat) (e : Block S Cl) (P : S → Prop)
    (he : ∀ s rs gs s', e.decide s rs gs = .ok s' → P s') :
    ∀ (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (r : S × List Fmt.RoundView × List OpenedColumn), foldBlocks ft (bs ++ [e]) s rs cols = .ok r → P r.1 := by
  intro bs
  induction bs with
  | nil =>
    intro s rs cols r h
    simp only [List.nil_append, foldBlocks] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i s' k hs
        injection h with h
        subst h
        obtain ⟨rs', gs', hd⟩ := step_decide ft e s s' _ cols k hs
        exact he _ _ _ _ hd
  | cons b l ih =>
    intro s rs cols r h
    simp only [List.cons_append, foldBlocks] at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih _ _ _ _ h

/-- The same of chainAt. -/
theorem chainAt_last (name : String) (ft : Nat) (e : Block S Cl) (P : S → Prop)
    (he : ∀ s rs gs s', e.decide s rs gs = .ok s' → P s')
    (bs : List (Block S Cl)) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft (bs ++ [e]) s v = .ok s') : P s' := by
  unfold chainAt at h
  split at h
  · cases h
  · split at h
    · rename_i t hf
      injection h with h
      subst h
      exact foldBlocks_last ft e P he bs s v.rounds v.opened _ hf
    · cases h
    · cases h

/-- **Nothing is left untested behind a chain's fold.** -/
theorem chainAt_nothing_left (name : String) (ft chain piece : Nat) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (st : S → Statement) (ask : S → Clauses) (ha : Asks st ask)
    (bs : List (Block S Cl)) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft (bs ++ [chainEnd chain piece sealed inFront ask]) s v = .ok s') :
    NothingLeft (st s') := by
  refine chainAt_last name ft _ (fun t => NothingLeft (st t)) ?_ bs s s' v h
  intro t rs gs t' hd
  obtain ⟨he, hu⟩ := untested_of_chainEnd chain piece sealed inFront st ask ha t t' rs gs hd
  subst he
  exact untested_spec _ hu

/-- A bind of Except that returns: both halves return. -/
theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The file's decision's course, read back: a yes of each fold, of the start, of the last test. -/
theorem runCore_chains {Cl S₁ S₂ S₃ : Type} (planWord : Option String) (okStart : Bool) (s₁ : S₁)
    (s₂ : S₂) (start₃ : S₁ → S₂ → Except String S₃) (ft : Nat) (b₁ : List (Block S₁ Cl))
    (b₂ : List (Block S₂ Cl)) (b₃ : List (Block S₃ Cl)) (fin : S₁ → S₂ → S₃ → Bool)
    (v₁ v₂ v₃ : Fmt.View) (e₁ : S₁) (e₂ : S₂) (e₃ : S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok (e₁, e₂, e₃)) :
    chainAt "the first chain" 0 b₁ s₁ (withEmptySealRound v₁) = .ok e₁ ∧
    chainAt "the shared chain" 0 b₂ s₂ v₂ = .ok e₂ ∧
    (∃ s₃, start₃ e₁ e₂ = .ok s₃ ∧ chainAt "the second chain" ft b₃ s₃ v₃ = .ok e₃) ∧
    fin e₁ e₂ e₃ = true := by
  unfold runCore at h
  dsimp only at h
  split at h
  · obtain ⟨_, hx, _⟩ := bind_ok h
    simp [throw, throwThe, MonadExceptOf.throw] at hx
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨a₁, h1, h⟩ := bind_ok h
    obtain ⟨a₂, h2, h⟩ := bind_ok h
    split at h
    · rename_i s hs
      obtain ⟨y, hy, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hy
      subst hy
      obtain ⟨a₃, h4, h⟩ := bind_ok h
      obtain ⟨_, h5, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨ha, hb, hc⟩ := h
      subst ha hb hc
      refine ⟨h1, h2, ⟨s, hs, h4⟩, ?_⟩
      cases hf : fin a₁ a₂ a₃ with
      | true => rfl
      | false => simp [need, hf] at h5
    · obtain ⟨_, hx, _⟩ := bind_ok h
      simp [throw, throwThe, MonadExceptOf.throw] at hx

/-- **Nothing is left untested behind a file's decision.** -/
theorem runEnd_nothing_left {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (e₁ : F.S₁) (e₂ : F.S₂) (e₃ : F.S₃)
    (st₂ : F.S₂ → Statement) (st₃ : F.S₃ → Statement)
    (l₂ : List (Block F.S₂ F.Cl)) (l₃ : List (Block F.S₃ F.Cl))
    (c₂ p₂ c₃ p₃ : Nat) (z₂ z₃ : Bool) (f₂ f₃ : List Fmt.DeclaredRound)
    (a₂ : F.S₂ → Clauses) (a₃ : F.S₃ → Clauses) (k₂ : Asks st₂ a₂) (k₃ : Asks st₃ a₃)
    (h₂ : F.shared.blocksInOrder = l₂ ++ [chainEnd c₂ p₂ z₂ f₂ a₂])
    (h₃ : F.second.blocksInOrder = l₃ ++ [chainEnd c₃ p₃ z₃ f₃ a₃])
    (h : F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃)) :
    NothingLeft (st₂ e₂) ∧ NothingLeft (st₃ e₃) := by
  unfold FileDescription.runEnd at h
  obtain ⟨_, j₂, ⟨s₃, _, j₃⟩, _⟩ := runCore_chains _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  rw [h₂] at j₂
  rw [h₃] at j₃
  exact ⟨chainAt_nothing_left _ _ _ _ _ _ st₂ a₂ k₂ l₂ _ _ _ j₂,
    chainAt_nothing_left _ _ _ _ _ _ st₃ a₃ k₃ l₃ _ _ _ j₃⟩

/-- The same from the decision's Boolean. -/
theorem run_nothing_left {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (st₂ : F.S₂ → Statement) (st₃ : F.S₃ → Statement)
    (l₂ : List (Block F.S₂ F.Cl)) (l₃ : List (Block F.S₃ F.Cl))
    (c₂ p₂ c₃ p₃ : Nat) (z₂ z₃ : Bool) (f₂ f₃ : List Fmt.DeclaredRound)
    (a₂ : F.S₂ → Clauses) (a₃ : F.S₃ → Clauses) (k₂ : Asks st₂ a₂) (k₃ : Asks st₃ a₃)
    (h₂ : F.shared.blocksInOrder = l₂ ++ [chainEnd c₂ p₂ z₂ f₂ a₂])
    (h₃ : F.second.blocksInOrder = l₃ ++ [chainEnd c₃ p₃ z₃ f₃ a₃])
    (h : F.run x v₁ v₂ v₃ = true) :
    ∃ e₁ e₂ e₃, F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃) ∧
      NothingLeft (st₂ e₂) ∧ NothingLeft (st₃ e₃) := by
  unfold FileDescription.run at h
  cases hr : F.runEnd x v₁ v₂ v₃ with
  | error e => simp [hr, Except.isOk, Except.toBool] at h
  | ok r =>
    obtain ⟨e₁, e₂, e₃⟩ := r
    exact ⟨e₁, e₂, e₃, rfl, runEnd_nothing_left F x v₁ v₂ v₃ e₁ e₂ e₃ st₂ st₃ l₂ l₃ c₂ p₂ c₃ p₃
      z₂ z₃ f₂ f₃ a₂ a₃ k₂ k₃ h₂ h₃ hr⟩

end VerifiableInference.Desc.ChainEnd
