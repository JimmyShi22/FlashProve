-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/KeepsShapes.lean: a commitment of the kind K1 leaves every array's shape in the
sub-proof's ledger: behind a yes each array has the number of rows R and of columns K that it had.
The one thing that a commitment writes into the engine is Fork.rootTaken, which turns an array's
field root alone.

It is Johnson/Desc/K1/KeepsNext.lean, lemma for lemma and proof for proof, with ShapesSame in the
place of "the next free slot is what it was".

Main names: ShapesSame F F' (the list of the arrays' (R, K) is one) · rootTaken_shapes ·
commitOne_shapes, commitAll_shapes, commitBehind_shapes, commitStep_shapes, commitOwn_shapes,
commitAtS_shapes. IS IT EMPTY HERE? Where a block refuses nothing is said. What is not claimed.
Nothing on the arrays' other fields (name, kind, root, owner, virtual rows). Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.K1.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

/-- F' has F's arrays' shapes. -/
def ShapesSame (F F' : Fork) : Prop :=
  (F'.trees.map fun T => (T.R, T.K)) = F.trees.map fun T => (T.R, T.K)

/-- Noting a commitment leaves the shapes. -/
theorem rootTaken_shapes (F : Fork) (t w : Nat) : ShapesSame F (F.rootTaken t w) := by
  unfold ShapesSame Fork.rootTaken
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_modify]
    split <;> rfl

theorem commitOne_shapes {L : LinkCtx} {F F' : Fork} {t : Nat} (h : L3.commitOne L F t = .ok F') :
    ShapesSame F F' := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact rootTaken_shapes _ _ _)
    | cases h

theorem commitAll_shapes {L : LinkCtx} : ∀ (ts : List Nat) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → ShapesSame F F'
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact rfl
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitAll_shapes ts F₁ F' h).trans (commitOne_shapes h1)

theorem commitBehind_shapes {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List Nat}
    (h : L3.commitBehind L check F ts = .ok (L', F')) : ShapesSame F F' := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact commitAll_shapes ts F F₁ h1
    · cases h

theorem commitStep_shapes {W : Type} {send : L3.Send W} {ts : List Nat} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') : ShapesSame s.F s'.F := by
  simp only [L3.commitStep, bind, Except.bind] at h
  cases h0 : L3.commitFront s.L with
  | error e => simp [h0] at h
  | ok u =>
    simp only [h0] at h
    cases h1 : send s.L.check s.w rs with
    | error e => simp [h1] at h
    | ok x =>
      simp only [h1] at h
      cases h2 : L3.commitBehind s.L x.1 s.F ts with
      | error e => simp [h2] at h
      | ok y =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact commitBehind_shapes (L' := y.1) (F' := y.2) h2

/-- **The kind's own block of a segment's later moment leaves the arrays' shapes.** -/
theorem commitOwn_shapes {Cl : Type} {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    {x y : Owing (L3.St (DState Unit))} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    ShapesSame x.held.F y.held.F := by
  simp only [commitOwn] at h
  split at h
  · split at h
    · cases h
    · rename_i ts
      cases h1 : L3.commitStep (laterOwn P x.owed) ts x.held rs with
      | error e => simp [h1, Except.map] at h
      | ok z =>
        simp only [h1, Except.map, Except.ok.injEq] at h
        subst h
        exact commitStep_shapes h1
  · cases h

/-- **The same at the carried record.** -/
theorem commitAtS_shapes {Cl : Type} {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') :
    ∃ L F tl y, s.link? = some L ∧ s.fork? = some F ∧ s.tl? = some tl ∧
      s' = ((laid s (y : L3.St (DState Unit)).w).putLink y.L).putFork y.F ∧ ShapesSame F y.F := by
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := owedOf s, held := { L := L, F := F, tl := tl, w := stateOf s () } } rs gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      exact ⟨L, F, tl, y.held, hL, hF, ht, h.symm, commitOwn_shapes h1⟩
  · cases h

end VerifiableInference.Desc.K1
