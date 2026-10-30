-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/KeepsCore.lean: Johnson/Desc/K13/Keeps.lean once more, for a relation that reads
the statement, the book of trees and the count of roots (Johnson/Desc/CoreKeeps.lean). Kind K13
writes the statement through those of the ground's plain functions that leave the book and the roots
(it receives nothing and takes nothing over): so its blocks keep EVERY relation R on the three that
these eight functions keep (CoreStill R). Theorems.

  batt_keeps, joinAll_keeps, rows_keeps   the kind's plain functions: that file's proofs.
  LensCore X core      what is asked of a lens, at a reading core of the three: enter leaves them;
                       get? hands them over; SET LAYS BACK THE PART's STATEMENT AND LEAVES THE BOOK
                       AND THE ROOTS: so it is at the first chain's record (K13/AtS.lean: atS).
  frontB_keeps · battB_keeps · quietB_keeps · rowsB_keeps · oneRowB_keeps   the kind's blocks. Where
                       a part's book is dropped at the laying back, coreStill_same says that it was
                       the record's own.
  atS_lensCore         the lens at the first chain's record meets it, at coreS.
  atM3_keeps, atM4_keeps   the joined blocks at the first chain's record.
The names stand in the namespace K13.RelCore.
What is not claimed. Which relations are such. A lens that lays the part's book back.

-/
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K1.KeepsAtSCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.RelCore
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K13
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.Ground (Core coreOf CoreStill CoreKeeps ByC coreStill_same core_eq)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1.RelCore (coreS)

variable {R : Core → Core → Prop}

/-- The batching changes the statement by taking mask entries alone. -/
theorem batt_keeps (H : CoreStill R) (owed : Johnson.Desc.First.ForkGround.RowsOwed)
    (kCol n : Nat)
    (pile : List TensorRow) (ledger : Nat) (d : St) (rs : List Fmt.RoundView) (y : TensorRow × St)
    (h : batt owed kCol n pile ledger d rs = .ok y) : R (coreOf d) (coreOf y.2) := by
  unfold batt at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases rs with
  | nil => cases h
  | cons r rs' =>
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    have := pure_ok h
    subst this
    exact H.takeMasks d t.2 ledger _ t.1 (there_ok ht)

/-- Messages join a group, one behind the other. -/
theorem joinAll_keeps (H : CoreStill R) (g : Nat) (l : List Nat) : ∀ (d d' : St),
    joinAll g l d = .ok d' → R (coreOf d) (coreOf d') := by
  induction l with
  | nil =>
    intro d d' h
    have := pure_ok h
    subst this
    exact H.refl _
  | cons o l ih =>
    intro d d' h
    unfold joinAll at h
    obtain ⟨e, he, h⟩ := bind_ok h
    exact H.trans (H.join d e g o false (there_ok he)) (ih e d' h)

/-- Behind W's commitment: a new group, joinings, one row. -/
theorem rows_keeps (H : CoreStill R) (Sh : LinShape) (claim : LinClaim) (ids : Array Nat) (d : St)
    (y : LinFirst × St) (h : rows Sh claim ids d = .ok y) : R (coreOf d) (coreOf y.2) := by
  unfold rows at h
  obtain ⟨w, _, h⟩ := bind_ok h
  obtain ⟨b, hb, h⟩ := bind_ok h
  obtain ⟨d₁, h1, h⟩ := bind_ok h
  obtain ⟨d₂, h2, h⟩ := bind_ok h
  obtain ⟨split, _, h⟩ := bind_ok h
  obtain ⟨d₃, h3, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨row, _, h⟩ := bind_ok h
  obtain ⟨d₄, h4, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  have g3 : R (coreOf d₂) (coreOf d₃) := by
    have h3' := there_ok h3
    split at h3'
    · exact H.join d₂ d₃ b.1 split false h3'
    · cases h3'; exact H.refl _
  exact H.trans (H.trans (H.trans (H.newGroup d b.2 _ _ b.1 (there_ok hb))
    (joinAll_keeps H _ _ _ _ h1)) (H.join d₁ d₂ b.1 w false (there_ok h2)))
    (H.trans g3 (H.addRows d₃ d₄ b.1 [row] (there_ok h4)))

variable {T Cl : Type}

/-- What is asked of a lens, at a reading core of the three. -/
structure LensCore (X : Lens T) (core : T → Core) : Prop where
  enter : ∀ t t', X.enter t = some t' → core t' = core t
  get : ∀ t p, X.get? t = some p → coreOf p.d = core t
  set : ∀ t p q, X.get? t = some p →
    core (X.set t q) = ⟨q.d.st, (core t).book, (core t).roots⟩

/-- The block in front keeps R. -/
theorem frontB_keeps (H : CoreStill R) (X : Lens T) (core : T → Core) (hX : LensCore X core)
    (p : Where) : Decides (ByC R core) (frontB (Cl := Cl) X p) := by
  intro t _ _ t' h
  obtain ⟨t₁, h1, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  show R (core t) (core t₁)
  rw [hX.enter t t₁ (there_ok h1)]
  exact H.refl _

/-- The batching's block keeps R. -/
theorem battB_keeps (H : CoreStill R) (X : Lens T) (core : T → Core) (hX : LensCore X core)
    (p : Where) : Decides (ByC R core) (claimCombinationBlock (Cl := Cl) X p) := by
  intro t rs _ t' h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨o, ho, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  have k := batt_keeps (H.and coreStill_same) _ _ _ _ _ _ _ _ ho
  have g := k.1
  rw [← core_eq s.d o.2 k.2.1 k.2.2] at g
  show R (core t) (core (X.set t _))
  rw [hX.set t s _ (part_ok hs), ← hX.get t s (part_ok hs)]
  exact g

/-- The block without a round keeps R. -/
theorem quietB_keeps (H : CoreStill R) (X : Lens T) (core : T → Core) (hX : LensCore X core)
    (p : Where) : Decides (ByC R core) (quietB (Cl := Cl) X p) := by
  intro t _ _ t' h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  show R (core t) (core (X.set t _))
  rw [hX.set t s _ (part_ok hs), ← hX.get t s (part_ok hs)]
  exact H.refl _

/-- The block that lays the rows keeps R. -/
theorem rowsB_keeps (H : CoreStill R) (X : Lens T) (core : T → Core) (hX : LensCore X core)
    (p : Where) : Decides (ByC R core) (rowsB (Cl := Cl) X p) := by
  intro t _ _ t' h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨o, ho, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  have k := rows_keeps (H.and coreStill_same) _ _ _ _ _ ho
  have g := k.1
  rw [← core_eq s.d o.2 k.2.1 k.2.2] at g
  show R (core t) (core (X.set t _))
  rw [hX.set t s _ (part_ok hs), ← hX.get t s (part_ok hs)]
  exact g

/-- The three in one block keep R. -/
theorem oneRowB_keeps (H : CoreStill R) (X : Lens T) (core : T → Core) (hX : LensCore X core)
    (p : Where) : Decides (ByC R core) (oneRowB (Cl := Cl) X p) := by
  intro t _ _ t' h
  obtain ⟨t₁, h1, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have g1 := frontB_keeps (Cl := Cl) H X core hX p _ _ _ _ h1
  have g2 := quietB_keeps (Cl := Cl) H X core hX p _ _ _ _ h
  refine H.trans g1 (H.trans ?_ g2)
  rw [hX.set t₁ s _ (part_ok hs), ← hX.get t₁ s (part_ok hs)]
  exact H.refl _

/-- The lens at the first chain's record, at the record's own three fields. -/
theorem atS_lensCore : LensCore atS coreS where
  enter := by
    intro t t' h
    simp only [atS] at h
    split at h <;>
      first
        | (cases h; done)
        | (cases h
           simp only [S.enterMem]
           split <;> first | rfl | simp_all)
  get := by
    intro t p h
    simp only [atS] at h
    split at h
    · cases h; rfl
    · cases h
  set := by
    intro t p q h
    simp only [atS] at h ⊢
    split at h
    · rename_i o ho
      rfl
    · cases h

/-- The front, the batching and the quiet part as one block. -/
theorem atM3_keeps (H : CoreStill R) (p : Where) : Decides (ByC R coreS) (atM3 (Cl := Cl) p) :=
  fun s rs gs s' h =>
    Keeps.andThen_decides _ (H.by_trans _) "K13: the members' batching"
      ((frontB atS p).andThen "the front and the batching" (claimCombinationBlock atS p)) (quietB atS p)
      (Keeps.andThen_decides _ (H.by_trans _) "the front and the batching" _ _
        (frontB_keeps H atS _ atS_lensCore p) (battB_keeps H atS _ atS_lensCore p))
      (quietB_keeps H atS _ atS_lensCore p) s rs gs s' h

/-- W's commitment with the own group and (Eval) behind it. -/
theorem atM4_keeps (H : CoreStill R) (p : Where) (commitW : Block S Cl)
    (hW : Decides (ByC R coreS) commitW) : Decides (ByC R coreS) (atM4 p commitW) :=
  Keeps.andThen_decides _ (H.by_trans _) _ _ _ hW (rowsB_keeps H atS _ atS_lensCore p)

end VerifiableInference.Desc.K13.RelCore
