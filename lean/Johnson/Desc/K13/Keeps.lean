-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Keeps.lean: kind K13 writes the statement through the ground's plain functions
alone, never begins a proximity test, admits no sample and copies nothing from another statement:
so its blocks keep EVERY relation R on statements that the eight functions keep which ask nothing
of their caller (Johnson/Desc/GroundQuiet.lean: GroundQuiet R): among them "a statement only grows"
and "no new mark". Theorems.

  batt_keeps, joinAll_keeps, rows_keeps   the kind's plain functions that change the statement.
  LensSt X st          what is asked of a lens, at a reading st of the statement: enter leaves the
                       statement; get? hands it over; set lays back the part's.
  frontB_keeps · battB_keeps · quietB_keeps · rowsB_keeps · oneRowB_keeps   the kind's blocks.
  atS_lensSt           the lens at the first chain's record meets it, at the record's own field.
  atM3_keeps, atM4_keeps   the joined blocks at the first chain's record; the second where the other
                       kind's block keeps it too.
  atM3_grows · atM3_noNew   the two relations at the first of these, said out.
What is not claimed. Which relations are such is Johnson/Desc/GroundKeeps.lean's matter.

-/
import Johnson.Desc.K13.AtS
import Johnson.Desc.GroundQuiet
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open OnBytes OnBytes.Params
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.Ground (GroundQuiet By)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.First (S)

variable {R : Statement → Statement → Prop}

/-- A value that must be there. -/
theorem there_ok {α : Type} {n : String} {o : Option α} {x : α} (h : there n o = .ok x) :
    o = some x := by
  cases o with
  | none => cases h
  | some y => cases h; rfl

/-- What pure returns. -/
theorem pure_ok {α : Type} {a b : α} (h : (pure a : Ans α) = .ok b) : a = b := by
  cases h; rfl

/-- The batching changes the statement by taking mask entries alone. -/
theorem batt_keeps (H : GroundQuiet R) (owed : Johnson.Desc.First.ForkGround.RowsOwed)
    (kCol n : Nat)
    (pile : List TensorRow) (ledger : Nat) (d : St) (rs : List Fmt.RoundView) (y : TensorRow × St)
    (h : batt owed kCol n pile ledger d rs = .ok y) : R d.st y.2.st := by
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
theorem joinAll_keeps (H : GroundQuiet R) (g : Nat) (l : List Nat) : ∀ (d d' : St),
    joinAll g l d = .ok d' → R d.st d'.st := by
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
theorem rows_keeps (H : GroundQuiet R) (Sh : LinShape) (claim : LinClaim) (ids : Array Nat) (d : St)
    (y : LinFirst × St) (h : rows Sh claim ids d = .ok y) : R d.st y.2.st := by
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
  have g3 : R d₂.st d₃.st := by
    have h3' := there_ok h3
    split at h3'
    · exact H.join d₂ d₃ b.1 split false h3'
    · cases h3'; exact H.refl _
  exact H.trans (H.trans (H.trans (H.newGroup d b.2 _ _ b.1 (there_ok hb))
    (joinAll_keeps H _ _ _ _ h1)) (H.join d₁ d₂ b.1 w false (there_ok h2)))
    (H.trans g3 (H.addRows d₃ d₄ b.1 [row] (there_ok h4)))

variable {T Cl : Type}

/-- The relation on records is transitive. -/
theorem by_trans {S : Type} (H : GroundQuiet R) (st : S → Statement) (a b c : S)
    (h : By R st a b) (k : By R st b c) : By R st a c := H.trans h k

/-- What is asked of a lens, at a reading st of the statement. -/
structure LensSt (X : Lens T) (st : T → Statement) : Prop where
  enter : ∀ t t', X.enter t = some t' → st t' = st t
  get : ∀ t p, X.get? t = some p → p.d.st = st t
  set : ∀ t p q, X.get? t = some p → st (X.set t q) = q.d.st

/-- The part of the record that the lens finds. -/
theorem part_ok {X : Lens T} {t : T} {p : Part} (h : X.part t = .ok p) : X.get? t = some p :=
  there_ok h

/-- The block in front keeps R. -/
theorem frontB_keeps (H : GroundQuiet R) (X : Lens T) (st : T → Statement) (hX : LensSt X st)
    (p : Where) :
    Decides (By R st) (frontB (Cl := Cl) X p) := by
  intro t _ _ t' h
  obtain ⟨t₁, h1, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  show R (st t) (st t₁)
  rw [hX.enter t t₁ (there_ok h1)]
  exact H.refl _

/-- The batching's block keeps R. -/
theorem battB_keeps (H : GroundQuiet R) (X : Lens T) (st : T → Statement) (hX : LensSt X st)
    (p : Where) :
    Decides (By R st) (claimCombinationBlock (Cl := Cl) X p) := by
  intro t rs _ t' h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨o, ho, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  show R (st t) (st (X.set t _))
  rw [hX.set t s _ (part_ok hs), ← hX.get t s (part_ok hs)]
  exact batt_keeps H _ _ _ _ _ _ _ _ ho

/-- The block without a round keeps R. -/
theorem quietB_keeps (H : GroundQuiet R) (X : Lens T) (st : T → Statement) (hX : LensSt X st)
    (p : Where) :
    Decides (By R st) (quietB (Cl := Cl) X p) := by
  intro t _ _ t' h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  show R (st t) (st (X.set t _))
  rw [hX.set t s _ (part_ok hs), ← hX.get t s (part_ok hs)]
  exact H.refl _

/-- The block that lays the rows keeps R. -/
theorem rowsB_keeps (H : GroundQuiet R) (X : Lens T) (st : T → Statement) (hX : LensSt X st)
    (p : Where) :
    Decides (By R st) (rowsB (Cl := Cl) X p) := by
  intro t _ _ t' h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨o, ho, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  show R (st t) (st (X.set t _))
  rw [hX.set t s _ (part_ok hs), ← hX.get t s (part_ok hs)]
  exact rows_keeps H _ _ _ _ _ ho

/-- The three in one block keep R. -/
theorem oneRowB_keeps (H : GroundQuiet R) (X : Lens T) (st : T → Statement) (hX : LensSt X st)
    (p : Where) :
    Decides (By R st) (oneRowB (Cl := Cl) X p) := by
  intro t _ _ t' h
  obtain ⟨t₁, h1, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have g1 := frontB_keeps (Cl := Cl) H X st hX p _ _ _ _ h1
  have g2 := quietB_keeps (Cl := Cl) H X st hX p _ _ _ _ h
  refine H.trans g1 (H.trans ?_ g2)
  rw [hX.set t₁ s _ (part_ok hs), ← hX.get t₁ s (part_ok hs)]
  exact H.refl _

/-- The lens at the first chain's record, at the record's own field. -/
theorem atS_lensSt : LensSt atS fun s : S => s.st where
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
theorem atM3_keeps (H : GroundQuiet R) (p : Where) :
    Decides (By R fun s : S => s.st) (atM3 (Cl := Cl) p) :=
  fun s rs gs s' h =>
    Keeps.andThen_decides _ (by_trans H _) "K13: the members' batching"
      ((frontB atS p).andThen "the front and the batching" (claimCombinationBlock atS p)) (quietB atS p)
      (Keeps.andThen_decides _ (by_trans H _) "the front and the batching" _ _
        (frontB_keeps H atS _ atS_lensSt p) (battB_keeps H atS _ atS_lensSt p))
      (quietB_keeps H atS _ atS_lensSt p) s rs gs s' h

/-- W's commitment with the own group and (Eval) behind it. -/
theorem atM4_keeps (H : GroundQuiet R) (p : Where) (commitW : Block S Cl)
    (hW : Decides (By R fun s : S => s.st) commitW) :
    Decides (By R fun s : S => s.st) (atM4 p commitW) :=
  Keeps.andThen_decides _ (by_trans H _) _ _ _ hW (rowsB_keeps H atS _ atS_lensSt p)

/-- Said out: the statement only grows. -/
theorem atM3_grows (p : Where) : Decides (By Grows fun s : S => s.st) (atM3 (Cl := Cl) p) :=
  atM3_keeps Ground.groundKeeps_grows.quiet p

/-- Said out: no new mark. -/
theorem atM3_noNew (p : Where) : Decides (By NoNewMark fun s : S => s.st) (atM3 (Cl := Cl) p) :=
  atM3_keeps Ground.groundKeeps_noNew.quiet p

end VerifiableInference.Desc.K13
