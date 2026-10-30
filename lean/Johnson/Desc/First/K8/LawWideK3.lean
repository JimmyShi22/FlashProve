-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawWideK3.lean: THE SMALLNESS TEST: THE LOOKUP'S BLOCK, ON THE CALLS AND ON
THE DIGITS, LEAVES ALL THAT THE SMALLNESS TEST'S LETTERS READ OFF ITS RECORD.

Between the draw of the matrix and the link's batching stands the lookup on the digits. Its block
writes the smallness test's record. Here: it writes none of the fields of `wide`
(Johnson/Desc/First/K8/LawWide.lean).
  `wide_putFork`, `wide_mark`, `wide_hearLook`: laying the ledger, a mark, or what the lookup on the
    calls returned leaves `wide`.
  `putDigits_wide`, `putCalls_wide`: so do the two seats' layings
    (Johnson/Desc/First/Look/K3Seat.lean): at the digits the record gets a count, two slots and what
    was heard: no field of `wide`.
  `decideVia_wide`: so does a yes of the kind's decision at either seat.
  `quietAt_wide`: so do the steps without a round that the kind joins behind
    (Johnson/Desc/First/Look/K3Whole.lean).
  `theOwn_leaves_wide`, `theWhole_leaves_wide`, `theStated_leaves_wide`: **every block that the kind
    makes at an address leaves `wide`.**
  `readTl g`, `Keeps4 g`, `theStated_leaves_tl`: ALL OF IT AT ANY READING g OF THE RECORD that reads
    none of the four fields that the lookup on the digits lays (a count, two slots, what was heard):
    so also at the drawn matrix.
Statements and proofs. The texts (Johnson/Desc/First/Look/) are read, called by name, not turned.
Limits. The block's DECISION alone: its runs of claims ("objects", "guests", "planes") are not
spoken of. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawWide
import Johnson.Desc.First.Look.K3Stated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model

theorem tl_putFork (s : S) (F : Fork) : (s.putFork F).tl? = s.tl? := by
  unfold S.putFork S.tl?
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho]
  | _ => simp [h]

theorem tl_mark (s : S) (m : String) : (s.mark m).tl? = s.tl? := by
  unfold S.mark
  cases s.failed <;> rfl

theorem tl_hearLook (s : S) (g : Forest.Heard) : (s.hearLook g).tl? = s.tl? := by
  unfold S.hearLook
  cases h : s.here with
  | lay a =>
    by_cases hl : a.lookHeard.isSome
    · simp only [hl, if_true]
      exact tl_mark s _
    · simp [hl, S.tl?, h]
  | att a =>
    by_cases hl : a.lookHeard.isSome
    · simp only [hl, if_true]
      exact tl_mark s _
    · simp [hl, S.tl?, h]
  | head a =>
    by_cases ho : a.opened
    · by_cases hl : a.lookHeard.isSome
      · simp only [ho, hl, Bool.not_true, Bool.false_eq_true, if_false, if_true]
        exact tl_mark s _
      · simp [ho, hl, S.tl?, h]
    · simp only [ho, Bool.not_false, if_true]
      exact tl_mark s _
  | _ => exact tl_mark s _

/-- A reading of the smallness test's record in the carried record. -/
def readTl {α : Type} (g : HTailF2 → α) (s : S) : Option α := s.tl?.map g

/-- A reading that the laying at the lookup on the digits does not turn: it reads none of the four
fields that are laid there. -/
def Keeps4 {α : Type} (g : HTailF2 → α) : Prop :=
  ∀ (tl : HTailF2) (fd a b : Nat) (h : Option Forest.Heard),
    g { tl with foldDrawn := fd, slotA := a, slotB := b, heard := h } = g tl

theorem wide_is : wide = readTl wideOf := rfl

theorem keeps4_wideOf : Keeps4 wideOf := fun _ _ _ _ _ => rfl

variable {α : Type} {g : HTailF2 → α}

theorem wide_of_tl {s s' : S} (h : s'.tl? = s.tl?) : readTl g s' = readTl g s := by
  unfold readTl
  rw [h]

theorem wide_putFork (s : S) (F : Fork) : readTl g (s.putFork F) = readTl g s :=
  wide_of_tl (tl_putFork s F)

theorem wide_mark (s : S) (m : String) : readTl g (s.mark m) = readTl g s :=
  wide_of_tl (tl_mark s m)

theorem wide_hearLook (s : S) (h : Forest.Heard) : readTl g (s.hearLook h) = readTl g s :=
  wide_of_tl (tl_hearLook s h)

/-- The laying at the lookup on the digits. -/
theorem putDigits_wide {Cl : Type} (hg : Keeps4 g) (claim : Aff → Cl) (s : S) (h : Forest.Heard)
    (G : Fork) : readTl g ((K3.seatDigits claim).put s h G) = readTl g s := by
  show readTl g (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some h }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test") = readTl g s
  cases ht : s.tl? with
  | none => exact wide_mark s _
  | some tl =>
    cases hf : s.fork? with
    | none => exact wide_mark s _
    | some F =>
      show readTl g ((s.putTl _).putFork G) = readTl g s
      rw [wide_putFork]
      unfold readTl
      rw [putTl_tl s tl _ ht, ht, Option.map_some, Option.map_some, hg]

/-- The laying at the lookup on the calls. -/
theorem putCalls_wide {Cl : Type} (claim : Aff → Cl) (s : S) (h : Forest.Heard) (G : Fork) :
    readTl g ((K3.seatCalls claim).put s h G) = readTl g s := by
  show readTl g ((s.putFork G).hearLook h) = readTl g s
  rw [wide_hearLook, wide_putFork]

/-- A yes of the kind's decision, at a seat whose laying leaves `wide`. -/
theorem decideVia_wide {Cl : Type} (seat : K3.Seat S Cl)
    (hput : ∀ s h G, readTl g (seat.put s h G) = readTl g s) (p : First.Look.P) (s s' : S)
    (rs : List Fmt.RoundView) (h : K3.Law.decideVia seat p s rs = .ok s') :
    readTl g s' = readTl g s := by
  unfold K3.Law.decideVia at h
  obtain ⟨F, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨x, _, h⟩ := bindOk h
  obtain rfl : seat.put s x.1 x.2 = s' := Except.ok.inj h
  exact hput s x.1 x.2

/-- The steps without a round that the kind joins behind. -/
theorem quietAt_wide (X : Verify.Public) (i : Nat) (digits : Bool) (f : S → Except String S)
    (hf : K3.quietAt X i digits = some f) (s s' : S) (h : f s = .ok s') :
    readTl g s' = readTl g s := by
  have hD : ∀ used claims, K3.quietDigits used claims s = .ok s' →
      readTl g s' = readTl g s := by
    intro used claims h
    unfold K3.quietDigits at h
    obtain ⟨F, _, h⟩ := bindOk h
    obtain ⟨G, _, h⟩ := bindOk h
    obtain rfl : s.putFork G = s' := Except.ok.inj h
    exact wide_putFork s G
  unfold K3.quietAt at hf
  dsimp only at hf
  generalize (if X.p4 then (2 : Nat) else 1) = step at hf
  split at hf
  · split at hf
    · obtain rfl := Option.some.inj hf
      unfold K3.quietHead at h
      cases hh : s.here with
      | head a =>
        simp only [hh] at h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨c, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain rfl : { s with here := .head { a with claim := some c } } = s' := Except.ok.inj h
        refine wide_of_tl ?_
        simp [S.tl?, hh]
      | _ => simp [hh] at h
    · exact nomatch hf
  · split at hf
    · split at hf
      · obtain ⟨hp, _, rfl⟩ := Option.map_eq_some_iff.1 hf
        exact hD _ _ h
      · obtain rfl := Option.some.inj hf
        unfold K3.quietLook at h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain rfl : s = s' := Except.ok.inj h
        rfl
    · split at hf
      · obtain ⟨a, _, rfl⟩ := Option.map_eq_some_iff.1 hf
        exact hD _ _ h
      · exact nomatch hf

section
variable {Cl : Type} {claim : Aff → Cl} {X : Verify.Public} {codes : Codes}
  {shape : Params.ReqShape} {a : Place}

/-- The kind's own block. -/
theorem theOwn_leaves_tl (hg : Keeps4 g) {runs : Bool} {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : b.Leaves (readTl g) := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨dg, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have hput : ∀ s h G,
          readTl g ((if dg then K3.seatDigits claim else K3.seatCalls claim).put s h G) =
            readTl g s := by
        intro s y G
        cases dg
        · exact putCalls_wide claim s y G
        · exact putDigits_wide hg claim s y G
      intro s rs gs s' hd
      dsimp only at hd
      split at hd <;> exact decideVia_wide _ hput p s s' rs hd

/-- With the step without a round joined behind. -/
theorem theWhole_leaves_tl (hg : Keeps4 g) {runs : Bool} {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : b.Leaves (readTl g) := by
  unfold K3.theWhole at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 := theOwn_leaves_tl hg hc
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact leavesAndThen S Cl _ (readTl g) _ c _ h0 fun s _ _ s' hd =>
      quietAt_wide X i _ f hq s s' hd
  · exact h0

/-- **Every block that the kind makes at an address leaves every such reading.** -/
theorem theStated_leaves_tl (hg : Keeps4 g) {readers : ℕ → Option (K3.Readers S)}
    {b : Block S Cl} (h : K3.theStated claim readers X codes shape a = some b) :
    b.Leaves (readTl g) := by
  unfold K3.theStated at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have hk := theWhole_leaves_tl hg hw
  split at h
  · obtain rfl := Option.some.inj h
    exact hk
  · split at h
    · obtain rfl := Option.some.inj h
      exact hk
    · split at h
      · obtain rfl := Option.some.inj h
        exact hk
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact hk

/-- **Every block that the kind makes at an address leaves `wide`.** -/
theorem theStated_leaves_wide {readers : ℕ → Option (K3.Readers S)} {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : b.Leaves wide :=
  theStated_leaves_tl keeps4_wideOf h

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.putDigits_wide
#print axioms VerifiableInference.Desc.First.K8.quietAt_wide
#print axioms VerifiableInference.Desc.First.K8.theStated_leaves_tl
#print axioms VerifiableInference.Desc.First.K8.theStated_leaves_wide
