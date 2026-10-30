-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Back.lean: no effect on the statement loses a claim.

Holds (Johnson/Desc/Means/Holds.lean) says that all that a statement claims holds of the words. This
file shows, for each of the pure effects on a statement that are named below: if Holds is true of
the statement behind the effect, it was true of the statement in front. So along a stretch of a
chain that changes the statement by these effects, words of which the statement in front does not
hold are words of which the statement behind does not hold. The beginning of a test is in
Johnson/Desc/Means/Holds.lean (Holds.of_begun, begin_catches).

An oracle message that is admitted gets its sample rows written anew. No claim is lost by that if it
had none before: NoneYet says that an oracle message that is not marked as sampled has no sample
row. It is kept by the effects, and the admitting tests the mark.

Main definitions: NoneYet.
Main theorems: Holds.of_withRow, Holds.of_withGroup, Holds.of_joined, Holds.of_stSent,
Holds.of_admitted, Holds.of_closeLedgers, Holds.of_onOracle; NoneYet.start, NoneYet.sameOracles,
NoneYet.onOracle, NoneYet.marked, NoneYet.stSent, NoneYet.closeLedgers.

What is not claimed. The converses. That a block changes the statement by these effects alone.
Nothing on soundness.

-/
import Johnson.Desc.Means.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {S S' : Statement} {G : Group}

/-! ## What is read behind a change of one group or one oracle message -/

theorem rows_modify {A : Array Group} {g : Nat} {f : Group → Group}
    (hf : ∀ G : Group, ∀ r ∈ G.rows.toList, r ∈ (f G).rows.toList) (g' : Nat) (G : Group)
    (h : A[g']? = some G) :
    ∃ G', (A.modify g f)[g']? = some G' ∧ ∀ r ∈ G.rows.toList, r ∈ G'.rows.toList := by
  rw [Array.getElem?_modify]
  by_cases c : g = g'
  · rw [if_pos c, h]
    exact ⟨f G, rfl, hf G⟩
  · rw [if_neg c]
    exact ⟨G, h, fun _ c => c⟩

theorem samples_modify {A : Array Oracle} {o : Nat} {f : Oracle → Oracle}
    (hf : ∀ x : Oracle, A[o]? = some x → ∀ r ∈ x.sampleRows.toList, r ∈ (f x).sampleRows.toList)
    (o' : Nat) (x : Oracle) (h : A[o']? = some x) :
    ∃ x' : Oracle, (A.modify o f)[o']? = some x' ∧
      ∀ r ∈ x.sampleRows.toList, r ∈ x'.sampleRows.toList := by
  rw [Array.getElem?_modify]
  by_cases c : o = o'
  · rw [if_pos c, h]
    exact ⟨f x, rfl, hf x (by rw [c]; exact h)⟩
  · rw [if_neg c]
    exact ⟨x, h, fun _ c => c⟩

/-! ## An oracle message that is not sampled has no sample row -/

/-- An oracle message that is not marked as sampled has no sample row. -/
def NoneYet (S : Statement) : Prop :=
  ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x → x.sampled = false → x.sampleRows = #[]

theorem NoneYet.start (codes : Codes) : NoneYet { codes := codes, oracles := #[], groups := #[] } :=
  fun o x h => by simp at h

theorem NoneYet.sameOracles (h : NoneYet S) (ho : S'.oracles = S.oracles) : NoneYet S' :=
  fun o x hx => h o x (ho ▸ hx)

/-- An effect on one oracle message that leaves its mark and its sample rows. -/
theorem NoneYet.onOracle (h : NoneYet S) (o : Nat) (f : Oracle → Oracle)
    (ho : S'.oracles = S.oracles.modify o f) (h1 : ∀ x, (f x).sampled = x.sampled)
    (h2 : ∀ x, (f x).sampleRows = x.sampleRows) : NoneYet S' := by
  intro o' x' hx' hs
  rw [ho] at hx'
  rcases getElem?_modify_some hx' with ⟨_, x, hx, rfl⟩ | ⟨_, hx⟩
  · rw [h2]
    exact h o' x hx (by rw [← h1]; exact hs)
  · exact h o' x' hx hs

/-- An effect on one oracle message that marks it as sampled. -/
theorem NoneYet.marked (h : NoneYet S) (o : Nat) (f : Oracle → Oracle)
    (ho : S'.oracles = S.oracles.modify o f) (h1 : ∀ x, (f x).sampled = true) : NoneYet S' := by
  intro o' x' hx' hs
  rw [ho] at hx'
  rcases getElem?_modify_some hx' with ⟨_, x, _, rfl⟩ | ⟨_, hx⟩
  · rw [h1] at hs
    cases hs
  · exact h o' x' hx hs

theorem NoneYet.stSent (h : NoneYet S) (sent : Array OracleNotice) :
    NoneYet (Slice.stSent S sent) := by
  intro o x' hx' hs
  by_cases ho : o < S.oracles.size
  · rw [Slice.stSent_old S sent o ho] at hx'
    exact h o x' hx' hs
  · obtain ⟨i, rfl⟩ : ∃ i, o = S.oracles.size + i := ⟨o - S.oracles.size, by omega⟩
    rw [Slice.stSent_new] at hx'
    obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.1 hx'
    rfl

theorem NoneYet.closeLedgers (h : NoneYet S) (l : List Nat) :
    NoneYet (Slice.closeLedgers S l) := by
  induction l generalizing S with
  | nil => exact h
  | cons a l ih =>
    have h1 : NoneYet { S with oracles := S.oracles.modify a fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } :=
      h.onOracle a (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
        rfl (fun _ => rfl) (fun _ => rfl)
    exact ih h1

/-! ## Backwards over each effect -/

variable {K : Type} [CommRing K] (ρ : Reading K) {m : Words K}

/-- A row is added: all that was claimed before, and the new row. -/
theorem Holds.of_withRow (hI : InOrder S) (g : Nat) (row : Row) (hG : S.groups[g]? = some G)
    (h : Holds ρ (Slice.withRow S g row) m) : Holds ρ S m ∧ Says ρ S row m := by
  refine ⟨Holds.back ρ hI (extends_withRow S g row)
    (rows_modify (f := fun G => { G with rows := G.rows.push row }) fun G r hr => by
      show r ∈ (G.rows.push row).toList
      simp [hr])
    (fun o x hx => ⟨x, hx, fun _ c => c⟩) h, ?_⟩
  have e := h.rows g _ (Slice.withRow_group S g row G hG) row (by simp)
  unfold Says at e ⊢
  rw [value_congr ρ (S := S) (S' := Slice.withRow S g row) rfl rfl] at e
  exact e

theorem Holds.of_withGroup (hI : InOrder S) (a b : Nat) (h : Holds ρ (Slice.withGroup S a b) m) :
    Holds ρ S m := by
  refine Holds.back ρ hI (extends_withGroup S a b) (fun g G hG => ⟨G, ?_, fun _ c => c⟩)
    (fun o x hx => ⟨x, hx, fun _ c => c⟩) h
  show (S.groups.push { code := a, maskCode := b })[g]? = some G
  have hg : g < S.groups.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hG
    cases hG
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hg)]
  exact hG

theorem Holds.of_joined (hI : InOrder S) (g o : Nat) (k : Bool) (G : Group)
    (h : Holds ρ (Slice.withMessageInGroup S g o k G) m) : Holds ρ S m :=
  Holds.back ρ hI (extends_withMessageInGroup S g o k G)
    (rows_modify (f := fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k })
      fun _ _ c => c)
    (samples_modify (f := fun x => { x with groups := x.groups ++ [g] }) fun _ _ _ c => c) h

theorem Holds.of_stSent (hI : InOrder S) (sent : Array OracleNotice)
    (h : Holds ρ (Slice.stSent S sent) m) : Holds ρ S m := by
  refine Holds.back ρ hI (extends_stSent S sent) (fun g G hG => ⟨G, hG, fun _ c => c⟩)
    (fun o x hx => ⟨x, ?_, fun _ c => c⟩) h
  have ho : o < S.oracles.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
    cases hx
  rw [Slice.stSent_old S sent o ho]
  exact hx

/-- An oracle message that was not marked as sampled is admitted. -/
theorem Holds.of_admitted (hI : InOrder S) (hN : NoneYet S) (o : Nat) (s : OracleShape)
    (p : List PadPlace) (rows : Array Row)
    (hs : ∀ x : Oracle, S.oracles[o]? = some x → x.sampled = false)
    (h : Holds ρ (Slice.admitted S o s p rows) m) : Holds ρ S m :=
  Holds.back ρ hI (extends_admitted S o s p rows) (fun g G hG => ⟨G, hG, fun _ c => c⟩)
    (samples_modify (f := fun x => { x with
      sampled := true, sampleRows := rows, pad := p.map fun q => (q.part, q.index),
      ledger := Slice.freshLedger S.codes s }) fun x hx r hr => by
        rw [hN o x hx (hs x hx)] at hr
        simp at hr) h

/-- An effect on one oracle message that leaves its shape and its sample rows. -/
theorem Holds.of_onOracle (hI : InOrder S) (o : Nat) (f : Oracle → Oracle)
    (h1 : ∀ x, (f x).shape = x.shape) (h2 : ∀ x, (f x).sampleRows = x.sampleRows)
    (h : Holds ρ { S with oracles := S.oracles.modify o f } m) : Holds ρ S m :=
  Holds.back (S' := { S with oracles := S.oracles.modify o f }) ρ hI
    (Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ h1)
    (fun g G hG => ⟨G, hG, fun _ c => c⟩)
    (samples_modify (f := f) fun x _ r hr => by rw [h2]; exact hr) h

theorem Holds.of_closeLedgers (hI : InOrder S) (l : List Nat)
    (h : Holds ρ (Slice.closeLedgers S l) m) : Holds ρ S m := by
  refine Holds.back ρ hI (extends_closeLedgers S l)
    (fun g G hG => ⟨G, by rw [closeLedgers_groups]; exact hG, fun _ c => c⟩)
    (fun o x hx => ?_) h
  have e := closeLedgers_sampleRows l S o
  rw [hx] at e
  obtain ⟨x', hx', hsame⟩ := Option.map_eq_some_iff.1 e
  exact ⟨x', hx', fun r hr => by rw [hsame]; exact hr⟩

end OnBytes.Means
