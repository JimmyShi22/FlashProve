-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/RowsOfSegment.lean: the kind "the code switch" (K2): WHAT
`segmentGroupRows` (Honest/K2/Closing.lean) RETURNS, ENTRY BY ENTRY: where it returns, the rows number n
of its list, for n a message of the segment's first sending in front of the fold's mask, are what
`messageRows` returns at the stretch number base + n; and the like for the fold's mask. One
definition, of a relation; statements with their proofs.

  `OkGives`   P x: whatever x returns has P: where x refuses nothing is said
  `OkGives.bind`, `.guard`, `.ite`   it passes through the steps of a text with refusals; at a bind
              the equation of the first step is kept
  `laidRow_at`       a tool: the row number n of a list that was laid message by message
  `rowsCore_gives`   the two ends at `rowsCore` (Honest/K2/Law/SegmentAlike.lean)
  `inFirstOf_at`     the member number n of the first sending's list: its shape and its main rows
  `segmentRows_row`, `segmentRows_mask`   THE ENDS

Kin: `OkLe` (Honest/K2/Law/ClosingGrows.lean) holds two texts against each other; this one holds one
text's return against a property. `rowsCore_count` (Honest/K2/Law/GroupCount.lean) walks the same
text for the lists' lengths. Two more laws read a return of `segmentGroupRows` or of the step above it,
in two other files: `segmentRows_members` (Honest/K2/Law/GroupMembers.lean)
and `segmentLeft_inv` (Honest/K2/Law/SegmentLeftInv.lean). Tools called: `mapM_at`, `map_ok`
(Honest/K2/Law/Reads.lean).

Limits. On a text with refusals: k is a letter: no sentence on what a stretch holds. The later
sendings' rows: not said here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows zeroG)
open Reads

variable {α β : Type}

/-- Whatever x returns has P. -/
def OkGives (P : α → Prop) (x : Except String α) : Prop := ∀ a, x = .ok a → P a

theorem OkGives.bind {x : Except String α} {f : α → Except String β} {P : β → Prop}
    (h : ∀ a, x = .ok a → OkGives P (f a)) : OkGives P (x.bind f) := by
  intro b hb
  cases x with
  | error e => cases hb
  | ok a => exact h a rfl b hb

theorem OkGives.ite {c : Prop} [Decidable c] {x₀ x : Except String α} {P : α → Prop}
    (h₀ : c → OkGives P x₀) (h : ¬c → OkGives P x) : OkGives P (if c then x₀ else x) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact h₀ hc
  · rw [if_neg hc]
    exact h hc

theorem OkGives.guard {c : Prop} [Decidable c] {e : String} {f : PUnit → Except String α}
    {P : α → Prop} (h : OkGives P (f PUnit.unit)) :
    OkGives P (if c then (throw e : Except String PUnit) >>= f else pure PUnit.unit >>= f) :=
  OkGives.ite (fun _ a ha => by cases ha) fun _ => h

/-- The row number n of a list that was laid message by message. -/
theorem laidRow_at (table : FreshTable) (codes : OnBytes.Codes) (k : Nat → Except String Stretch)
    (off : Nat) {A : List Laid} {r₀ : List Johnson.Prover.Send.Rows}
    (h₀ : (A.zipIdx.mapM fun x =>
      (k (off + x.2)).bind (messageRows table codes x.1.1 none x.1.2)) = .ok r₀)
    {n : Nat} {s : OnBytes.OracleShape} {d : Nat → Nat → Cb.Gl.E} (hx : A[n]? = some (s, d)) :
    ∃ r, r₀[n]? = some r ∧ (k (off + n)).bind (messageRows table codes s none d) = .ok r := by
  have hz : A.zipIdx[n]? = some ((s, d), n) := by
    rw [List.getElem?_zipIdx, hx]
    simp
  obtain ⟨b, hb, hg⟩ := mapM_at _ _ _ h₀ n ((s, d), n) hz
  exact ⟨b, hb, hg⟩

/-- **The two ends, at `rowsCore`.** -/
theorem rowsCore_gives (table : FreshTable) (S : SegmentPub) (ps : Bool)
    (prevKept : List OnBytes.OracleShape) (A : List Laid) (B : List Laid × Nat)
    (k : Nat → Except String Stretch) (base : Nat) (withFresh : Bool) :
    OkGives (fun R : GroupRows =>
      (∀ n s d, A[n]? = some (s, d) → ∃ r, R.rows[n]? = some r ∧
        (k (base + n)).bind (messageRows table S.sizes.codes s none d) = .ok r) ∧
      (withFresh = true → ∃ r, R.fresh = some r ∧
        (k (base + ((S.sent.headD #[]).size - 1))).bind
          (messageRows table S.sizes.codes
            ((S.sent.headD #[]).getD ((S.sent.headD #[]).size - 1) default).shape
            (some S.foldVars) fun _ _ => zeroG) = .ok r))
      (rowsCore table S ps prevKept A B k base withFresh) := by
  unfold rowsCore
  dsimp only
  refine OkGives.guard ?_
  refine OkGives.guard ?_
  refine OkGives.guard ?_
  refine OkGives.guard ?_
  refine OkGives.guard ?_
  refine OkGives.bind fun r₀ h₀ => ?_
  have first : ∀ (r₁ : List Johnson.Prover.Send.Rows) n s d, A[n]? = some (s, d) →
      ∃ r, (r₀ ++ r₁)[n]? = some r ∧
        (k (base + n)).bind (messageRows table S.sizes.codes s none d) = .ok r := by
    intro r₁ n s d hx
    obtain ⟨r, hr, hg⟩ := laidRow_at table S.sizes.codes k base h₀ hx
    exact ⟨r, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hr).1, hr], hg⟩
  refine OkGives.ite (fun _ => ?_) fun hw => ?_
  · refine OkGives.bind fun fr hfr => ?_
    obtain ⟨r, hr, rfl⟩ := map_ok hfr
    refine OkGives.bind fun r₁ _ => ?_
    intro R hR
    obtain rfl := Except.ok.inj hR
    exact ⟨first r₁, fun _ => ⟨r, rfl, hr⟩⟩
  · refine OkGives.bind fun fr _ => ?_
    refine OkGives.bind fun r₁ _ => ?_
    intro R hR
    obtain rfl := Except.ok.inj hR
    exact ⟨first r₁, fun h => absurd h hw⟩

/-- The member number n of the first sending's list. -/
theorem inFirstOf_at (S : SegmentPub) (prev : Option Left) (own : Nat → Nat → Nat → Cb.Gl.E)
    {n : Nat} (hn : n < (S.sent.headD #[]).size - 1) :
    (inFirstOf S prev own)[n]? =
      some (((S.sent.headD #[]).getD n default).shape, dataAtOf S prev own n) := by
  unfold inFirstOf
  generalize (S.sent.headD #[]) = arr at hn ⊢
  have hs : n < arr.size := by omega
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_take_of_lt hn,
    Array.getElem?_toList, Array.getElem?_eq_getElem hs]
  simp [Array.getD, hs]

/-- **THE ROWS OF MESSAGE NUMBER n OF THE FIRST SENDING**, in front of the fold's mask. -/
theorem segmentRows_row {table : FreshTable} {S : SegmentPub} {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E}
    {k : Nat → Except String Stretch} {base : Nat} {withFresh : Bool} {R : GroupRows}
    (h : segmentGroupRows table S prev prevKept own k base withFresh = .ok R) {n : Nat}
    (hn : n < (S.sent.headD #[]).size - 1) :
    ∃ r, R.rows[n]? = some r ∧
      (k (base + n)).bind (messageRows table S.sizes.codes ((S.sent.headD #[]).getD n default).shape
        none (dataAtOf S prev own n)) = .ok r := by
  rw [segmentRows_eq] at h
  have g := rowsCore_gives table S prev.isSome prevKept (inFirstOf S prev own)
    (laterOf S prev.isSome own) k base withFresh R h
  exact g.1 n _ _ (inFirstOf_at S prev own hn)

/-- **THE FOLD's MASK.** -/
theorem segmentRows_mask {table : FreshTable} {S : SegmentPub} {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E}
    {k : Nat → Except String Stretch} {base : Nat} {R : GroupRows}
    (h : segmentGroupRows table S prev prevKept own k base true = .ok R) :
    ∃ r, R.fresh = some r ∧
      (k (base + ((S.sent.headD #[]).size - 1))).bind
        (messageRows table S.sizes.codes
          ((S.sent.headD #[]).getD ((S.sent.headD #[]).size - 1) default).shape
          (some S.foldVars) fun _ _ => zeroG) = .ok r := by
  rw [segmentRows_eq] at h
  have g := rowsCore_gives table S prev.isSome prevKept (inFirstOf S prev own)
    (laterOf S prev.isSome own) k base true R h
  exact g.2 rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.OkGives
#print axioms ProofFile.Honest.K2.Law.OkGives.bind
#print axioms ProofFile.Honest.K2.Law.OkGives.ite
#print axioms ProofFile.Honest.K2.Law.OkGives.guard
#print axioms ProofFile.Honest.K2.Law.laidRow_at
#print axioms ProofFile.Honest.K2.Law.rowsCore_gives
#print axioms ProofFile.Honest.K2.Law.inFirstOf_at
#print axioms ProofFile.Honest.K2.Law.segmentRows_row
#print axioms ProofFile.Honest.K2.Law.segmentRows_mask
