-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/UnheardField.lean: Johnson/IMR/UnheardAt.lean's unheard_at IN THE FORM OF OUR
THEOREMS FOR FoldFacts' FIELDS: general in «reached» and in the reader: in front of the lookup on
the calls of a segment l < 24 the segment's own part of the verifier's state is fresh: nothing is
heard in it yet. It goes in no structure. Used for the
lookups' two theorems on the other callers' public parts.

WHAT IS SAID.
  callsFit, calls_numbers   a test with code on the written list of the 358 places, decided by the
                            kernel: a place of kind K3 with piece 2 in segment l has l < 24 and
                            stands at number 14 l + 3. (At the head's segment kind K3 has other
                            pieces; the lookup on the digits is piece 7.)
  callsAll, calls_there     the other way round, so that the first test is not idle: at each number
                            14 l + 3, l < 24, the written list has such a place: 24 of them.
  calls_reject              a negative test: on the written list without its first place both
                            tests reject.
  calls_number_at           what the first test's yes gives at one number.
  unheard_field_at          **the top**: FreshLay or FreshAtt of the own part.
  own_none_field_at         at a layers' own part b: b.own = none.
  heard5_none_field_at      at an attention's own part b: b.heard5 = none.
HOW. Calls alone: unheard_at behind reach_raw and Reach.fold and calls_number_at.
THE PREMISES IN FRONT, BY NAME: hS · hR · O · hRch («reached» is reached by the wrapped
sub-protocols' steps). The fence «no mark» stands among the binders for the form's sake and IS NOT
SPENT. No test on the plan is asked.
What is not claimed. Which segments are layers' and which attention's. The head's segment. That a
state is reached: NO MEMBER. No soundness.

-/
import Johnson.IMR.UnheardAt
import Johnson.IMR.WrittenList
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc (Place KindName)

/-- On a list of places: a place of kind K3 with piece 2 in segment l has l < 24 and stands at
number 14 l + 3. A test with code. -/
def callsFit (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | some p =>
      (p.kind != KindName.K3) || (p.piece != 2) ||
        (match p.link with
         | some l => decide (l < 24) && (k == 14 * l + 3)
         | none => true)
    | none => true

set_option maxRecDepth 1000000 in
theorem calls_numbers : callsFit placesW = true := by decide +kernel

/-- The other way round, so that the test above is not idle: at each number 14 l + 3, l < 24, the
list has a place of kind K3 with piece 2 in segment l. A test with code. -/
def callsAll (ps : List Place) : Bool :=
  (List.range 24).all fun l =>
    match ps[14 * l + 3]? with
    | some p => (p.kind == KindName.K3) && (p.piece == 2) && (p.link == some l)
    | none => false

set_option maxRecDepth 1000000 in
theorem calls_there : callsAll placesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: on the written list without its first place both tests reject. -/
theorem calls_reject : callsFit (placesW.drop 1) = false ∧ callsAll (placesW.drop 1) = false := by
  decide +kernel

/-- What the test's yes gives at one number. -/
theorem calls_number_at {k l : ℕ} {p : Place} (hpl : placesW[k]? = some p) (hK : p.kind = .K3)
    (hc : p.piece = 2) (hl : p.link = some l) : l < 24 ∧ k = 14 * l + 3 := by
  have hk : k < placesW.length := by
    rcases Nat.lt_or_ge k placesW.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hpl
      cases hpl
  have h := List.all_eq_true.1 calls_numbers k (List.mem_range.2 hk)
  simp only [hpl, hK, hc, hl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  exact h

end IM

namespace Meaning.K2

open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In front of the lookup on the calls of a segment l < 24 the segment's own part is fresh**,
at whatever is reached. The fence is not spent. -/
theorem unheard_field_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a p l, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some l →
      p.kind = .K3 → p.piece = 2 →
      (∃ b, (at_ a).2.here = .lay b ∧ FreshLay b) ∨
        (∃ b, (at_ a).2.here = .att b ∧ FreshAtt b) := by
  intro k a p l hr _ hpl hl hK hc
  obtain ⟨h24, rfl⟩ := IM.calls_number_at hpl hK hc hl
  obtain ⟨_, rs, cols, f⟩ := (reach_raw (hRch _ a hr)).fold
  exact unheard_at hS hR O h24 f

/-- At a layers' own part. -/
theorem own_none_field_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a p l, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some l →
      p.kind = .K3 → p.piece = 2 → ∀ b, (at_ a).2.here = .lay b → b.own = none := by
  intro k a p l hr hu hpl hl hK hc b hb
  rcases unheard_field_at hS hR O Rch at_ hRch k a p l hr hu hpl hl hK hc with
    ⟨b', hb', q⟩ | ⟨b', hb', -⟩
  · rw [hb] at hb'
    injection hb' with e
    rw [e]
    exact q.2.1
  · rw [hb] at hb'
    cases hb'

/-- At an attention's own part. -/
theorem heard5_none_field_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a p l, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some l →
      p.kind = .K3 → p.piece = 2 → ∀ b, (at_ a).2.here = .att b → b.heard5 = none := by
  intro k a p l hr hu hpl hl hK hc b hb
  rcases unheard_field_at hS hR O Rch at_ hRch k a p l hr hu hpl hl hK hc with
    ⟨b', hb', -⟩ | ⟨b', hb', q⟩
  · rw [hb] at hb'
    cases hb'
  · rw [hb] at hb'
    injection hb' with e
    rw [e]
    exact q.2.2.2.2.2

end Meaning.K2

#print axioms IM.calls_numbers
#print axioms IM.calls_there
#print axioms IM.calls_reject
#print axioms IM.calls_number_at
#print axioms Meaning.K2.unheard_field_at
#print axioms Meaning.K2.own_none_field_at
#print axioms Meaning.K2.heard5_none_field_at
