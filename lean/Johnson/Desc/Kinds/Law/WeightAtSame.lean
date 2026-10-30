-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WeightAtSame.lean: WHAT THE SENTENCE WeightAt
(Johnson/Desc/Kinds/Law/MergeClaimAt.lean: the output head's own claim on the committed weights, at
the verifier's state) READS OF THE STATE, AS LEMMAS: for whoever must carry that sentence over a
sub-protocol of the head's segment that stands behind the head's own rounds.

THE FOOTPRINT. WeightAt W s c m says: there are letters g and a hearing H with
given ... s = .ok g, (seatAt ...).heard s = some H, and WeightTrue c ((seatAt ...).ledger s) m noEnt
at them. Of the state s it reads:
  through given: the heard reply (out.reply); the request's words (req); that the state stands in an
    opened head's segment, and what the lookup on the calls has heard there (lookHeard);
  through heard: the head's x and squaresP, and, of the head's ledger of hidden values, THAT
    SOMETHING IS SHOWN UNDER EVERY SLOT THAT x NAMES (Johnson/Stored/HeadSeat.lean: allOf): else
    heard answers nothing and the sentence is false;
  through WeightTrue: of H the last sumcheck's challenges and the number of ONE slot, its second end
    value's; of the ledger what is shown under that slot and its factor.
It reads neither the head's tables (t) nor the arrays' numbers of columns.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  weightAt_same: THE THREE READERS: where given and heard answer alike at two states, and the second
      end value's form is worth the same at the two ledgers: the sentence holds at both or at none.
  KeptW s s': THE FIELDS: both states stand in a head's segment; x, squaresP, opened, lookHeard, the
      heard reply and the request's words are the same; the second's ledger is later than the
      first's (OnBytes.PscRun.Later: what lies under a filled slot is kept). It is
      Law/RunsFixed.lean's Alike less its clauses on t and on the columns.
  given_kept, heard_kept: the two readers under KeptW.
  weightSlot_filled: where heard answers, the one slot is x.tH.sEnd + 1, and it is filled.
  weightAt_kept: UNDER KeptW s s', WHERE heard ANSWERS AT THE EARLIER STATE s: the sentence holds at
      both or at none.

Every letter under "there is": KeptW: o, o': pinned by the two states' field here.
weightSlot_filled: x: pinned by o.x = some x. In weightAt_kept's premise: H: pinned by heard at s.
What it does not say. THAT heard ANSWERS AT THE EARLIER STATE: a premise of weightAt_kept: WITHOUT
IT THE WAY BACK FAILS: a later ledger may show what the earlier one does not. That any sub-protocol
meets KeptW. Nothing on soundness.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.MergeClaimAt
import Johnson.Desc.Kinds.Law.RunsFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First (S HeadOwn)

/-! ## 1 The three readers -/

/-- **The sentence reads the state through three readers.** -/
theorem weightAt_same (W : OnBytes.Model.Verify.Public) (s s' : S) (c : Cells) (m : Nat → E)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' =
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s)
    (hh : (seatAt W.hS (readsOf W)).heard s' = (seatAt W.hS (readsOf W)).heard s)
    (hp : ∀ H : HeardAll, (seatAt W.hS (readsOf W)).heard s = some H →
      atWorld ((seatAt W.hS (readsOf W)).ledger s') m noEnt (H.2.2.logits.end_ 1).var =
        atWorld ((seatAt W.hS (readsOf W)).ledger s) m noEnt (H.2.2.logits.end_ 1).var) :
    WeightAt W s' c m ↔ WeightAt W s c m := by
  constructor
  · rintro ⟨g, H, e1, e2, e3⟩
    refine ⟨g, H, hg ▸ e1, hh ▸ e2, ?_⟩
    have e3' := e3
    unfold WeightTrue at e3' ⊢
    exact (hp H (hh ▸ e2)).symm.trans e3'
  · rintro ⟨g, H, e1, e2, e3⟩
    refine ⟨g, H, hg.trans e1, hh.trans e2, ?_⟩
    have e3' := e3
    unfold WeightTrue at e3' ⊢
    exact (hp H e2).trans e3'

/-! ## 2 The fields -/

/-- **What a sub-protocol between owes**: s' goes on from s, as far as the sentence reads. -/
def KeptW (s s' : S) : Prop :=
  ∃ o o', s.here = .head o ∧ s'.here = .head o' ∧ o'.x = o.x ∧ o'.squaresP = o.squaresP ∧
    o'.opened = o.opened ∧ o'.lookHeard = o.lookHeard ∧ s'.out.reply = s.out.reply ∧
    s'.req = s.req ∧ Later o.F o'.F

/-- Alike gives it. -/
theorem KeptW.of_alike {s s' : S} (a : Alike s s') : KeptW s s' := by
  obtain ⟨o, o', ho, ho', e1, e2, _, e4, e5, e6, e7, hL, _⟩ := a
  exact ⟨o, o', ho, ho', e1, e2, e4, e5, e6, e7, hL⟩

section At
variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat)

theorem given_kept (p : Par) {s s' : S} (a : KeptW s s') :
    given p (seatAt h iU3) s' = given p (seatAt h iU3) s := by
  obtain ⟨o, o', ho, ho', _, _, eo, el, er, eq, _⟩ := a
  refine given_congr p (seatAt h iU3) ?_ er (requestOf_congr eq)
  show s'.lookHeard?.map _ = s.lookHeard?.map _
  unfold S.lookHeard?
  rw [ho, ho']
  simp only [eo, el]

theorem heard_kept {s s' : S} (a : KeptW s s') (H : HeardAll)
    (e : (seatAt h iU3).heard s = some H) : (seatAt h iU3).heard s' = some H := by
  obtain ⟨o, o', ho, ho', ex, es, _, _, _, _, hL⟩ := a
  have e' : (match s.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H := e
  show (match s'.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H
  rw [ho] at e'
  rw [ho']
  simp only [ex, es] at e' ⊢
  obtain ⟨q, hq, e1⟩ := Option.bind_eq_some_iff.mp e'
  obtain ⟨x, hx, e2⟩ := Option.bind_eq_some_iff.mp e1
  rw [hq, hx]
  exact allOf_later hL x _ H e2

end At

/-! ## 3 The one slot -/

/-- The text's 0 is the library's. -/
theorem zero_is : (0 : E) = OnBytes.zeroE := rfl

/-- The hidden value under a filled slot is the same at every later ledger. -/
theorem hidden_kept {F G : Fork} (m : Nat → E) {j : Nat} (hL : Later F G)
    (hf : OnBytes.PscRun.Filled F j) : hidden G m j = hidden F m j := by
  obtain ⟨_, h1, h2⟩ := hL.keep j hf
  unfold hidden
  rw [zero_is, h1, h2]

theorem atWorld_slot (F : Fork) (m : Nat → E) (ent : Nat → Nat → Nat → E) (j : Nat) :
    atWorld F m ent (Aff.slot j) = (Aff.slot j).const + OnBytes.oneE * hidden F m j := by
  simp [atWorld, atHidden, Aff.slot]

theorem hidAt_spec {F : Fork} {j : Nat} {a : Hid} (e : hidAt F j = some a) :
    a.var = Aff.slot j ∧ OnBytes.PscRun.Filled F j := by
  unfold hidAt at e
  cases hs : F.shown j with
  | none => rw [hs] at e; simp at e
  | some x =>
    rw [hs] at e
    simp only [Option.map_some, Option.some.injEq] at e
    subst e
    refine ⟨rfl, ?_⟩
    unfold Fork.shown at hs
    split at hs
    · rename_i hc
      exact (Eq.mp (Bool.and_eq_true _ _) hc).2
    · cases hs

theorem sumOf_ends {F : Fork} {t : OnBytes.Model.Tsc} {r : Point} {n : Nat} {sm : Sum}
    (e : sumOf F t r n = some sm) : hidsAt F t.sEnd n = some sm.ends := by
  unfold sumOf at e
  obtain ⟨a1, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a2, h2, e⟩ := Option.bind_eq_some_iff.mp e
  obtain rfl := Option.some.inj e
  exact h2

theorem allOf_logits {F : Fork} {x : OnBytes.Model.Head.Heard}
    {sq : Option Part.MaskedSum.Heard} {H : HeardAll} (e : allOf F x sq = some H) :
    sumOf F x.tH (x.tH.r ++ x.rs.reverse) 2 = some H.2.2.logits := by
  unfold allOf at e
  obtain ⟨a1, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a2, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a3, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a4, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a5, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a6, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a7, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a8, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a9, h9, e⟩ := Option.bind_eq_some_iff.mp e
  obtain rfl := Option.some.inj e
  exact h9

/-- **Where heard answers, the one slot is the last sumcheck's second end value's, and it is
filled.** -/
theorem weightSlot_filled (h : OnBytes.Model.Head.Shape) (iU3 : Nat) {s : S} {o : HeadOwn}
    (ho : s.here = .head o) {H : HeardAll} (e : (seatAt h iU3).heard s = some H) :
    ∃ x, o.x = some x ∧ (H.2.2.logits.end_ 1).var = Aff.slot (x.tH.sEnd + 1) ∧
      OnBytes.PscRun.Filled o.F (x.tH.sEnd + 1) := by
  have e' : (match s.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H := e
  rw [ho] at e'
  obtain ⟨q, _, e1⟩ := Option.bind_eq_some_iff.mp e'
  obtain ⟨x, hx, e2⟩ := Option.bind_eq_some_iff.mp e1
  have h1 := (hidsAt_spec (sumOf_ends (allOf_logits e2))).2 1 (by decide)
  exact ⟨x, hx, (hidAt_spec h1).1, (hidAt_spec h1).2⟩

/-! ## 4 The sentence under KeptW -/

/-- **UNDER KeptW, WHERE heard ANSWERS AT THE EARLIER STATE, THE SENTENCE HOLDS AT BOTH STATES OR AT
NONE.** -/
theorem weightAt_kept (W : OnBytes.Model.Verify.Public) {s s' : S} (a : KeptW s s')
    (hh : ∃ H, (seatAt W.hS (readsOf W)).heard s = some H) (c : Cells) (m : Nat → E) :
    WeightAt W s' c m ↔ WeightAt W s c m := by
  obtain ⟨H0, h0⟩ := hh
  refine weightAt_same W s s' c m (given_kept _ _ _ a) ((heard_kept _ _ a H0 h0).trans h0.symm) ?_
  intro H hH
  obtain ⟨o, o', ho, ho', _, _, eo, _, _, _, hL⟩ := a
  obtain ⟨x, _, hv, hf⟩ := weightSlot_filled _ _ ho hH
  rw [hv, atWorld_slot, atWorld_slot]
  have l1 : (seatAt W.hS (readsOf W)).ledger s = (if o.opened then some o.F else none).getD {} := by
    show s.fork?.getD {} = _
    unfold S.fork?
    rw [ho]
  have l2 : (seatAt W.hS (readsOf W)).ledger s' =
      (if o'.opened then some o'.F else none).getD {} := by
    show s'.fork?.getD {} = _
    unfold S.fork?
    rw [ho']
  rw [l1, l2, eo]
  cases o.opened with
  | false => rfl
  | true =>
    show _ + _ * hidden o'.F m _ = _ + _ * hidden o.F m _
    rw [hidden_kept m hL hf]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.weightAt_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.given_kept
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heard_kept
#print axioms VerifiableInference.Desc.Kinds.Head.Law.weightSlot_filled
#print axioms VerifiableInference.Desc.Kinds.Head.Law.weightAt_kept
