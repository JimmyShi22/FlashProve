-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/HeardCalls.lean: behind a yes of K3's seated block at the calls' address of a
layers' link, what the record holds in LayOwn.fo, which is what K4's hearing is handed, has the
layout's own shape. The half of the planes' row's premise hNC that names no seat.

The lookup's files' law (Johnson/Desc/First/Look/K3HeardShape.lean: heard_shape_lay) ends at K3's
own heard record behind a yes of the kind's block K3.block at the calls' seat: (K3.seatCalls
claim).heard s' = some g, g.shape = X.y.fo; that reader is S.lookHeard?. Two steps part it from K4:
(1) what stands in a description is not K3.block but what K3.theStated gives:
the block with the hearing exchanged (K3.Law.blockVia), a test more on the plan, and a step without
a round joined behind; (2) K4's hearing is handed LayOwn.fo, not lookHeard.

Main theorems (namespace `Meaning.Planes`).
  `putFork_lay`, `hearLook_lay`: plain lemmas on the carried record's text.
  `k3_lays_both`: behind a yes of K3.block at the calls' seat: where the record stands in a layers'
      link a: a.fo = a.lookHeard (S.hearLook lays both at once).
  `quietAt_calls_same`: what is joined behind the lookup on the calls hands the record on as it is
      (by the lookups' `quietLook_ok`, Johnson/Desc/First/Look/K3QuietLaws.lean).
  `theStated_calls_yes`: **a yes of the block that K3.theStated gives at the calls' address, where
      its test on the plan says yes, holds a yes of K3.block at the calls' seat, at the place's own
      parameters, WITH THE SAME RECORD BEHIND.** By the lookups' swap `K3.Law.blockVia_decide`
      (Johnson/Top/H/K3Via/Blocks.lean), which asks the test on the plan.
  `heard_fo_calls`: **so, where publicOf returns X and i is a layers' link: for all a, fo with
      s.here = .lay a, a.fo = some fo: fo.shape = X.y.fo.**

ALL PREMISES of heard_fo_calls: hX (publicOf's return) · hn, h0 (i is no head's link; i is even
where p4) · h (the maker's return at the address ⟨1, some i, K3.pieceAt X i false, .K3⟩) · hp (that
block's test on the plan) · hy (its yes) · ha, hfo (look-ups in the record behind). WHO CAN PAY: hX,
hn, h0: the scope · h: the seat · hp: the decision's yes (it asks the tests on the plan) · hy: the
fold.
OBJECT · LETTERS. Object: the lookups' K3.theStated, theWhole, theOwn, K3.Law.blockVia,
K3.block, K3.seatCalls; State's hearLook, putFork. No seat of a description is named.
Letters: claim, readers, codes, shape: free.
Compiled with the whole library.









Limits. One direction. A block that refuses always meets all this emptily. Nothing on soundness.

-/
import Johnson.Desc.First.Look.K3HeardShape
import Johnson.Desc.First.Look.K3Stated
import Johnson.Desc.First.Look.K3SeatLaw
import Johnson.Desc.First.Look.K3QuietLaws
import Johnson.Top.H.K3Via.Blocks
import Johnson.Desc.BlockKeeps
import Johnson.Desc.K12.FrameLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K3 (mark_here)

/-- Where the record behind putFork stands in a layers' link, so did the record in front. -/
theorem putFork_lay {s : S} {G : Fork} {a' : LayOwn} (h : (s.putFork G).here = .lay a') :
    ∃ a, s.here = .lay a ∧ a' = { a with F := G } := by
  unfold S.putFork at h
  split at h
  · rename_i a ha
    exact ⟨a, ha, (Here.lay.inj h).symm⟩
  · cases h
  · rename_i a ha
    split at h
    · cases h
    · rw [ha] at h
      cases h
  · rename_i h1 h2 h3
    exact absurd h (h1 a')

/-- Where the record behind hearLook stands in a layers' link, so did the record in front; and if
nothing was heard there, both homes hold what is heard now. -/
theorem hearLook_lay {s : S} {g : Forest.Heard} {a' : LayOwn} (h : (s.hearLook g).here = .lay a') :
    ∃ a, s.here = .lay a ∧
      (a.lookHeard = none → a' = { a with fo := some g, lookHeard := some g }) := by
  unfold S.hearLook at h
  split at h
  · rename_i a ha
    refine ⟨a, ha, fun h0 => ?_⟩
    rw [h0] at h
    exact (Here.lay.inj h).symm
  · rename_i a ha
    split at h
    · rw [mark_here, ha] at h
      cases h
    · cases h
  · rename_i a ha
    split at h
    · rw [mark_here, ha] at h
      cases h
    · split at h
      · rw [mark_here, ha] at h
        cases h
      · cases h
  · rename_i h1 h2 h3
    rw [mark_here] at h
    exact absurd h (h1 a')

/-- **Behind a yes of K3's own block at the seat of the calls the two homes of what was heard hold
the same.** -/
theorem k3_lays_both {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) {s s' : S}
    {rs : List Fmt.RoundView} {cols : List (List (ℕ × List UInt64))}
    (H : (K3.block (K3.seatCalls claim) piece laid before p guests).decide s rs cols = .ok s')
    {a' : LayOwn} (ha' : s'.here = .lay a') : a'.fo = a'.lookHeard := by
  unfold K3.block at H
  dsimp only at H
  obtain ⟨F, hF, H⟩ := Keeps.ebind_ok H
  obtain ⟨_, hn, H⟩ := Keeps.ebind_ok H
  obtain ⟨_, -, H⟩ := Keeps.ebind_ok H
  obtain ⟨_, -, H⟩ := Keeps.ebind_ok H
  obtain ⟨x, -, H⟩ := Keeps.ebind_ok H
  have e : s' = (s.putFork x.2).hearLook x.1 := (Except.ok.inj H).symm
  have h0 : s.lookHeard? = none := by
    have : (s.lookHeard?).isNone = true := by
      unfold need at hn
      split at hn
      · assumption
      · cases hn
    exact Option.isNone_iff_eq_none.1 this
  subst e
  obtain ⟨a1, h1, h2⟩ := hearLook_lay ha'
  obtain ⟨a, h3, rfl⟩ := putFork_lay h1
  have hnone : a.lookHeard = none := by
    unfold S.lookHeard? at h0
    rw [h3] at h0
    exact h0
  rw [h2 hnone]

/-- What is joined behind the lookup on the calls hands the record on as it is. -/
theorem quietAt_calls_same {X : Verify.Public} {i : ℕ} {f : S → Except String S}
    (h : K3.quietAt X i false = some f) {u s : S} (hf : f u = .ok s) : s = u := by
  unfold K3.quietAt at h
  dsimp only at h
  by_cases h1 : K3.isHead X i = true
  · rw [if_pos h1] at h
    simp at h
  · rw [if_neg h1] at h
    by_cases h2 : (i % (if X.p4 = true then 2 else 1) == 0) = true
    · rw [if_pos h2] at h
      simp only [Bool.false_eq_true, if_false] at h
      have e := Option.some.inj h
      subst e
      exact (K3.quietLook_ok _ _ _ hf).1
    · rw [if_neg h2] at h
      simp at h

theorem pieceAt_ne (X : Verify.Public) (i : ℕ) : K3.pieceAt X i false ≠ K3.pieceAt X i true := by
  unfold K3.pieceAt
  split <;> simp

/-- **A yes of K3's seated block at the calls' address, where its test on the plan says yes, holds a
yes of the kind's own block (K3.block) at the calls' seat, with the same record behind.** -/
theorem theStated_calls_yes {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (i : ℕ) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape ⟨1, some i, K3.pieceAt X i false, .K3⟩ = some b)
    (hp : b.planOk = true) {s1 s : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hy : b.decide s1 rs gs = .ok s) :
    ∃ p laid sent rs' gs', First.Look.placeAt X i false = some p ∧
      (K3.block (K3.seatCalls claim) (K3.pieceAt X i false) laid sent p []).decide s1 rs' gs' =
        .ok s := by
  unfold K3.theStated at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have hb : b.decide = w.decide ∧ b.planOk = w.planOk := by
    dsimp only at h
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · split at h
      · cases h
        exact ⟨rfl, rfl⟩
      · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨rfl, rfl⟩
  rw [hb.1] at hy
  rw [hb.2] at hp
  unfold K3.theWhole at hw
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 hw
  have hne : (K3.pieceAt X i false == K3.pieceAt X i true) = false :=
    beq_eq_false_iff_ne.2 (pieceAt_ne X i)
  -- the kind's own block at the address
  have hown : ∃ p laid sent key, First.Look.placeAt X i false = some p ∧
      b₀.decide = (K3.Law.blockVia (K3.seatCalls claim) (K3.pieceAt X i false) laid sent p
        []).decide ∧
      b₀.planOk = ((K3.Law.blockVia (K3.seatCalls claim) (K3.pieceAt X i false) laid sent p
        []).planOk && key) := by
    unfold K3.theOwn at h0
    split at h0
    · cases h0
    · obtain ⟨i', hi, h0⟩ := Option.bind_eq_some_iff.1 h0
      obtain rfl : i = i' := Option.some.inj hi
      obtain ⟨digits, _, h0⟩ := List.exists_of_findSome?_eq_some h0
      split at h0
      · cases h0
      · rename_i hpc
        obtain ⟨p, hpl, h0⟩ := Option.bind_eq_some_iff.1 h0
        obtain ⟨sent, _, h0⟩ := Option.bind_eq_some_iff.1 h0
        obtain ⟨laid, _, h0⟩ := Option.bind_eq_some_iff.1 h0
        obtain ⟨key, _, h0⟩ := Option.map_eq_some_iff.1 h0
        cases digits with
        | true =>
          exfalso
          apply hpc
          exact bne_iff_ne.2 (pieceAt_ne X i)
        | false =>
          subst h0
          exact ⟨p, laid, sent, key, hpl, rfl, rfl⟩
  obtain ⟨p, laid, sent, key, hpl, ed, ep⟩ := hown
  -- the step joined behind hands the record on
  have hcore : b₀.planOk = true ∧ ∃ rs' gs', b₀.decide s1 rs' gs' = .ok s := by
    dsimp only [Option.bind_some] at hy hp
    rw [hne] at hy hp
    split at hy
    · rename_i f hf
      rw [hf] at hp
      obtain ⟨u, h1, h2⟩ := (K12.andThen_ok _ _ _ s1 s rs gs).1 hy
      have e : s = u := quietAt_calls_same hf h2
      subst e
      exact ⟨(Bool.and_eq_true _ _ ▸ hp).1, _, _, h1⟩
    · rename_i hf
      rw [hf] at hp
      exact ⟨hp, _, _, hy⟩
  obtain ⟨hp0, rs', gs', h1⟩ := hcore
  rw [ep, Bool.and_eq_true] at hp0
  rw [ed] at h1
  exact ⟨p, laid, sent, rs', gs', hpl, K3.Law.blockVia_decide hp0.1 h1⟩

/-- **hNC's PAYER, WITHOUT A SEAT.** Behind a yes of K3's seated block at the calls' address of a
layers' link, where its test on the plan says yes: what the record holds in LayOwn.fo, which is what
K4's hearing is handed, has the layout's own shape: so as many calls as the layout's. -/
theorem heard_fo_calls {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (hX : Verify.publicOf pol KL layout = .ok X) (codes : Codes) (shape : ReqShape) (i : ℕ)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape ⟨1, some i, K3.pieceAt X i false, .K3⟩ = some b)
    (hp : b.planOk = true) {s1 s : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hy : b.decide s1 rs gs = .ok s) {a : LayOwn} {fo : Forest.Heard} (ha : s.here = .lay a)
    (hfo : a.fo = some fo) : fo.shape = X.y.fo := by
  obtain ⟨p, laid, sent, rs', gs', hpl, hk⟩ :=
    theStated_calls_yes claim readers X codes shape i h hp hy
  unfold First.Look.placeAt at hpl
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hpl
  obtain ⟨g', hg', hsh⟩ := First.Look.heard_shape_lay claim _ laid sent []
    (Params.settingOf X.P.frame) hX hx hn h0 hk
  have hb := k3_lays_both _ _ _ _ _ _ hk ha
  have e : some g' = some fo := by
    rw [← hfo, hb, ← hg']
    show s.lookHeard? = a.lookHeard
    unfold S.lookHeard?
    rw [ha]
  rw [← Option.some.inj e]
  exact hsh

#print axioms k3_lays_both
#print axioms theStated_calls_yes
#print axioms heard_fo_calls

end Meaning.Planes
