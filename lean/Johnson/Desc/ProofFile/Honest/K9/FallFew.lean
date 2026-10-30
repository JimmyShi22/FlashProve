-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallFew.lean: K9's SHARE OF THE FALL's MEASURE, AT THE FALL's OWN
TEST: statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

  `drawnOne x`     the challenge in which the one element x is drawn
  `gathered`       what stands in front of the adding where x is drawn, from the state s: the state
                   behind the gatherer, K9's part of it, the claims; nothing where the draw or the
                   gatherer refuses or no segment is open
  `batch_split`    a yes of K9's batching gives: `gathered` answers, K9's own adding returns, and the
                   state behind is the gathered one with the new ledger (one direction)
  `tests_behind`   at that state the lens of the tests behind the adding shows the new ledger, and the
                   merge's slot of the gathered state
  `FallGood`       THE PREMISES: `K9H.SlotsGood` (Johnson/Desc/K9/Honest/SlotsFew.lean) at the ledgers
                   and claims that `gathered` yields, at the challenges at which it answers; and the
                   merge's slot is one and the same at all of them
  `batFall_few`    **UNDER THEM AT MOST n * d ELEMENTS OF THE FIELD ARE READINGS OF A chi AT WHICH K9's
                   SHARE OF THE FALL's TEST SPEAKS**, from the state s in front of the batching

WHAT IS COUNTED, AND WHAT NOT. READINGS IN THE FIELD, NOT WORDS (Johnson/Desc/K9/Honest/SlotsFew.lean's
head). IT IS NOT THE COUNT OF THE ROUND "BAT-sigma": the other kinds' shares of the test are laid silent
here; and at some chi the gatherer itself refuses (another kind's test on values inside its run of
claims): there `gathered` answers nothing and nothing is counted: that is the share in front.
WHAT IS NOT CLAIMED. That `FallGood` holds at any state of a run: its clause `fixed` is a law on the
other kinds' runs of claims; its clause `live` hangs on what the claims' makers read. A count of field
elements; no probability. Nothing
on any property.
AT K9's BARE BATCHING (`K9.batch atS p g`): for the member as the description's makers wrap it:
Honest/K9/Quiet.lean, `quiet_few_of`.
-/
import Johnson.Desc.ProofFile.Honest.K9.Fall
import Johnson.Desc.K9.Honest.SlotsFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS tAtS Where addList mergeOf drawAlone batch adds)
open VerifiableInference.Desc.K9H (SlotsGood freeSlot_few)
open VerifiableInference.Desc.First.Door (freeSlotOk)

/-- The challenge in which x alone is drawn. -/
def drawnOne (x : E) : Fmt.Drawn := ⟨[x.triple], [], [], none⟩

/-- What stands in front of the adding where x is drawn. -/
def gathered (p : Where) (g : S → Except String (List Claim × S)) (s : S) (x : E) :
    Option (S × VerifiableInference.Desc.K9.Part × List Claim) :=
  match (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] with
  | .ok t₁ =>
    match g t₁ with
    | .ok y => (atS.get? y.2).map fun a => (y.2, a, y.1)
    | .error _ => none
  | .error _ => none

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error m => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- **What a yes of the batching is.** -/
theorem batch_split (p : Where) (g : S → Except String (List Claim × S)) (s s₁ : S) (x : E)
    (h : (batch atS p g).decide s [⟨[], drawnOne x⟩] [] = .ok s₁) :
    ∃ e a cls G, gathered p g s x = some (e, a, cls) ∧ addList a.F cls = .ok G ∧
      s₁ = atS.set e { a with F := G } := by
  obtain ⟨t₁, h₁, h⟩ := bind_ok (x := (drawAlone (Cl := Claim) atS p).decide s _ []) h
  obtain ⟨s₀, _, h⟩ := bind_ok (x := atS.part t₁) h
  obtain ⟨_, _, h⟩ := bind_ok (x := VerifiableInference.Desc.K9.need "K9.draw-has-run" s₀.L.handed) h
  obtain ⟨y, hy, h⟩ := bind_ok (x := g t₁) h
  obtain ⟨a, ha, h⟩ := bind_ok (x := atS.part y.2) h
  obtain ⟨G, hG, h⟩ := bind_ok (x := addList a.F y.1) h
  refine ⟨y.2, a, y.1, G, ?_, hG, (Except.ok.inj h).symm⟩
  have ha' : atS.get? y.2 = some a := by
    unfold VerifiableInference.Desc.K9.Lens.part VerifiableInference.Desc.K9.there at ha
    cases hq : atS.get? y.2 with
    | none => rw [hq] at ha; exact nomatch ha
    | some b => rw [hq] at ha; exact congrArg some (Except.ok.inj ha)
  unfold gathered
  rw [h₁]
  simp only [hy, ha', Option.map_some]

/-- At the state behind the adding the tests' lens shows the new ledger and the gathered state's
merge's slot. -/
theorem tests_behind (e : S) (a : VerifiableInference.Desc.K9.Part) (ha : atS.get? e = some a)
    (G : Fork) : ∃ tl, tAtS.get? (atS.set e { a with F := G }) = some ⟨mergeOf e, tl, G⟩ := by
  cases hh : e.here with
  | between => simp [atS, S.link?, hh] at ha
  | fin x => simp [atS, S.link?, hh] at ha
  | mem x => simp [atS, S.link?, hh] at ha
  | lay x => exact ⟨x.tl, by simp [tAtS, atS, S.putLink, S.putFork, S.fork?, S.tl?, mergeOf, hh]⟩
  | att x => exact ⟨x.tl, by simp [tAtS, atS, S.putLink, S.putFork, S.fork?, S.tl?, mergeOf, hh]⟩
  | head x =>
    by_cases ho : x.opened = true
    · exact ⟨x.tl, by simp [tAtS, atS, S.putLink, S.putFork, S.fork?, S.tl?, mergeOf, hh, ho]⟩
    · simp [atS, S.link?, hh, ho] at ha

/-- **The premises.** -/
structure FallGood (p : Where) (g : S → Except String (List Claim × S)) (s : S) (n : Nat)
    (merge : Option Nat) (d : Nat) (P : Nat → Polynomial Cb.Gl.E) : Prop where
  slots : SlotsGood Reading.gl n merge d P (fun x => (gathered p g s x).isSome = true)
    (fun x => ((gathered p g s x).map (·.2.1.F)).getD {})
    (fun x => ((gathered p g s x).map (·.2.2)).getD [])
  merge : ∀ x y, gathered p g s x = some y → mergeOf y.1 = merge

/-- **Few values of chi make K9's share of the fall's test speak.** -/
theorem batFall_few (p : Where) (g : S → Except String (List Claim × S)) (s : S) (n : Nat)
    (merge : Option Nat) (d : Nat) (P : Nat → Polynomial Cb.Gl.E)
    (h : FallGood p g s n merge d P) :
    Prob.cnt (fun y : Cb.Gl.E => ∃ x : E, Reading.gl.val x = y ∧
      (batFallTest (batch atS p g) n (fun _ _ => none) (fun _ => none) s [drawnOne x]).isSome
        = true) ≤ n * d := by
  refine le_trans (Prob.cnt_mono fun y hy => ?_) (freeSlot_few Reading.gl n merge d P _ _ _ h.slots)
  obtain ⟨x, rfl, hx⟩ := hy
  have hx' : ((behindBat (batch atS p g) s [drawnOne x]).bind fun s₁ =>
      (freeSlotShare n s₁).or none).isSome = true := hx
  cases hb : behindBat (batch atS p g) s [drawnOne x] with
  | none => rw [hb] at hx'; exact nomatch hx'
  | some s₁ =>
    rw [hb] at hx'
    have hd : (batch atS p g).decide s [⟨[], drawnOne x⟩] [] = .ok s₁ := by
      have hb' : ((batch atS p g).decide s [⟨[], drawnOne x⟩] []).toOption = some s₁ := hb
      cases hq : (batch atS p g).decide s [⟨[], drawnOne x⟩] [] with
      | error m => rw [hq] at hb'; exact nomatch hb'
      | ok t => rw [hq] at hb'; exact congrArg Except.ok (Option.some.inj hb')
    obtain ⟨e, a, cls, G, hg, hG, rfl⟩ := batch_split p g s s₁ x hd
    have ha : atS.get? e = some a := by
      unfold gathered at hg
      split at hg
      · split at hg
        · rename_i y _
          cases hq : atS.get? y.2 with
          | none => rw [hq] at hg; exact nomatch hg
          | some b =>
            rw [hq] at hg
            have e1 := Option.some.inj hg
            have e2 : y.2 = e := congrArg (·.1) e1
            have e3 : b = a := congrArg (·.2.1) e1
            rw [← e2, hq, e3]
        · exact nomatch hg
      · exact nomatch hg
    obtain ⟨tl, ht⟩ := tests_behind e a ha G
    have hf : freeSlotOk n merge G = false := by
      have hx'' : ((freeSlotShare n (atS.set e { a with F := G })).or none).isSome = true := hx'
      have h1 : (freeSlotShare n (atS.set e { a with F := G })).isSome = true := by
        cases hq : freeSlotShare n (atS.set e { a with F := G }) with
        | none => rw [hq] at hx''; exact nomatch hx''
        | some _ => rfl
      unfold freeSlotShare slotsFree at h1
      rw [ht, h.merge x _ hg] at h1
      have h2 : (if freeSlotOk n merge G = true then (none : Option String)
          else some "K9.free-slot").isSome = true := h1
      cases hq : freeSlotOk n merge G with
      | false => rfl
      | true => rw [hq] at h2; exact nomatch h2
    exact ⟨x, G, rfl, by rw [hg]; rfl, by rw [hg]; exact hG, hf⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batch_split
#print axioms ProofFile.Honest.K9.tests_behind
#print axioms ProofFile.Honest.K9.batFall_few
#print axioms ProofFile.Honest.K9.drawnOne
#print axioms ProofFile.Honest.K9.gathered
#print axioms ProofFile.Honest.K9.bind_ok
#print axioms ProofFile.Honest.K9.FallGood
