-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PileMasks.lean: WHO EARNS AND WHO KEEPS "K13.pileMasks" (every row on the table
names mask entries of the index masks' message alone: `pileMasksC`, Johnson/Desc/K13/PubK13.lean) AT
THREE BLOCKS OF OURS. Statements with their proofs.
  `atM3_pileMasks`: **kind K13's block EARNS it**: behind a yes the one row names that message
    alone, WHATEVER STOOD IN FRONT: the block's own front tests the pile's rows, and the
    batching's row is made of their mask entries and of entries that it takes of that message.
  `atM4_pileMasks`: W's commitment keeps it: the rows on the table and the record's number stay.
  `openingZero_pileMasks`: the first segment's opening keeps it WHERE NO ROW IS PENDING: that block
    LAYS the record's number of the index masks' message.
  `rider3_pileMasks`, `rider4_pileMasks`, `riderG_pileMasks`: the item is a rider at the three
    blocks (Johnson/Desc/K13/Law/FillFromSentences.lean, FillGFromSentences.lean).
What is not claimed. That any other block of the chain keeps it: whoever lays a pending row earns it
anew; whoever leaves the rows on the table and the record's number keeps it. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillGFromSentences
import Johnson.Desc.K13.Law.Good2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)

section
variable {Pp W Cl : Type}

/-- **Kind K13's block earns it.** -/
theorem atM3_pileMasks {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    pileMasksC s' = true := by
  obtain ⟨out, hb, _, hr⟩ := atM3_ok h
  obtain ⟨r, rs', x, t, hd, o, _, _, hfit, _, _, _, _, hrun, _, rfl⟩ := batt_ok hb
  obtain ⟨_, _, _, _, e⟩ := atM3_rec h
  have ho : s'.out = s.out := by rw [e]
  refine (pileMasksC_iff s').2 fun r' hr' => ?_
  rw [hr] at hr'
  obtain rfl := List.mem_singleton.1 hr'
  rw [ho]
  exact rowOf_onLedger hfit (atM3_ledger h) hrun

/-- W's commitment keeps it. -/
theorem atM4_pileMasks {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s')
    (h0 : pileMasksC s = true) : pileMasksC s' = true := by
  obtain ⟨_, _, _, ho, hrows⟩ := atM4_rec h
  unfold pileMasksC at h0 ⊢
  rw [hrows, ho]
  exact h0

/-- The first segment's opening keeps it where no row is pending. -/
theorem openingZero_pileMasks {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (h0 : s.out.pending.isEmpty = true) : pileMasksC t = true := by
  obtain ⟨hstand, _, _, _, _, ho, _⟩ := K1.openingZero_rec h
  have hp : t.out.pending = [] := by
    rw [ho]
    exact List.isEmpty_iff.1 h0
  have hr : t.rows = [] := by
    unfold S.rows
    cases hh : t.here with
    | mem a => simp [First.standOf, hh] at hstand
    | _ => exact hp
  unfold pileMasksC
  rw [hr]
  rfl

/-! ## The item is a rider at the three blocks -/

theorem rider3_pileMasks {P : Where} {Mg : Meaning Pp W}
    (hM : ∀ x, Mg.pub pileMasksItem x = pileMasksC x.2) (hP : ∀ x, Mg.pubP pileMasksItem x) :
    Rider3 Cl P Mg pileMasksItem := fun x x' h => by
  obtain ⟨rs, gs, hd⟩ := h.2
  exact ⟨fun _ => by rw [hM]; exact atM3_pileMasks hd, fun _ => hP x'⟩

theorem rider4_pileMasks {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W}
    {Q : List Pub} {p : Option Place} (hm : pileMasksItem ∈ Q)
    (hM : ∀ x, Mg.pub pileMasksItem x = pileMasksC x.2) (hP : ∀ x, Mg.pubP pileMasksItem x) :
    Rider4 Cl P P' N Mg Q p pileMasksItem := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hM] at h0
  exact ⟨by rw [hM]; exact atM4_pileMasks hd h0, fun _ => hP x'⟩

theorem riderG_pileMasks {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub}
    {p : Option Place} (hm : Pub.noneSent ∈ Q)
    (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2)
    (hM : ∀ x, Mg.pub pileMasksItem x = pileMasksC x.2) (hP : ∀ x, Mg.pubP pileMasksItem x) :
    RiderG Cl q gp nm X fvs kCol N Mg Q p pileMasksItem := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hNS, noneSentC_eq, Bool.and_eq_true] at h0
  exact ⟨by rw [hM]; exact openingZero_pileMasks hd h0.2, fun _ => hP x'⟩

end

end VerifiableInference.Desc.K13.Law
