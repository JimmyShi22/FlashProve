-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscLater.lean: what lies under a slot that is filled stays there: each of six
routines of the sub-proofs' masked sumcheck (OnBytes/Model/Psc.lean) leads to a later state.

Definitions, and theorems with their proofs. A form names a hidden value by its slot, and what lies
under the slot is read at the end (`Fork.worldOf`, OnBytes/Model/HideLaws.lean). So a fact on a
form's value that is stated at one state of a sub-proof must last to the last state.

Main names:
  `Later F G`: G has as many slots as F and has taken no fewer; if F's three arrays have one entry
    for each slot, so have G's; every slot that is filled in F is filled in G and holds the same
    shown value and the same factor.
  `Later.refl`, `Later.trans`; `took_later`, `hideRun_later`, `owe_later`, `paid_later`: the steps.
  `pscBeginAt_later`, `pscBegin_later`, `pscRound_later`, `roundIn_later`, `pscEnds_later`,
    `pscRow_later`: a run of each routine that returns, from a state whose arrays have their size,
    leads to a later state.
  `hide_keeps`, `hideRun_keeps`, `pscEnds_keeps`, `pscRow_keeps`: the same without the premise on
    the sizes.
  `SlotsSame F G`: G has F's slots and what lies under them; `SlotsSame.later`. `lin_slots`,
    `lin_later`, `linsLoop_slots`, `kap_slots`, `push_slots`, `batchBy_slots`, `rootTaken_slots`:
    adding a claim, drawing the batching element and noting a commitment leave the slots.
  `FirstPass F G`: G differs from F at most in the next slot, in what lies under the slots and in
    the list of owed claims; `FirstPass.refl`, `FirstPass.trans`, and a law for each step and
    routine of the pass that reads messages.
  `shown_iff`: what `Fork.shown` gives, and when. `shown_later`: it gives the same at every later
    state.
  `publicPart_later`: so does `Fork.publicPart`.

Limits: nothing is said where a routine fails. Nothing on the claims that are added, on soundness,
on an honest prover or on hiding.


-/
import OnBytes.Tie.Pv.Psc.PscFork

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model

/-- G is a later state than F: what lies under the slots that are filled in F is kept. -/
structure Later (F G : Fork) : Prop where
  next : F.next ≤ G.next
  ns : G.ns = F.ns
  sized : Sized F → Sized G
  keep : ∀ j, Filled F j → Filled G j ∧ G.vp.getD j zeroE = F.vp.getD j zeroE ∧
    G.mf.getD j zeroE = F.mf.getD j zeroE

/-- Every state is later than itself. -/
theorem Later.refl (F : Fork) : Later F F :=
  ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

/-- Later than a later state is later. -/
theorem Later.trans {F G H : Fork} (h : Later F G) (h' : Later G H) : Later F H :=
  ⟨Nat.le_trans h.next h'.next, h'.ns.trans h.ns, fun s => h'.sized (h.sized s), fun j hj => by
    obtain ⟨a1, a2, a3⟩ := h.keep j hj
    obtain ⟨b1, b2, b3⟩ := h'.keep j a1
    exact ⟨b1, b2.trans a2, b3.trans a3⟩⟩

/-- Taking slots. -/
theorem took_later (F : Fork) (n : Nat) : Later F (took F n) :=
  ⟨Nat.le_add_right _ _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

/-- Entering an owed claim. -/
theorem owe_later (F : Fork) (what : String) : Later F (F.owe what).2 :=
  ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

/-- Marking an owed claim as added. -/
theorem paid_later (F : Fork) (i : Nat) : Later F (F.paid i) :=
  ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

/-- Putting a run of values under slots. -/
theorem hideRun_later {F G : Fork} {first : Nat} {v : Array E} {factor : E} (hF : Sized F)
    (h : F.hideRun first v factor = some G) : Later F G := by
  obtain ⟨a1, a2, a3, a4⟩ := hideRun_ok F G first v factor hF h
  refine ⟨Nat.le_of_eq a1.next.symm, a1.ns, fun _ => a2, fun j hj => ?_⟩
  by_cases hin : first ≤ j ∧ j < first + v.size
  · exfalso
    have e : first + (j - first) = j := by omega
    have := (a3 (j - first) (by omega)).2.1
    rw [e] at this
    exact this hj
  · obtain ⟨b1, b2, b3⟩ := a4 j (by omega)
    exact ⟨b3.2 hj, b1, b2⟩

/-- The beginning, from a given target. -/
theorem pscBeginAt_later {target : E} {F G : Fork} {c c' : Ctx} {p : Psc}
    (h : pscBeginAt target F c = .ok ((p, G), c')) : Later F G := by
  obtain ⟨_, _, -, rfl, -⟩ := pscBeginAt_ok _ _ _ _ _ _ h
  exact took_later F 1

/-- The beginning. -/
theorem pscBegin_later {C : Aff} {F G : Fork} {c c' : Ctx} {p : Psc}
    (h : pscBegin C F c = .ok ((p, G), c')) : Later F G := by
  obtain ⟨_, _, _, -, -, rfl, -⟩ := pscBegin_ok _ _ _ _ _ _ h
  exact took_later F 1

/-- One round. -/
theorem pscRound_later {p : Psc} {w : OnBytes.Psc.Weight} {draw : Blk E} {F G : Fork} {c c' : Ctx}
    {r : E} {p' : Psc} (h : pscRound p w draw F c = .ok (((r, p'), G), c')) : Later F G := by
  obtain ⟨_, _, -, -, -, -, rfl, -⟩ := pscRound_ok _ _ _ _ _ _ _ _ _ h
  exact took_later F _

/-- One round of a given form. -/
theorem roundIn_later {form : RoundForm} {p : Psc} {z : E} {degree : Nat} {F G : Fork} {c c' : Ctx}
    {r : E} {p' : Psc} (h : roundIn form p z degree F c = .ok (((r, p'), G), c')) : Later F G := by
  obtain ⟨_, _, -, -, -, -, -, rfl, -⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h
  exact took_later F _

/-- The round in Y and the round of the end values. -/
theorem pscEnds_later {p : Psc} {degreeInY n : Nat} {F G : Fork} {c c' : Ctx} {e : Nat} {p' : Psc}
    (hF : Sized F) (h : pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) : Later F G := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, hG, -⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h
  exact (took_later F _).trans (hideRun_later (took_sized _ hF) hG)

/-- The claim that a sumcheck leaves. -/
theorem pscRow_later {p : Psc} {S0 : E} {kept : Aff} {F G : Fork} {c c' : Ctx} {row : Aff}
    {p' : Psc} (hF : Sized F) (h : pscRow p S0 kept F c = .ok (((row, p'), G), c')) :
    Later F G := by
  obtain ⟨-, -, -, -, -, hG, -, -⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h
  exact hideRun_later hF hG

/-! ## The same without a premise on the arrays' sizes -/

/-- One value put under a slot leads to a later state. -/
theorem hide_keeps {F G : Fork} {j : Nat} {y factor : E} (h : F.hide j y factor = some G) :
    Later F G := by
  unfold Fork.hide at h
  split at h
  · rename_i hq
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hq
    obtain rfl := Option.some.inj h
    refine ⟨Nat.le_refl _, rfl, fun s => ⟨by simp [s.1], by simp [s.2.1], by simp [s.2.2]⟩, ?_⟩
    intro i hi
    have hij : i ≠ j := by
      rintro rfl
      have hlt : i < F.gotF.size := by rw [hq.1.2]; exact hq.1.1
      have e : F.gotF.getD i false = F.gotF.getD i true := by
        simp [Array.getD_eq_getD_getElem?, hlt]
      unfold Filled at hi
      rw [e, hq.2] at hi
      exact absurd hi (by simp)
    refine ⟨?_, getD_set_other _ _ _ _ _ hij, getD_set_other _ _ _ _ _ hij⟩
    show (F.gotF.set! j true).getD i false = true
    rw [getD_set_other _ _ _ _ _ hij]
    exact hi
  · simp at h

/-- The steps of a run of values lead to a later state. -/
theorem hideSteps_keeps (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep factor) (first, F) = some x → Later F x.2
  | [], first, F, x, h => by
    have hx : (first, F) = x := by simpa using h
    subst hx
    exact Later.refl F
  | y :: l, first, F, x, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep factor (first, F) y with
    | none => simp [hq] at h
    | some s =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep factor) s = some x := by simpa using h
      simp only [Fork.hideStep] at hq
      cases hh : F.hide first y factor with
      | none => simp [hh] at hq
      | some H =>
        rw [hh] at hq
        obtain rfl : (first + 1, H) = s := by simpa using hq
        exact (hide_keeps hh).trans (hideSteps_keeps factor l _ _ _ h2)

/-- A run of values put under slots leads to a later state. -/
theorem hideRun_keeps {F G : Fork} {first : Nat} {v : Array E} {factor : E}
    (h : F.hideRun first v factor = some G) : Later F G := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact hideSteps_keeps factor _ _ _ _ hx
  · simp at h

/-- The round in Y and the round of the end values lead to a later state. -/
theorem pscEnds_keeps {p : Psc} {degreeInY n : Nat} {F G : Fork} {c c' : Ctx} {e : Nat} {p' : Psc}
    (h : pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) : Later F G := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, hG, -⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h
  exact (took_later F _).trans (hideRun_keeps hG)

/-- Making the claim that a sumcheck leaves leads to a later state. -/
theorem pscRow_keeps {p : Psc} {S0 : E} {kept : Aff} {F G : Fork} {c c' : Ctx} {row : Aff}
    {p' : Psc} (h : pscRow p S0 kept F c = .ok (((row, p'), G), c')) : Later F G := by
  obtain ⟨-, -, -, -, -, hG, -, -⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h
  exact hideRun_keeps hG

/-! ## Steps that leave what lies under the slots -/

/-- G has F's slots: their number, the next one, and the three arrays. -/
structure SlotsSame (F G : Fork) : Prop where
  ns : G.ns = F.ns
  next : G.next = F.next
  vp : G.vp = F.vp
  mf : G.mf = F.mf
  gotF : G.gotF = F.gotF

/-- Every state has its own slots. -/
theorem SlotsSame.refl (F : Fork) : SlotsSame F F := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `SlotsSame` goes through a state between. -/
theorem SlotsSame.trans {F G H : Fork} (h : SlotsSame F G) (h' : SlotsSame G H) : SlotsSame F H :=
  ⟨h'.ns.trans h.ns, h'.next.trans h.next, h'.vp.trans h.vp, h'.mf.trans h.mf,
    h'.gotF.trans h.gotF⟩

/-- A state with the same slots is a later state. -/
theorem SlotsSame.later {F G : Fork} (h : SlotsSame F G) : Later F G :=
  ⟨Nat.le_of_eq h.next.symm, h.ns, fun s => by
    unfold Sized at *
    rw [h.vp, h.mf, h.gotF, h.ns]
    exact s, fun j hj => by
    unfold Filled at *
    rw [h.vp, h.mf, h.gotF]
    exact ⟨hj, rfl, rfl⟩⟩

/-- Handing out the weight of a claim leaves the slots. -/
theorem kapTake_slots {F G : Fork} {c : Nat} {k : E} (h : F.kapTake c = some (k, G)) :
    SlotsSame F G := by
  unfold Fork.kapTake at h
  split at h
  · simp at h
  · split at h
    · cases hk : F.kapAt c with
      | none => simp [hk] at h
      | some k' =>
        simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact SlotsSame.refl F
    · split at h
      · cases hk : F.kapAt c with
        | none => simp [hk] at h
        | some k' =>
          simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · simp at h

/-- Handing out the weight of the next claim leaves the slots. -/
theorem kap_slots {F G : Fork} {k : E} (h : F.kap = some (k, G)) : SlotsSame F G := by
  unfold Fork.kap at h
  cases hk : F.kapTake F.nClaim with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k', H⟩ := x
    simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact (kapTake_slots hk).trans ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Adding a multiple of a form to the one equation leaves the slots. -/
theorem push_slots {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) : SlotsSame F G := by
  unfold Fork.push at h
  split at h
  · simp at h
  · simp only [] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp at h

/-- Adding a claim leaves what lies under the slots. -/
theorem lin_slots {F G : Fork} {f : Aff} (h : F.lin f = some G) : SlotsSame F G := by
  unfold Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k, H⟩ := x
    simp only [hk, Option.bind_some] at h
    exact (kap_slots hk).trans (push_slots h)

/-- Adding a claim leads to a later state. -/
theorem lin_later {F G : Fork} {f : Aff} (h : F.lin f = some G) : Later F G := (lin_slots h).later

/-- Adding a list of claims leaves the slots. -/
theorem linsLoop_slots : ∀ (l : List Aff) (F G : Fork), l.foldlM Fork.lin F = some G →
    SlotsSame F G
  | [], F, G, h => by
    obtain rfl : F = G := by simpa using h
    exact SlotsSame.refl F
  | a :: l, F, G, h => by
    rw [List.foldlM_cons] at h
    cases hq : F.lin a with
    | none => simp [hq] at h
    | some H =>
      rw [hq] at h
      exact (lin_slots hq).trans (linsLoop_slots l H G (by simpa using h))

/-- Taking the drawn batching element leaves the slots. -/
theorem batchBy_slots {F G : Fork} {x : E} (h : F.batchBy x = some G) : SlotsSame F G := by
  unfold Fork.batchBy at h
  split at h
  · simp at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Noting a commitment leaves the slots. -/
theorem rootTaken_slots (F : Fork) (t w : Nat) : SlotsSame F (F.rootTaken t w) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The pass that reads messages -/

/-- G differs from F at most in the next slot, in what lies under the slots, and in the list of owed
claims: so the arrays, the coefficients of the one equation, the number of claims and the batching
element are F's. -/
def FirstPass (F G : Fork) : Prop :=
  G = { F with next := G.next, vp := G.vp, mf := G.mf, gotF := G.gotF, owed := G.owed }

/-- Every state stands in the relation to itself. -/
theorem FirstPass.refl (F : Fork) : FirstPass F F := rfl

/-- `FirstPass` goes through a state between. -/
theorem FirstPass.trans {F G H : Fork} (h : FirstPass F G) (h' : FirstPass G H) :
    FirstPass F H := by
  unfold FirstPass at *
  rw [h', h]

/-- Taking slots. -/
theorem took_firstPass (F : Fork) (n : Nat) : FirstPass F (took F n) := rfl

/-- Entering an owed claim. -/
theorem owe_firstPass (F : Fork) (what : String) : FirstPass F (F.owe what).2 := rfl

/-- Marking an owed claim as added. -/
theorem paid_firstPass (F : Fork) (i : Nat) : FirstPass F (F.paid i) := rfl

/-- A state that differs at most in what lies under the slots. -/
theorem Same.firstPass {F G : Fork} (h : Same F G) : FirstPass F G := by
  unfold Same at h
  unfold FirstPass
  rw [h]

/-- Putting a run of values under slots. -/
theorem hideRun_firstPass {F G : Fork} {first : Nat} {v : Array E} {factor : E} (hF : Sized F)
    (h : F.hideRun first v factor = some G) : FirstPass F G :=
  (hideRun_ok F G first v factor hF h).1.firstPass

/-- The beginning. -/
theorem pscBegin_firstPass {C : Aff} {F G : Fork} {c c' : Ctx} {p : Psc}
    (h : pscBegin C F c = .ok ((p, G), c')) : FirstPass F G := by
  obtain ⟨_, _, _, -, -, rfl, -⟩ := pscBegin_ok _ _ _ _ _ _ h
  exact took_firstPass F 1

/-- One round of a given form. -/
theorem roundIn_firstPass {form : RoundForm} {p : Psc} {z : E} {degree : Nat} {F G : Fork}
    {c c' : Ctx} {r : E} {p' : Psc}
    (h : roundIn form p z degree F c = .ok (((r, p'), G), c')) : FirstPass F G := by
  obtain ⟨_, _, -, -, -, -, -, rfl, -⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h
  exact took_firstPass F _

/-- The round in Y and the round of the end values. -/
theorem pscEnds_firstPass {p : Psc} {degreeInY n : Nat} {F G : Fork} {c c' : Ctx} {e : Nat}
    {p' : Psc} (hF : Sized F) (h : pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) :
    FirstPass F G := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, hG, -⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h
  exact (took_firstPass F _).trans (hideRun_firstPass (took_sized _ hF) hG)

/-- The claim that a sumcheck leaves. -/
theorem pscRow_firstPass {p : Psc} {S0 : E} {kept : Aff} {F G : Fork} {c c' : Ctx} {row : Aff}
    {p' : Psc} (hF : Sized F) (h : pscRow p S0 kept F c = .ok (((row, p'), G), c')) :
    FirstPass F G := by
  obtain ⟨-, -, -, -, -, hG, -, -⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h
  exact hideRun_firstPass hF hG

/-- What `Fork.shown` gives, and when. -/
theorem shown_iff (F : Fork) (j : Nat) (y : E) :
    F.shown j = some y ↔ j < F.ns ∧ Filled F j ∧ y = F.vp.getD j zeroE := by
  unfold Fork.shown Filled
  constructor
  · intro h
    split at h
    · rename_i hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      exact ⟨hq.1, hq.2, (Option.some.inj h).symm⟩
    · simp at h
  · rintro ⟨h1, h2, rfl⟩
    simp [h1, h2]

/-- What was shown for a slot is the same at every later state. -/
theorem shown_later {F G : Fork} (h : Later F G) {j : Nat} {y : E} (hs : F.shown j = some y) :
    G.shown j = some y := by
  obtain ⟨h1, h2, rfl⟩ := (shown_iff F j y).1 hs
  obtain ⟨a1, a2, -⟩ := h.keep j h2
  exact (shown_iff G j _).2 ⟨by rw [h.ns]; exact h1, a1, a2.symm⟩

/-- The loop of `Fork.publicPart` gives the same at every later state. -/
theorem publicLoop_later {F G : Fork} (h : Later F G) : ∀ (l : List (Nat × E)) (v t : E),
    l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y)) v =
      some t →
    l.foldlM (fun (v : E) (x : Nat × E) => (G.shown x.1).map fun y => addE v (mulE x.2 y)) v =
      some t
  | [], v, t, hl => hl
  | x :: l, v, t, hl => by
    rw [List.foldlM_cons] at hl ⊢
    cases hs : F.shown x.1 with
    | none => simp [hs] at hl
    | some y =>
      rw [shown_later h hs]
      rw [hs] at hl
      exact publicLoop_later h l _ t hl

/-- The public part of a form is the same at every later state. -/
theorem publicPart_later {F G : Fork} (h : Later F G) {a : Aff} {t : E}
    (hp : F.publicPart a = some t) : G.publicPart a = some t := by
  unfold Fork.publicPart at hp ⊢
  rw [← Array.foldlM_toList] at hp ⊢
  exact publicLoop_later h _ _ _ hp

end OnBytes.PscRun

#print axioms OnBytes.PscRun.hideRun_later
#print axioms OnBytes.PscRun.pscEnds_later
#print axioms OnBytes.PscRun.pscRow_later
#print axioms OnBytes.PscRun.hideRun_keeps
#print axioms OnBytes.PscRun.lin_slots
#print axioms OnBytes.PscRun.shown_later
#print axioms OnBytes.PscRun.publicPart_later
