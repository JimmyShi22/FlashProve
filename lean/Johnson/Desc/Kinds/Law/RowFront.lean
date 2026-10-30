-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowFront.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS WITH WHAT IT CLOSES SAID AT THE RECORD IN FRONT OF THE BLOCK, as the table's rows ask ("what the block closes holds
in front if what it opens holds behind"): STATED AND PROVED, general in the seat, and of the block as it rides (Head.blockOf W l).
OPENED, AT THE RECORD BEHIND (s'): Opened (Law/RowAtDecide.lean: the 35 forms of the block's three runs worth 0; the claim on the weights true) and JoinOpened
(Law/RowJoin.lean: the form of "join" at the head's key vectors worth 0).
CLOSED, AT THE RECORD IN FRONT (s): FrontIdn (at every position's corner the row's 17 forms are 0; the two plain sums: the part "idn" of the relation on cells) ·
FrontRider (the two guests' corner values, summed under the weights of zt, are 0) · KeysWorth (Law/RowJoin.lean) AT s: the lookup's own formula, fed with the
extensions of the calls' tables at their key points, is worth 0 IN THE WORLD OF THE LEDGER IN FRONT.
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE YET; whoever
may pick mask behind the draws makes every hidden scalar what they like. At parOf, before := []: the block's own test that the messages with the cells precede its first draw is idle at this seat. rs IS WHAT decide IS SHOWN (no sealed digest): that these are the rounds of the written reading is another file's equation (Johnson/Desc/Sound/ShownRounds.lean).
All that Law/RowRides.lean and Law/RowJoin.lean do not say. gk (what the lookup has heard) IS A LETTER, tied to the record by nothing here; CEndFilled
(each number that gk's last claim names is filled in the ledger in front) IS A PREMISE: the lookup's files' to pay. That joinForm at constants is the library's
claimJoin: the lookups' tie. "planes" is no part of it.
  vW_later        a form all of whose numbers are filled in a ledger is worth the same at every later ledger.
  joinFold_worlds · joinForm_worlds   the lookup's formula at constants hangs on the world through gk's last claim alone.
  decide_frames   where the decision goes on: the same letters, the same points of the lookup, a later ledger.
  RowFrontStatement · rowFront · RowFrontRidesStatement · rowFrontRides

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowRides
import Johnson.Desc.Kinds.Law.RowJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork Reading World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)

variable {S : Type}

/-- The part "idn" of the relation on cells, at the letters that given returns at a record. -/
def FrontIdn (p : Par) (L : Seat S) (s : S) (c : NCells) : Prop :=
  ∃ g : Given, given p L s = .ok g ∧ (∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0) ∧
    meanAt c.toCells = 0 ∧ countAt c.toCells = 0

/-- The two guests' corner values, summed under the weights of the lookup's point on the positions, are 0. -/
def FrontRider (p : Par) (L : Seat S) (s : S) (c : NCells) : Prop :=
  ∃ g : Given, given p L s = .ok g ∧
    (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) = 0 ∧
    (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t)) = 0

/-- Each number that the lookup's last claim names is filled in the ledger. -/
def CEndFilled (gk : OnBytes.Model.Forest.Heard) (F : Fork) : Prop :=
  ∀ x, x ∈ gk.cEnd.slots.toList → OnBytes.PscRun.Filled F x.1

/-- **K6's ROW, WHAT IT CLOSES SAID IN FRONT.** -/
def RowFrontStatement : Prop :=
  ∀ (S Cl : Type) (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par) (s : S)
    (c : NCells) (mask : Nat → E) (gk : OnBytes.Model.Forest.Heard) (s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    (kind cl L link piece p).decide s rs gs = .ok s' → SeatBack p L s → WellLaid (L.ledger s) →
    p.ok = true → hasFeatures p → p.okStart (L.request s) = true →
    (∀ y, Reply.token L.toSeat s = some y → y < p.sizes.V) →
    Canonical rs → Sound.NoBad (ruleK6T p L s c mask) rs → CEndFilled gk (L.ledger s) →
    Opened p L s' c mask → JoinOpened p L s' c mask gk →
    FrontIdn p L s c ∧ FrontRider p L s c ∧ KeysWorth p L s c mask gk

/-- **THE SAME OF THE BLOCK AS IT RIDES.** -/
def RowFrontRidesStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block First.S Unit), blockOf W l = some b →
    ∀ (s : First.S) (c : NCells) (mask : Nat → E) (gk : OnBytes.Model.Forest.Heard) (s' : First.S)
      (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    b.decide s rs gs = .ok s' → WellLaid ((seatAt W.hS (readsOf W)).ledger s) →
    (parOf W.hS (workOf W)).ok = true → hasFeatures (parOf W.hS (workOf W)) →
    (parOf W.hS (workOf W)).okStart ((seatAt W.hS (readsOf W)).request s) = true →
    (∀ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y →
      y < (parOf W.hS (workOf W)).sizes.V) →
    Canonical rs → Sound.NoBad (ruleK6T (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c mask) rs →
    CEndFilled gk ((seatAt W.hS (readsOf W)).ledger s) →
    Opened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask →
    JoinOpened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask gk →
    FrontIdn (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c ∧
      FrontRider (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c ∧
      KeysWorth (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c mask gk

namespace Came

/-- A form all of whose numbers are filled in a ledger is worth the same at every later ledger. -/
theorem vW_later {F G : Fork} (mask : Nat → E) (ent : Nat → Nat → Nat → E) (f : Form)
    (hL : Later F G) (hf : ∀ x, x ∈ f.slots.toList → OnBytes.PscRun.Filled F x.1) :
    vW (worldE G mask ent) f = vW (worldE F mask ent) f := by
  unfold vW Aff.value
  have e1 : f.ents.toList.map (OnBytes.Model.Ent.value Reading.gl (worldE G mask ent))
      = f.ents.toList.map (OnBytes.Model.Ent.value Reading.gl (worldE F mask ent)) :=
    List.map_congr_left fun x _ => by simp only [OnBytes.Model.Ent.value, worldE]
  have e2 : f.slots.toList.map (OnBytes.Model.slotValue Reading.gl (worldE G mask ent))
      = f.slots.toList.map (OnBytes.Model.slotValue Reading.gl (worldE F mask ent)) :=
    List.map_congr_left fun x hx => by
      simp only [OnBytes.Model.slotValue, worldE]
      rw [hidden_later mask hL (hf x hx)]
  rw [e1, e2]

section Value
variable {K' : Type} [CommRing K'] (ρ : Reading K') (W W' : World K')

theorem joinFold_worlds (g : OnBytes.Model.Forest.Heard) (KF : Array Aff) : ∀ (l : List Nat) (f f' : Aff),
    f.value ρ W = f'.value ρ W' →
    (∀ c, c ∈ l → (KF.getD c (Aff.ofConst zeroE)).value ρ W
      = (KF.getD c (Aff.ofConst zeroE)).value ρ W') →
    (l.foldl (joinStep g KF) f).value ρ W = (l.foldl (joinStep g KF) f').value ρ W'
  | [], _, _, h, _ => h
  | c :: l, f, f', h, hk => by
    simp only [List.foldl_cons]
    refine joinFold_worlds g KF l _ _ ?_ fun c' hc' => hk c' (List.mem_cons_of_mem _ hc')
    unfold joinStep
    rw [Aff.value_addMul, Aff.value_addMul, Aff.value_sub, Aff.value_sub, Aff.value_ofConst,
      Aff.value_ofConst, h, hk c (List.mem_cons_self)]

/-- The formula hangs on the world through the fed forms' values and the lookup's last claim's alone. -/
theorem joinForm_worlds (g : OnBytes.Model.Forest.Heard) (KF : Array Aff)
    (hk : ∀ c, c < KF.size → (KF.getD c (Aff.ofConst zeroE)).value ρ W
      = (KF.getD c (Aff.ofConst zeroE)).value ρ W')
    (hc : g.cEnd.value ρ W = g.cEnd.value ρ W') :
    (joinForm g KF).value ρ W = (joinForm g KF).value ρ W' := by
  unfold joinForm
  rw [Aff.value_sub, Aff.value_sub, Aff.value_add, Aff.value_add, Aff.value_ofConst,
    Aff.value_ofConst, hc,
    joinFold_worlds ρ W W' g KF (List.range KF.size) _ _
      (by rw [Aff.value_ofConst, Aff.value_ofConst]) fun c hc' => hk c (List.mem_range.1 hc')]

end Value

/-- **Where the decision goes on**: the same letters, the same points of the lookup, a later ledger. -/
theorem decide_frames {Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (kind cl L link piece p).decide s rs gs = .ok s') (hback : SeatBack p L s)
    (hWL : WellLaid (L.ledger s)) (hcan : Canonical rs) :
    given p L s' = given p L s ∧ L.lookup s' = L.lookup s ∧ Later (L.ledger s) (L.ledger s') := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) p L s rs
      = .ok s' := hd
  obtain ⟨g, H, F1, w, s1, s2, hg, hh, e1, e2, rfl⟩ := decide_hears hd'
  obtain ⟨bL, _, bG, bZ⟩ := hback g rs [] F1 H w s1 s2 hg hWL hcan hh e1 e2
  refine ⟨bG, bZ, ?_⟩
  rw [bL]
  exact keeps_hear _ _ _ _ _ hh

/-- The keys' sentence rides from a record to an earlier one. -/
theorem keys_front (p : Par) (L : Seat S) (s s' : S) (c : NCells) (mask : Nat → E)
    (gk : OnBytes.Model.Forest.Heard) (hG : given p L s' = given p L s)
    (hZ : L.lookup s' = L.lookup s) (hL : Later (L.ledger s) (L.ledger s'))
    (hf : CEndFilled gk (L.ledger s)) (h : KeysWorth p L s' c mask gk) :
    KeysWorth p L s c mask gk := by
  obtain ⟨g, z, hg, hz, hv⟩ := h
  refine ⟨g, z, hG ▸ hg, hZ ▸ hz, ?_⟩
  rw [← hv]
  refine joinForm_worlds Reading.gl _ _ gk _ (fun call hc => ?_)
    (vW_later mask noEnt gk.cEnd hL hf).symm
  have hc6 : call < 6 := by simpa [trueKeys] using hc
  rw [trueKeys_getD g z.2 c call hc6, Aff.value_ofConst, Aff.value_ofConst]

theorem rowFront : RowFrontStatement := by
  intro S Cl cl L link piece p s c mask gk s' rs gs hd hback hWL hplan hd0 hreq hy hcan hnb hfill
    hopen hjoin
  obtain ⟨hG, hZ, hL⟩ := decide_frames cl L link piece p hd hback hWL hcan
  obtain ⟨⟨g, hg, hrows⟩, hcl⟩ :=
    rowPrice S Cl cl L link piece p s c mask s' rs gs hd hback hWL hplan hd0 hreq hy hcan hnb hopen
  have hkw := keys_front p L s s' c mask gk hG hZ hL hfill (keys_worth p L s' c mask gk hcl hjoin)
  obtain ⟨g', H, z, hg', _, _, hC⟩ := hcl
  rw [hg] at hg'
  obtain rfl : g = g' := Except.ok.inj hg'
  exact ⟨⟨g, hG ▸ hg, hrows, hC.1.1, hC.1.2⟩, ⟨g, hG ▸ hg, hC.2.2.1, hC.2.2.2⟩, hkw⟩

theorem rowFrontRides : RowFrontRidesStatement := by
  intro W l b hb s c mask gk s' rs gs hd
  unfold blockOf at hb
  cases hU : W.H.tl.ix.U.getD 2 none with
  | none =>
    rw [hU] at hb
    simp at hb
  | some i =>
    rw [hU] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    have e : readsOf W = i := by
      unfold readsOf
      rw [hU]
      rfl
    rw [e]
    intro hWL
    exact rowFront First.S Unit (fun _ => ()) (seatAt W.hS i) l 4 (parOf W.hS (workOf W)) s c mask gk s' rs gs hd ((seatBack_iff _ _ _).2 (seatBack_at W.hS i (workOf W) s)) hWL

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.decide_frames
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowFront
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowFrontRides
