-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK5.lean: the closing of a segment (K10): an attention segment's own block
(kind K5, Johnson/Desc/First/Att/SeatN.lean: k5AtN) does alike at two states of the first chain that are one once
wiped. One structure of type Prop; the rest are theorems.

Words. wipeS sets to zero the targets of the rows that a state of the first chain holds (Honest/K10/WipeS.lean says
which). Two states are one under w where w s = w s'. A reader does not see w where it returns at w s what it returns
at s. A writer goes through w where it returns at w s the image under w of what it returns at s. Two outcomes are
alike where both refuse with the same word, or both return and the values are one under w (AlikeE, Wipe/Alike.lean). A
block does alike (Whole2 w) where its decide, each of its runs of claims and each of its runs behind the batching have
like outcomes at two states that are one under w; the claims of a run are then equal.

What is proved.
  K5Blind w L     what is asked of the seat L of K5's hearing: its two readers do not see w; its laying goes through w
  decide5_2, k5_whole2   K5Blind w L ⊢ the kind's decide does alike; with runs of claims that do alike, so does its
                  block; at any type of state
  firstK2, keysK2, secondK2, runsK2   SeatCBlind w L (Wipe/KeepK3.lean) ⊢ each of the kind's three named runs returns
                  equal forms and like states at two states that are one under w, at any type of state
  seatSO_blind    K5Blind wipeS seatSO
  runsO2, runN2   FnCl2 wipeS of the four runs at the first chain's state, "join" among them; and of a run of forms
                  taken as a run of claims
  **k5_keeps**      k5AtN W l g before = some b ⊢ Whole2 wipeS b: the field k5 of SeatKeeps2 (Wipe/Lots2.lean)

By what. The decide: what the seat's readers return at s is rewritten to what they return at s'; then the two texts
make the same calls, one after the other (AlikeE.head'); the last line is the seat's laying, under a name. The three
runs read the state through inOf and keysOfK alone, which do not see w (Wipe/KeepK3.lean), and hand the state back as it
is. "join" is the lookup's run (Wipe/KeepK3.lean: joinRun2). The hearing and the runs' formulas are not opened. k5_keeps
follows k5AtN_quiet of Johnson/Goal/Meaning/RecSeated.lean.

Limits. Nothing is said of what the hearing or the formulas compute. No property of the protocol is claimed: nothing
is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK3
import Johnson.Desc.First.Att.SeatN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First

/-! ## 1 The kind at any type of state -/

section letter
variable {T Cl : Type} {w : T → T}

/-- What is asked of the seat of K5's hearing: the readers do not see w; the laying goes through w. -/
structure K5Blind (w : T → T) (L : Att.P.Seat T) : Prop where
  ledger : ∀ s, L.ledger (w s) = L.ledger s
  owed : ∀ s, L.owed (w s) = L.owed s
  lay : ∀ s h G, L.lay (w s) h G = (L.lay s h G).map w

/-- K5's decide has like outcomes at two states that are one under w. -/
theorem decide5_2 {L : Att.P.Seat T} (h : K5Blind w L) (p : Att.P.Par) {s s' : T} (hs : w s = w s')
    (rs : List Fmt.RoundView) : AlikeE w (Att.P.decide L p s rs) (Att.P.decide L p s' rs) := by
  unfold Att.P.decide
  rw [blind2 (f := L.owed) h.owed hs, blind2 (f := L.ledger) h.ledger hs]
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun F => ?_
  refine AlikeE.head' fun y => ?_
  obtain ⟨hd, G, rest, k⟩ := y
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.named_alone ?_
  rw [← h.lay s, ← h.lay s', hs]

/-- **K5's block does alike** at a seat whose readers do not see w and whose laying goes through w, and at runs of
claims that do alike. -/
theorem k5_whole2 {L : Att.P.Seat T} (h : K5Blind w L)
    (claims : List (String × (Nat → T → Except String (List Cl × T))))
    (hc : ∀ c ∈ claims, ∀ n, FnCl2 w (c.2 n)) (p : Att.P.Par) : Whole2 w (Att.P.attentionKind L claims p) :=
  ⟨fun _ _ rs _ _ hs _ => decide5_2 h p hs rs, hc, (fun _ hx => nomatch hx)⟩

variable {L : Att.P.SeatC T}

/-- The run "first" returns nothing at both of two states that are one under w, or equal forms and like states. -/
theorem firstK2 (h : SeatCBlind w L) (c : Att.P.ParC) {s s' : T} (hs : w s = w s') :
    (Att.P.firstK L c s).map (wCl w) = (Att.P.firstK L c s').map (wCl w) := by
  unfold Att.P.firstK
  rw [blind2 (f := Att.P.inOf L c) (inOf_blind h c) hs]
  cases Att.P.inOf L c s' with
  | none => rfl
  | some x =>
    obtain ⟨i, K⟩ := x
    show ((Att.P.Runs.firstRun i K).bind fun y => some (y.1, s)).map (wCl w) =
      ((Att.P.Runs.firstRun i K).bind fun y => some (y.1, s')).map (wCl w)
    cases Att.P.Runs.firstRun i K with
    | none => rfl
    | some y => exact congrArg some (wCl_eq hs)

/-- The run "keys" returns nothing at both, or no form and like states. -/
theorem keysK2 (h : SeatCBlind w L) (c : Att.P.ParC) {s s' : T} (hs : w s = w s') :
    (Att.P.keysK L c s).map (wCl w) = (Att.P.keysK L c s').map (wCl w) := by
  unfold Att.P.keysK
  rw [blind2 (f := Att.P.keysOfK L c) (keysOfK_blind h c) hs]
  cases Att.P.keysOfK L c s' with
  | none => rfl
  | some y => exact congrArg some (wCl_eq hs)

/-- The run "second" returns nothing at both, or equal forms and like states. -/
theorem secondK2 (h : SeatCBlind w L) (c : Att.P.ParC) {s s' : T} (hs : w s = w s') :
    (Att.P.secondK L c s).map (wCl w) = (Att.P.secondK L c s').map (wCl w) := by
  unfold Att.P.secondK
  rw [blind2 (f := Att.P.inOf L c) (inOf_blind h c) hs]
  cases Att.P.inOf L c s' with
  | none => rfl
  | some x =>
    obtain ⟨i, K⟩ := x
    show ((Att.P.Runs.secondRun i K).bind fun y => some (y, s)).map (wCl w) =
      ((Att.P.Runs.secondRun i K).bind fun y => some (y, s')).map (wCl w)
    cases Att.P.Runs.secondRun i K with
    | none => rfl
    | some y => exact congrArg some (wCl_eq hs)

/-- **Each of K5's three named runs returns equal forms and like states, or refuses with one word.** -/
theorem runsK2 (h : SeatCBlind w L) (c : Att.P.ParC) : ∀ x ∈ Att.P.runsK L c, ∀ n, FnCl2 w (x.2 n) := by
  intro x hx n s s' hs
  rcases List.mem_cons.1 hx with rfl | hx
  · exact AlikeE.named_alone (firstK2 h c hs)
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact AlikeE.named_alone (keysK2 h c hs)
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact AlikeE.named_alone (secondK2 h c hs)
      · cases hx

end letter

/-! ## 2 At the first chain's state -/

/-- The seat of K5's hearing at the first chain's state: its readers do not see the wiping; its laying goes through
it. -/
theorem seatSO_blind : K5Blind wipeS Att.P.seatSO where
  ledger s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl
  owed _ := rfl
  lay s h G := by
    rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | ⟨_, _, _, _ | _, _, _, _, _, _, _, _ | _⟩ |
      _ | _ | _, _⟩ <;> rfl

/-- Each of K5's four named runs at the first chain's state returns equal forms and like states. -/
theorem runsO2 (A : Attention.Plan) : ∀ x ∈ Att.P.runsO A, ∀ n, FnCl2 wipeS (x.2 n) := by
  intro x hx n
  unfold Att.P.runsO at hx
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK2 (seatCO_blind _) _ _ hr n
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact joinRun2 (seatCalls_blind id) (keysOfO_blind A) n
      · cases hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK2 (seatCO_blind _) _ _ hr n
    · cases hx

/-- A run of forms that does so still does when its forms are taken as claims. -/
theorem runN2 {r : Nat → S → Except String (List Aff × S)} {n : Nat} (h : FnCl2 wipeS (r n)) :
    FnCl2 wipeS (Att.P.runN r n) := by
  intro s s' hs
  unfold Att.P.runN
  refine AlikeE.map (h s s' hs) fun y y' hy => ?_
  show (y.1.map Att.P.claimOf, wipeS y.2) = (y'.1.map Att.P.claimOf, wipeS y'.2)
  rw [(Prod.mk.inj hy).1, (Prod.mk.inj hy).2]

/-- **Kind K5's block does alike at two states that are one once wiped.** -/
theorem k5_keeps (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) {b : Block S Claim}
    (h : Att.P.k5AtN W l g before = some b) : Whole2 wipeS b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_same2 (k5_whole2 seatSO_blind (Att.P.runsN p) (fun c hc n => ?_) _) rfl (fun _ hx => hx) rfl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  exact runN2 (runsO2 p r hr n)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.K5Blind
#print axioms ProofFile.Honest.K10.decide5_2
#print axioms ProofFile.Honest.K10.k5_whole2
#print axioms ProofFile.Honest.K10.firstK2
#print axioms ProofFile.Honest.K10.keysK2
#print axioms ProofFile.Honest.K10.secondK2
#print axioms ProofFile.Honest.K10.runsK2
#print axioms ProofFile.Honest.K10.seatSO_blind
#print axioms ProofFile.Honest.K10.runsO2
#print axioms ProofFile.Honest.K10.runN2
#print axioms ProofFile.Honest.K10.k5_keeps
