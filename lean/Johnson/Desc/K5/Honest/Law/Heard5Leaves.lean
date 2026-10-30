-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Heard5Leaves.lean: CONDITIONAL, on a yes of the block's decision (and, at
the lookup, on the maker's return): THE KINDS OF SUB-PROTOCOL THAT STAND BETWEEN THE OWN ROUNDS OF
AN ATTENTION SEGMENT AND THE SEGMENT's BATCHING LEAVE WHAT THESE ROUNDS HANDED ON: wherever such a
block's decision says yes, the reading `S.heard5?` (Johnson/Desc/First/State.lean) of the state
behind is that of the state in front (`Block.Leaves`, Johnson/Desc/Sound/FoldHeard.lean). NO TEST ON
THE PLAN IS ASKED. On the verifier's text alone, kind by kind; no description in it.

Why. The library has, of the same blocks, that they carry what was heard TOGETHER WITH a sized
ledger (`K5Law.CarK5`, Johnson/Desc/First/Att/Claims/WalkK5.lean, WalkK8.lean), and of the lookup on
the digits that the open attention segment's part is kept but for two fields
(`k3_digits_step_attStays`, `digits_step_heard5`, Johnson/Desc/First/Look/K3DigitsOwnStays.lean):
the last two under the premise that the block's test on the plan says yes. For the one reading
`S.heard5?` that premise is not needed: no decision of these kinds writes the field. Nearer kin in
the library: `digits_put_heard5` (Johnson/Top/H/K3StepsVia.lean): the laying at the lookup on the
digits, one way ("some stays some"), where `putDigits_heard5` here is an equation;
`via_digits_steps_heard5` there: the kind's block, again under its test on the plan.

How. The sending: its three writes (`commitAtS_slots`, Johnson/Desc/K1/KeepsSlots.lean;
`heard5_put`, Johnson/Desc/K1/Law/K5AtLater.lean). The sending of the reads with its quiet step:
`heard5_k1Quiet` (K5AtLater.lean) and `leavesAndThen` (Johnson/Desc/Sound/FoldHeardProofs.lean). The
smallness test's draw: `drawn_of_yes` (Johnson/Desc/First/K8/TieRides.lean). The lookup: its makers
are opened as Johnson/Desc/First/K8/LawWideK3.lean opens them for the readings of the smallness
test's part of the state (`theStated_leaves_tl`): the proofs here follow that file's, step for step,
at another reading.

Main names:
  `commitAtS_leaves5`, `k1Reads_leaves5`: the sending; the sending of the reads with its quiet step.
  `draw_leaves5`: the smallness test's draw.
  `heard5_mark`, `heard5_hearLook`, `putDigits_heard5`, `putCalls_heard5`, `decideVia_heard5`,
    `quietAt_heard5`, `theOwn_leaves5`, `theWhole_leaves5`: the lookup's parts.
  `theStated_leaves_heard5`: **every block that the lookup kind makes at an address.**

Limits. The blocks' DECISIONS alone: their runs of claims are not spoken of. One direction, from a
yes; no yes is shown. Nothing on the ledger.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K1.Law.K5AtLater
import Johnson.Desc.First.K8.LawWideK3
import Johnson.Desc.First.K8.TieRides
import Johnson.Desc.First.Att.Claims.WalkK5
import Johnson.Desc.Sound.FoldHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open K5Law (heard5_putFork heard5_putTl)

/-! ## The sending -/

/-- The sending's decision leaves the reading. -/
theorem commitAtS_leaves5 {Cl : Type} (P : K1.Par) (link moment : ℕ) (arrays : Option (List ℕ)) :
    (K1.commitAtS P link moment arrays : Block S Cl).Leaves S.heard5? := by
  intro s rs gs s' h
  obtain ⟨_, _, _, y, _, _, _, e, _⟩ := K1.commitAtS_slots h
  rw [e]
  exact K1.heard5_put s _ _ _

/-- The sending of the reads with the quiet step joined behind it. -/
theorem k1Reads_leaves5 (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) : (IM.k1Reads Z G l X pr reads).Leaves S.heard5? :=
  leavesAndThen S Unit _ S.heard5? _ _ _ (commitAtS_leaves5 _ _ _ _) (K1.heard5_k1Quiet G l X)

/-! ## The smallness test's draw -/

/-- The draw's decision leaves the reading. -/
theorem draw_leaves5 {Cl : Type} (p : K8.Par) :
    (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p).Leaves S.heard5? := by
  intro s rs gs s' h
  obtain ⟨tl, mm, f, _, rfl⟩ := K8.drawn_of_yes p s s' rs gs h
  exact heard5_putTl s _

/-! ## The lookup -/

/-- A mark leaves the reading. -/
theorem heard5_mark (s : S) (m : String) : (s.mark m).heard5? = s.heard5? := by
  unfold S.mark
  cases s.failed <;> rfl

/-- The hearing of the lookup on the calls leaves the reading: it lays two other fields of the open
segment's part, or marks. -/
theorem heard5_hearLook (s : S) (g : Forest.Heard) : (s.hearLook g).heard5? = s.heard5? := by
  unfold S.hearLook
  cases h : s.here with
  | lay a =>
    by_cases hl : a.lookHeard.isSome
    · simp only [hl, if_true]
      exact heard5_mark s _
    · simp [hl, S.heard5?, h]
  | att a =>
    by_cases hl : a.lookHeard.isSome
    · simp only [hl, if_true]
      exact heard5_mark s _
    · simp [hl, S.heard5?, h]
  | head a =>
    by_cases ho : a.opened
    · by_cases hl : a.lookHeard.isSome
      · simp only [ho, hl, Bool.not_true, Bool.false_eq_true, if_false, if_true]
        exact heard5_mark s _
      · simp [ho, hl, S.heard5?, h]
    · simp only [ho, Bool.not_false, if_true]
      exact heard5_mark s _
  | _ => exact heard5_mark s _

/-- The laying at the lookup on the digits. -/
theorem putDigits_heard5 {Cl : Type} (claim : Aff → Cl) (s : S) (h : Forest.Heard) (G : Fork) :
    ((K3.seatDigits claim).put s h G).heard5? = s.heard5? := by
  show (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some h }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test").heard5? = s.heard5?
  cases ht : s.tl? with
  | none => exact heard5_mark s _
  | some tl =>
    cases hf : s.fork? with
    | none => exact heard5_mark s _
    | some F =>
      show ((s.putTl _).putFork G).heard5? = s.heard5?
      rw [heard5_putFork, heard5_putTl]

/-- The laying at the lookup on the calls. -/
theorem putCalls_heard5 {Cl : Type} (claim : Aff → Cl) (s : S) (h : Forest.Heard) (G : Fork) :
    ((K3.seatCalls claim).put s h G).heard5? = s.heard5? := by
  show ((s.putFork G).hearLook h).heard5? = s.heard5?
  rw [heard5_hearLook, heard5_putFork]

/-- A yes of the kind's decision, at a seat whose laying leaves the reading. -/
theorem decideVia_heard5 {Cl : Type} (seat : K3.Seat S Cl)
    (hput : ∀ s h G, (seat.put s h G).heard5? = s.heard5?) (p : First.Look.P) (s s' : S)
    (rs : List Fmt.RoundView) (h : K3.Law.decideVia seat p s rs = .ok s') : s'.heard5? = s.heard5? := by
  unfold K3.Law.decideVia at h
  obtain ⟨F, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨x, _, h⟩ := bindOk h
  obtain rfl : seat.put s x.1 x.2 = s' := Except.ok.inj h
  exact hput s x.1 x.2

/-- The steps without a round that the kind joins behind. -/
theorem quietAt_heard5 (X : Verify.Public) (i : ℕ) (digits : Bool) (f : S → Except String S)
    (hf : K3.quietAt X i digits = some f) (s s' : S) (h : f s = .ok s') :
    s'.heard5? = s.heard5? := by
  have hD : ∀ used claims, K3.quietDigits used claims s = .ok s' → s'.heard5? = s.heard5? := by
    intro used claims h
    unfold K3.quietDigits at h
    obtain ⟨F, _, h⟩ := bindOk h
    obtain ⟨G, _, h⟩ := bindOk h
    obtain rfl : s.putFork G = s' := Except.ok.inj h
    exact heard5_putFork s G
  unfold K3.quietAt at hf
  dsimp only at hf
  generalize (if X.p4 then (2 : ℕ) else 1) = step at hf
  split at hf
  · split at hf
    · obtain rfl := Option.some.inj hf
      unfold K3.quietHead at h
      cases hh : s.here with
      | head a =>
        simp only [hh] at h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨c, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain rfl : { s with here := .head { a with claim := some c } } = s' := Except.ok.inj h
        simp [S.heard5?, hh]
      | _ => simp [hh] at h
    · exact nomatch hf
  · split at hf
    · split at hf
      · obtain ⟨hp, _, rfl⟩ := Option.map_eq_some_iff.1 hf
        exact hD _ _ h
      · obtain rfl := Option.some.inj hf
        unfold K3.quietLook at h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain ⟨_, _, h⟩ := bindOk h
        obtain rfl : s = s' := Except.ok.inj h
        rfl
    · split at hf
      · obtain ⟨a, _, rfl⟩ := Option.map_eq_some_iff.1 hf
        exact hD _ _ h
      · exact nomatch hf

section
variable {Cl : Type} {claim : Aff → Cl} {X : Verify.Public} {codes : Codes}
  {shape : Params.ReqShape} {a : Place}

/-- The kind's own block. Conditional: h: the maker returns. -/
theorem theOwn_leaves5 {runs : Bool} {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : b.Leaves S.heard5? := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨dg, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have hput : ∀ s h G,
          ((if dg then K3.seatDigits claim else K3.seatCalls claim).put s h G).heard5? =
            s.heard5? := by
        intro s y G
        cases dg
        · exact putCalls_heard5 claim s y G
        · exact putDigits_heard5 claim s y G
      intro s rs gs s' hd
      dsimp only at hd
      split at hd <;> exact decideVia_heard5 _ hput p s s' rs hd

/-- With the step without a round joined behind. Conditional: h: the maker returns. -/
theorem theWhole_leaves5 {runs : Bool} {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : b.Leaves S.heard5? := by
  unfold K3.theWhole at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 := theOwn_leaves5 hc
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact leavesAndThen S Cl _ S.heard5? _ c _ h0 fun s _ _ s' hd =>
      quietAt_heard5 X i _ f hq s s' hd
  · exact h0

/-- **Every block that the lookup kind makes at an address leaves what an attention segment's own
rounds handed on.** Conditional: h: the maker returns. No test on the plan. -/
theorem theStated_leaves_heard5 {readers : ℕ → Option (K3.Readers S)} {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : b.Leaves S.heard5? := by
  unfold K3.theStated at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have hk := theWhole_leaves5 hw
  split at h
  · obtain rfl := Option.some.inj h
    exact hk
  · split at h
    · obtain rfl := Option.some.inj h
      exact hk
    · split at h
      · obtain rfl := Option.some.inj h
        exact hk
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact hk

end

end H2K5.Honest

#print axioms H2K5.Honest.commitAtS_leaves5
#print axioms H2K5.Honest.k1Reads_leaves5
#print axioms H2K5.Honest.draw_leaves5
#print axioms H2K5.Honest.heard5_mark
#print axioms H2K5.Honest.heard5_hearLook
#print axioms H2K5.Honest.putDigits_heard5
#print axioms H2K5.Honest.putCalls_heard5
#print axioms H2K5.Honest.decideVia_heard5
#print axioms H2K5.Honest.quietAt_heard5
#print axioms H2K5.Honest.theOwn_leaves5
#print axioms H2K5.Honest.theWhole_leaves5
#print axioms H2K5.Honest.theStated_leaves_heard5
