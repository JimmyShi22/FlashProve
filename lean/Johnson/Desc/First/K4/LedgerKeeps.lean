-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/LedgerKeeps.lean: K4's BLOCK KEEPS THE LEDGER: wherever the block's `decide`
returns a state, the ledger in that state is later than the ledger in the state in front
(`OnBytes.PscRun.Later`). It is K4's share of «later across the seat» (the definition in
Johnson/Desc/Part/LedgerKeeps.lean): `LedgerKeeps ledger b := ∀ s rs gs s', b.decide s rs gs =
.ok s' → Later (ledger s) (ledger s')`. Statements and proofs.

`decide_later`: for the block at any seat L whose laying and reading of the ledger fit (`hL`: behind
the three layings of `decide` the ledger read is the ledger laid), with `ledger := L.fork`.
`seatOwn_fits`: the seat at the first chain's carried record has that, by the definitions.
`blockAtS_later`: at the carried record S: where `decide` returns, the chain stood in a layers'
link, stands in one still, and that link's ledger is later.

`front_later`, `back_later`: the block's two runs of claims keep the ledger too (with
`formsFrontWith_later`, `formsBack_later`; over `formsFrontWith_some`, `formsBack_some`,
OnBytes/Desc/First/K4/ClaimsLaws.lean). `addForms_later`: so does adding forms to the one equation.
`freeSlot_same`: the run behind the batching hands the state on as it is.

It joins `decide_ok` (Johnson/Desc/First/K4/BlockLaws.lean) and `hearFl_later`
(OnBytes/Desc/First/K4/HearGrows.lean). NO PREMISE ON THE ARRAYS' SIZES. Limits: a block that says
no to all has all this emptily: it is an invariant, and wants a returning half beside it. Nothing on
soundness or hiding.
-/
import Johnson.Desc.First.K4.BlockLaws
import OnBytes.Desc.First.K4.HearGrows
import Johnson.Desc.First.K4.AtS
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.First (S LayOwn)

/-- **K4's block keeps the ledger**, at a seat whose laying and reading of the ledger fit. -/
theorem decide_later {T : Type} (L : Seat T)
    (hL : ∀ (s : T) (F : Fork) (o : Own), L.fork (L.setOwed (L.setOwn (L.setFork s F) o) none) = F)
    {p : Par} {s s' : T} {rs : List Fmt.RoundView} {cols : List (List (Nat × List UInt64))}
    (h : (block L p).decide s rs cols = .ok s') : Later (L.fork s) (L.fork s') := by
  obtain ⟨_, _, _, fo, o, F, _, h5, h6⟩ := decide_ok L h
  rw [h6, hL]
  exact hearFl_later h5

/-- The seat at the carried record lays and reads the ledger fittingly. -/
theorem seatOwn_fits (s : Part) (F : Fork) (o : Own) :
    seatOwn.fork (seatOwn.setOwed (seatOwn.setOwn (seatOwn.setFork s F) o) none) = F := rfl

/-- **At the first chain's carried record.** -/
theorem blockAtS_later {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s') :
    ∃ a a', s.here = .lay a ∧ s'.here = .lay a' ∧ Later a.F a'.F := by
  have h' : ((named "the part is not there" (part? s)).bind fun q =>
      ((block seatOwn p).decide q rs cols).map (setPart s)) = .ok s' := h
  cases hq : part? s with
  | none => simp [hq, named, Except.bind] at h'
  | some q =>
    cases hd : (block seatOwn p).decide q rs cols with
    | error e => simp [hq, named, Except.bind, hd, Except.map] at h'
    | ok q' =>
      simp only [hq, named, Except.bind, hd, Except.map, Except.ok.injEq] at h'
      have hl := decide_later seatOwn seatOwn_fits hd
      cases hs : s.here with
      | lay a =>
        have hq1 : q.1 = a := by
          simp only [part?, hs, Option.some.injEq] at hq
          rw [← hq]
        refine ⟨a, q'.1, rfl, ?_, ?_⟩
        · rw [← h']
          rfl
        · rw [← hq1]
          exact hl
      | between => simp [part?, hs] at hq
      | att _ => simp [part?, hs] at hq
      | head _ => simp [part?, hs] at hq
      | fin _ => simp [part?, hs] at hq
      | mem _ => simp [part?, hs] at hq

/-! ### The runs of claims and the run behind the batching -/

/-- Listing the claims in front leads to a later ledger. -/
theorem formsFrontWith_later {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork}
    {fs : Array Aff} (h : formsFrontWith rows P g o F = some (fs, G)) : Later F G := by
  obtain ⟨_, _, _, F1, F2, _, _, _, _, r1, r2, e⟩ := formsFrontWith_some h
  have l12 := (OnBytes.PscRun.hideRun_keeps r1).trans (OnBytes.PscRun.hideRun_keeps r2)
  rw [e]
  refine l12.trans ?_
  split
  · exact (OnBytes.PscRun.paid_later F2 _).trans (OnBytes.PscRun.paid_later _ _)
  · exact OnBytes.PscRun.paid_later F2 _

/-- Listing the claims behind leads to a later ledger. -/
theorem formsBack_later {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsBack o F = some (fs, G)) : Later F G := by
  obtain ⟨F1, _, r1, e⟩ := formsBack_some h
  rw [e]
  exact (OnBytes.PscRun.hideRun_keeps r1).trans (OnBytes.PscRun.paid_later F1 _)

/-- Adding forms to the one equation leads to a later ledger. -/
theorem addForms_later {fs : Array Aff} {F G : Fork} (h : addForms fs F = some G) : Later F G := by
  unfold addForms at h
  rw [← Array.foldlM_toList] at h
  exact (OnBytes.PscRun.linsLoop_slots _ _ _ h).later

/-- **The run "front" keeps the ledger**, at a seat whose laying and reading of the ledger fit. -/
theorem front_later {T : Type} (L : Seat T) (hL : ∀ (s : T) (F : Fork), L.fork (L.setFork s F) = F)
    (p : Par) (run : Nat → T → Except String (List Aff × T))
    (hr : (block L p).claims.lookup "front" = some run) {n : Nat} {s s' : T} {cl : List Aff}
    (h : run n s = .ok (cl, s')) : Later (L.fork s) (L.fork s') := by
  obtain ⟨o, fs, F, _, hf, _, e⟩ := (front_ok L p run hr n s s' cl).mp h
  rw [e, hL]
  unfold frontOf at hf
  split at hf
  · exact formsFrontWith_later hf
  · exact formsFrontWith_later hf

/-- **The run "back" keeps the ledger.** -/
theorem back_later {T : Type} (L : Seat T) (hL : ∀ (s : T) (F : Fork), L.fork (L.setFork s F) = F)
    (p : Par) (run : Nat → T → Except String (List Aff × T))
    (hr : (block L p).claims.lookup "back" = some run) {n : Nat} {s s' : T} {cl : List Aff}
    (h : run n s = .ok (cl, s')) : Later (L.fork s) (L.fork s') := by
  obtain ⟨o, fs, F, _, hf, _, e⟩ := (back_ok L p run hr n s s' cl).mp h
  rw [e, hL]
  exact formsBack_later hf

/-- The run behind the batching hands the state on as it is. -/
theorem freeSlot_same {T : Type} (L : Seat T) {hp : HPlan2} {s s' : T}
    (h : freeSlot L hp s = .ok s') : s' = s := by
  unfold freeSlot at h
  cases ho : L.own s with
  | none => simp [ho, named, bind, Except.bind] at h
  | some o =>
    cases hb : freeSlotOk hp.used o.wo.sFv (L.fork s) with
    | false =>
      simp [ho, named, test, VerifiableInference.Desc.need, hb, bind, Except.bind] at h
    | true =>
      simp [ho, named, test, VerifiableInference.Desc.need, hb, bind, Except.bind, pure,
        Except.pure] at h
      exact h.symm

end OnBytes.Desc.First.K4
