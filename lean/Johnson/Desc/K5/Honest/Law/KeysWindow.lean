-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/KeysWindow.lean: CONDITIONAL: AT A STATE OF THE FIRST CHAIN: EVERY SLOT
THAT A KEY FORM OF AN ATTENTION SEGMENT (kind K5) NAMES LIES IN THE WINDOW OF SLOTS THAT THE KIND's
HEARING TOOK. Four statements with their proofs. On the verifier's own data: no prover is in this
file.

  endOf_is       the window's end (endOf, HeardWindow.lean) is k5End (Live.lean): by unfolding
  keysOfO_win    CONDITIONAL: **keysOfO A t = some KF → ∀ f ∈ KF.toList,
                 SlotsIn (Win k (k5End x k)) f**
  keysOfO_slotsIn   CONDITIONAL: the same in the library's form with two numbers (SlotsIn lo hi f,
                 Johnson/Desc/Kinds/Law/SlotsFilled.lean): one with the first by unfolding
  keysOfO_from   CONDITIONAL: the half line: SlotsIn (k ≤ ·) f

The premises. gf: GeoFits (geoOf A.S) x: public · hI: HeldLive x k t
(Johnson/Desc/K5/Honest/Law/LiveState.lean): what t holds of the segment's own rounds was returned
by the hearing at the plan x, from a ledger whose arrays have their length and whose next slot was
k; of its five parts four are spent: the last, the test on the drawn elements, is not · hk: the key
forms' reader returns at t.

THE ROAD. keysOfO's text (Johnson/Desc/First/Att/SeatO.lean, RunsK.lean) is opened into the returns
of inOf, of the pad's reader, of the run "first" and of the run "keys" · at a state in an attention
segment inOf is inAt at the segment's own ledger (att_of_inOf, Claims/K5Still.lean; inOf_isAt,
Claims/InAt.lean) · what inAt is made of: inAt_spec (LiveState.lean), leftP_spec · then keysRun_win
(HeardWindow.lean).

Who is meant to pay HeldLive: at the state in front of the segment's batching: held_at_batch
(Johnson/Desc/K5/Honest/Law/HeldAtBatch.lean), under the library's head and its own premises;
heldLive_congr and heldLive_of_car carry it on.

Limits. Conditional. That a reached state has HeldLive is not proved here. Where the reader returns
nothing the statements say nothing. All Limits of HeardWindow.lean hold here too. No property is
claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.HeardWindow
import Johnson.Desc.K5.Honest.Law.LiveState
import Johnson.Desc.First.Att.SeatO
import Johnson.Desc.Kinds.Law.SlotsFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest.Window
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (parCOf geoOf GeoFits keysOfO leftP_spec)
open K5Law (SlotsIn inOf_isAt att_of_inOf)

/-- The window's end is the name that the kind's other laws have for it. -/
theorem endOf_is (x : Params.AttentionRounds) (k : ℕ) : endOf x k = k5End x k := rfl

/-- **AT A STATE: EVERY SLOT THAT A KEY FORM NAMES LIES IN THE WINDOW.** CONDITIONAL: GeoFits;
HeldLive at the state; the key forms' reader returns there. -/
theorem keysOfO_win (A : OnBytes.Attention.Plan) {x : Params.AttentionRounds} {k : ℕ} {t : First.S}
    {KF : Array Aff} (gf : GeoFits (geoOf A.S) x) (hI : HeldLive x k t)
    (hk : keysOfO A t = some KF) : ∀ f ∈ KF.toList, SlotsIn (Win k (k5End x k)) f := by
  obtain ⟨h, F, G, rs, rest, lead, h5, hh, hz, rfl, -⟩ := hI
  cases hi : P.inOf (P.seatCO (parCOf A)) (parCOf A) t with
  | none => simp [keysOfO, P.keysOfK, hi] at hk
  | some y =>
    obtain ⟨i, K⟩ := y
    cases hpd : (P.seatCO (parCOf A)).pad t with
    | none => simp [keysOfO, P.keysOfK, hi, hpd] at hk
    | some k3 =>
      cases h1 : P.Runs.firstRun i K with
      | none => simp [keysOfO, P.keysOfK, hi, hpd, h1] at hk
      | some z =>
        obtain ⟨l₁, j⟩ := z
        have hk' : P.Runs.keysRun i k3 j = some KF := by
          simpa [keysOfO, P.keysOfK, hi, hpd, h1] using hk
        obtain ⟨a, he⟩ := att_of_inOf hi
        rw [inOf_isAt he] at hi
        obtain ⟨g, -, hi⟩ := Option.bind_eq_some_iff.1 hi
        obtain ⟨h', h5', hi⟩ := Option.bind_eq_some_iff.1 hi
        have e5 : a.heard5 = some h := by
          unfold First.S.heard5? at h5
          rw [he] at h5
          exact h5
        obtain rfl : h' = h := Option.some.inj (h5'.symm.trans e5)
        obtain ⟨eg, -, L, hL, hp⟩ := inAt_spec hi
        have eg' : i.g = geoOf A.S := eg
        exact keysRun_win hh hz (i := i) (zk := g.zk) (l := L) (F' := a.F)
          (by rw [eg]; exact leftP_spec hL) (by rw [eg]; exact hp) (by rw [eg']; exact gf) h1 hk'

/-- The same in the library's form with two numbers. CONDITIONAL: as `keysOfO_win`. -/
theorem keysOfO_slotsIn (A : OnBytes.Attention.Plan) {x : Params.AttentionRounds} {k : ℕ}
    {t : First.S} {KF : Array Aff} (gf : GeoFits (geoOf A.S) x) (hI : HeldLive x k t)
    (hk : keysOfO A t = some KF) : ∀ f ∈ KF.toList,
      VerifiableInference.Desc.Kinds.Head.Law.SlotsIn k (k5End x k) f :=
  keysOfO_win A gf hI hk

/-- The half line. CONDITIONAL: as `keysOfO_win`. -/
theorem keysOfO_from (A : OnBytes.Attention.Plan) {x : Params.AttentionRounds} {k : ℕ}
    {t : First.S} {KF : Array Aff} (gf : GeoFits (geoOf A.S) x) (hI : HeldLive x k t)
    (hk : keysOfO A t = some KF) : ∀ f ∈ KF.toList, SlotsIn (k ≤ ·) f := fun f hf =>
  OnBytes.Desc.First.K4.Slots.slotsIn_mono (fun _ w => w.1) (keysOfO_win A gf hI hk f hf)

end H2K5.Honest.Window

#print axioms H2K5.Honest.Window.endOf_is
#print axioms H2K5.Honest.Window.keysOfO_win
#print axioms H2K5.Honest.Window.keysOfO_slotsIn
#print axioms H2K5.Honest.Window.keysOfO_from
