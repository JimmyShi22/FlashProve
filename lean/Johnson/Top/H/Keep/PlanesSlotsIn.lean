-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
planes_slotIn: no state of the verifier is shown at which its premises hold
together.
Johnson/Top/H/Keep/PlanesSlotsIn.lean: The kind "lookup" (K3): WHICH SLOTS THE THREE CLAIMS OF THE
RUN "planes" NAME, AND THAT EACH OF THEM PASSES THE PUBLIC TEST slotIn
(Johnson/Desc/First/Batch/FormsIn.lean) at the late slots K9.lateOf of the ledgers in front of and
behind the run. Statements and proofs. Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: K3.planesRun (Johnson/Desc/First/Look/K3Runs.lean) at any seat whose claims' forms are read
  by form; K9.slotIn, K9.lateOf, K9.mergeOf.
Used by Johnson/Desc/First/Att/K05PlanesLeft.lean and Johnson/P5J/K03MergeAttAt.lean.
LETTERS: P, seat, form, lm, readers, n, s, s', cl, g, own, free, a, G free.
Compiled with the whole library.

Main names:
  slotsIn_got, slotsIn_planesAff, slotsIn_countAff: the caller's columns and the two sums.
  planes_slotsIn: a claim of "planes" names no slot but: the window of the sumcheck over the leaves;
    the slot of the bits' shown value; what the leaves' starting form names; what the caller's forms
    on the columns (bit, pin) name. General in the property P of a slot. The sister, for slots, of
    planes_rowsIn (Johnson/Top/H/Keep/PlanesRowsIn.lean), which speaks of entries.
  slotIn_of_behind: THE WAY BACK OF slotIn_behind (Johnson/Top/H/Keep/LateWorld.lean): a slot that
    is below the number of slots and filled BEHIND a run passes slotIn at the ledger in front, at
    the late slots lateOf: it was filled in front, or it is late.
  planes_filledBehind: every slot that a claim of "planes" names is there and filled in the ledger
    behind the run.
  planes_slotIn: THE END.
  mergeOf_none: outside a layers' link and the output head's link the merge has no slot: so there
    the clause "not the merge's free slot" asks nothing.

EACH PREMISE OF planes_slotIn, AND WHO PAYS IT.
  hs (SeatFits): proved of both real seats: Johnson/Top/H/K3SeatFits.lean.
  hf, hg: the state's ledger and what was heard: the row's own.
  hrun: the run accepts: planesRun_answers
    (Johnson/Desc/Kinds/Law/SilentPlanes.lean) from the clauses of leavesReady_of_leftAt
    (Johnson/Top/H/Keep/K3LeftWindow.lean) and the caller's readers.
  hG: the ledger behind.
  hS: the ledger in front has its sizes: the row's own (K3LeftAt has it at the lookup's border).
  hB: the slot of the bits' shown value is there and filled: THE LOOKUP's: left_sBitIn
    (K3LeftWindow.lean); at a later ledger by Fo.Later.
  hst: the slots that the leaves' starting form names are there and filled: THE LOOKUP's, BUT NOT IN
    THE SENTENCE K3LeftAt: LeavesFilled, made by k3_calls_leavesFilled (K3LeftWindow.lean) at an
    accept of the lookup's decide; at a later ledger by leavesFilled_stays.
  hb, hp: the slots that the caller's forms name are there and filled: THE CALLER's.
  hmask: the mask row's message has a seat among own: a fact on the state's frame and book: NOT TO
    BE HAD FROM WHAT THE LOOKUP LEFT. Its payer: MaskOkCalls.seat
    (Johnson/Desc/First/Look/K3CallsMask.lean).
  hfree: no claim names the merge's free slot: at an attention link by mergeOf_none.

Limits. On slots alone: nothing on entries. Nothing on what lies under a slot. lateOk is not spoken
of.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3RunsLaw
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H.Keep.PadNamed
import Johnson.Top.H.Keep.LateWorld
import Johnson.Road.K4.Slots.SlotsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.K.Kc OnBytes.PscRun
open OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_mono slotsIn_empty slotsIn_ofConst slotsIn_slot
  slotsIn_addMul slotsIn_scale slotsIn_add slotsIn_sub slotsIn_foldl slotsIn_rowForm)
open Cb.Fo.PlaneClaims (planesAff countAff)
open VerifiableInference.Desc.K3 (Seat Readers planesRun)
open VerifiableInference.Desc.K9 (lateOf lateAt slotIn maskSeat mergeOf)
open VerifiableInference.Desc.Sound (lateAt_late)
open _root_.Fo.Tp (got In hide_new)

section
variable {P : ℕ → Prop}

/-- What a reader's column hands in. -/
theorem slotsIn_got (o : Option Aff) (h : ∀ f, o = some f → SlotsIn P f) (F : Fork) (c : Tape) :
    SlotsIn P (got (Fl.need o) F c) := by
  cases o with
  | none => exact slotsIn_empty
  | some f => exact h f rfl

theorem slotsIn_planesAff (g : Heard) (lm e : ℕ) (B : ℕ → Aff) (h : ∀ col, SlotsIn P (B col)) :
    SlotsIn P (planesAff g lm e B) := by
  unfold planesAff
  exact slotsIn_foldl _ (fun f col hf => slotsIn_addMul _ hf (h col)) _ _ (slotsIn_ofConst _)

theorem slotsIn_countAff (g : Heard) (lm : ℕ) (B : ℕ → Aff) (h : ∀ col, SlotsIn P (B col)) :
    SlotsIn P (countAff g lm B) := by
  unfold countAff
  exact slotsIn_foldl _ (fun f col hf => slotsIn_add hf (h col)) _ _ (slotsIn_ofConst _)

/-- **Which slots a claim of "planes" names.** -/
theorem planes_slotsIn {S Cl : Type} (seat : Seat S Cl) (form : Cl → Aff)
    (hform : ∀ a, form (seat.claim a) = a) (lm : ℕ) (readers : Readers S) {n : ℕ} {s s' : S}
    {cl : List Cl} {g : Heard} (hg : seat.heard s = some g)
    (hrun : planesRun seat lm readers n s = .ok (cl, s'))
    (hw : ∀ i, i < g.leaves.walk.1.length → P (g.leaves.first + i)) (hB : P g.sBit)
    (hst : SlotsIn P g.leaves.start)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → SlotsIn P f)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → SlotsIn P f) :
    ∀ c ∈ cl, SlotsIn P (form c) := by
  obtain ⟨F, g1, e1, e2⟩ := planes_heard seat lm readers hrun
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans e2)
  obtain ⟨r, rows, G, u, hr, h1, rfl, _⟩ := planesRun_cut seat lm readers e1 e2 hrun
  obtain ⟨_, row, p', h2, rfl⟩ := _root_.Fo.Tp.planeClaims_run g lm _ _ (fun _ _ => quiet_need _)
    (fun _ => quiet_need _) F G [] u rows h1
  obtain ⟨-, -, -, -, -, -, rfl, -⟩ := _root_.Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ h2
  have b0 : ∀ e, SlotsIn P (planesAff g lm e fun col => got (Fl.need (r.1 e col)) F []) :=
    fun e => slotsIn_planesAff g lm e _ fun col => slotsIn_got _ (hb r hr e col) F []
  have c0 : SlotsIn P (countAff g lm fun col => got (Fl.need (r.2 col)) F []) :=
    slotsIn_countAff g lm _ fun col => slotsIn_got _ (hp r hr col) F []
  intro c hc
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hc
  rw [hform]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact slotsIn_rowForm _ _ hw hst (slotsIn_scale _ (b0 0))
  · exact slotsIn_sub (slotsIn_slot hB) (b0 1)
  · exact c0

end

/-- **A slot that is there and filled behind a run passes the public test in front of it**, at the
late slots lateOf. -/
theorem slotIn_of_behind (own : List (ℕ × ℕ)) (free : Option ℕ) (a : Desc.K9.Part) (G : Fork)
    (hS : Sized a.F) (hns : G.ns = a.F.ns) (j : ℕ) (hj : j < G.ns)
    (hg : G.gotF.getD j false = true) (hmask : (maskSeat own a).isSome = true)
    (hfree : free ≠ some j) : slotIn own free (lateOf a.F G) a j = true := by
  have h1 : j < a.F.ns := by
    rw [← hns]
    exact hj
  have h4 : j < a.F.vp.size := by
    rw [hS.1]
    exact h1
  have h5 : j < a.F.mf.size := by
    rw [hS.2.1]
    exact h1
  have h6 : (free != some j) = true := bne_iff_ne.2 hfree
  unfold slotIn
  rw [decide_eq_true h1, hmask, h6, decide_eq_true h4, decide_eq_true h5]
  cases hF : a.F.gotF.getD j false with
  | false =>
    rw [lateAt_late hj hF hg]
    rfl
  | true => simp

section
variable {S Cl : Type} (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (lm : ℕ)
  (readers : Readers S) {n : ℕ} {s s' : S} {cl : List Cl} {g : Heard} {F G : Fork}
include hs

/-- **Every slot that a claim of "planes" names is there and filled behind the run.** -/
theorem planes_filledBehind (hf : seat.fork s = some F) (hg : seat.heard s = some g)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) (hG : seat.fork s' = some G)
    (hS : Sized F) (hB : g.sBit < F.ns ∧ Filled F g.sBit)
    (hst : _root_.Fo.FilledA F g.leaves.start)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → _root_.Fo.FilledA F f)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → _root_.Fo.FilledA F f) :
    G.ns = F.ns ∧ ∀ c ∈ cl, ∀ x ∈ (form c).slots.toList, x.1 < G.ns ∧ Filled G x.1 := by
  obtain ⟨G1, hG1, rfl⟩ := planes_fills seat lm readers hf hg hrun
  obtain rfl : G1.paid g.owedPlanes = G :=
    Option.some.inj ((hs.markFork s F _ hf).symm.trans hG)
  obtain ⟨hL, _, hnew⟩ := hide_new hS hG1
  have up : ∀ j, In F j → In G1 j := fun j hj => hj.later hL
  have key : ∀ c ∈ cl, SlotsIn (In G1) (form c) :=
    planes_slotsIn seat form hs.form lm readers hg hrun
      (fun i hi => hnew i (by
        rw [Array.size_replicate]
        exact hi))
      (up _ hB) (slotsIn_mono up hst)
      (fun r hr e col f hf' => slotsIn_mono up (hb r hr e col f hf'))
      (fun r hr col f hf' => slotsIn_mono up (hp r hr col f hf'))
  exact ⟨hL.ns, fun c hc x hx => key c hc x hx⟩

/-- **THE END: every slot that a claim of "planes" names passes slotIn.** -/
theorem planes_slotIn (own : List (ℕ × ℕ)) (free : Option ℕ) (a : Desc.K9.Part)
    (hf : seat.fork s = some a.F) (hg : seat.heard s = some g)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) (hG : seat.fork s' = some G)
    (hS : Sized a.F) (hB : g.sBit < a.F.ns ∧ Filled a.F g.sBit)
    (hst : _root_.Fo.FilledA a.F g.leaves.start)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → _root_.Fo.FilledA a.F f)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → _root_.Fo.FilledA a.F f)
    (hmask : (maskSeat own a).isSome = true)
    (hfree : ∀ c ∈ cl, ∀ x ∈ (form c).slots.toList, free ≠ some x.1) :
    ∀ c ∈ cl, ∀ x ∈ (form c).slots.toList, slotIn own free (lateOf a.F G) a x.1 = true := by
  obtain ⟨hns, key⟩ :=
    planes_filledBehind seat form hs lm readers hf hg hrun hG hS hB hst hb hp
  intro c hc x hx
  obtain ⟨k1, k2⟩ := key c hc x hx
  exact slotIn_of_behind own free a G hS hns x.1 k1 k2 hmask (hfree c hc x hx)

end

/-- Outside a layers' link and the output head's link the merge has no slot. -/
theorem mergeOf_none {s : Desc.First.S} (h1 : ∀ a, s.here ≠ .lay a) (h2 : ∀ a, s.here ≠ .head a) :
    mergeOf s = none := by
  unfold mergeOf
  cases hh : s.here with
  | lay a => exact absurd hh (h1 a)
  | head a => exact absurd hh (h2 a)
  | between => rfl
  | att a => rfl
  | fin a => rfl
  | mem a => rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.planes_slotsIn
#print axioms VerifiableInference.OnPublicFiles.slotIn_of_behind
#print axioms VerifiableInference.OnPublicFiles.planes_filledBehind
#print axioms VerifiableInference.OnPublicFiles.planes_slotIn
#print axioms VerifiableInference.OnPublicFiles.mergeOf_none
