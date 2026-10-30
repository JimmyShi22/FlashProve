-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/TidyTop.lean: THE INSTANCE, AND "TIDY" AT EVERY REACHED
STATE. NEW, typed by hand.
  TidyL A B   where A's code table's lengths are in order: B's code table is A's, and if A is tidy
  so is B. WHY NOT TidyStay: the proximity test's own law on "tidy" (calls_walk,
  Johnson/Desc/K12/Law/CallsWalkG.lean) stands UNDER "the code table's lengths are in order": so
  "tidy in front, tidy behind" with no premise is shown of that sub-protocol by nobody.
  groundQuiet_tidyL · stQuiet_tidyL · admitOn_tidyL · atFinish_tidyL (K12: PAID) · k2_tidyL (from
  the sentence that is owed on TidyStay, with the kind's own yes_keeps_whole at Grows)
  descPure_tidyL   every sub-protocol of the first chain's flat list: Fits (ByS TidyL) b
  reach_tidyL      along Reach: tidy, and the first state's code table
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.AtSeats.Fit.TidySeat
import Johnson.Top.H0.Tw.K2C.KeepsWhole
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Means (Tidy)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl WholeF Fits Steps steps_of_fits)
open VerifiableInference.Desc.Ground (GroundQuiet By TidyStay groundQuiet_tidy admitOn_tidy
  tidyStay_begun groundKeeps_grows)
open VerifiableInference.Desc.K13.Law (StQuiet row_of_quiet)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile (Pub)

/-- **Where the code table's lengths are in order: the code table stays, and a tidy statement stays
tidy.** -/
def TidyL (A B : Statement) : Prop :=
  A.codes.lengthsOk = true → B.codes = A.codes ∧ (Tidy A → Tidy B)

theorem tidyL_mk {A B : Statement} (g : Grows A B) (t : TidyStay A B) : TidyL A B :=
  fun _ => ⟨g.1, t⟩

theorem groundQuiet_tidyL : GroundQuiet TidyL where
  refl := fun _ _ => ⟨rfl, id⟩
  trans := fun {A B C} h k hl => by
    obtain ⟨e1, t1⟩ := h hl
    obtain ⟨e2, t2⟩ := k (e1 ▸ hl)
    exact ⟨e2.trans e1, fun x => t2 (t1 x)⟩
  newGroup := fun d d' a b n h =>
    tidyL_mk (groundKeeps_grows.newGroup d d' a b n h) (groundQuiet_tidy.newGroup d d' a b n h)
  recv := fun ft d d' a b h =>
    tidyL_mk (groundKeeps_grows.recv ft d d' a b h) (groundQuiet_tidy.recv ft d d' a b h)
  join := fun d d' a b c h =>
    tidyL_mk (groundKeeps_grows.join d d' a b c h) (groundQuiet_tidy.join d d' a b c h)
  addRow := fun d d' a b h =>
    tidyL_mk (groundKeeps_grows.addRow d d' a b h) (groundQuiet_tidy.addRow d d' a b h)
  takeMask := fun d d' a b h =>
    tidyL_mk (groundKeeps_grows.takeMask d d' a b h) (groundQuiet_tidy.takeMask d d' a b h)
  closeLedger := fun d d' a h =>
    tidyL_mk (groundKeeps_grows.closeLedger d d' a h) (groundQuiet_tidy.closeLedger d d' a h)
  spendAsMask := fun d d' a h =>
    tidyL_mk (groundKeeps_grows.spendAsMask d d' a h) (groundQuiet_tidy.spendAsMask d d' a h)
  adopt := fun d d' a b c h =>
    tidyL_mk (groundKeeps_grows.adopt d d' a b c h) (groundQuiet_tidy.adopt d d' a b c h)

theorem stQuiet_tidyL : StQuiet TidyL where
  quiet := groundQuiet_tidyL
  begun := fun T g G hG _ => ⟨Slice.closeLedgers_codes _ _, tidyStay_begun T g G hG⟩
  row := fun lay im o n lin T r os' h _ =>
    ⟨rfl, row_of_quiet groundQuiet_tidy lay im o n lin T r os' h⟩

theorem admitOn_tidyL : K1.AdmitOn TidyL :=
  fun d d' o rows h hr =>
    tidyL_mk (groundKeeps_grows.admit d d' o rows h) (admitOn_tidy d d' o rows h hr)

/-- **The first chain's last proximity test**: a run of calls of the plain functions, each with its
conditions. -/
theorem atFinish_tidyL (p : K12.P12) : Decides (ByS TidyL) (K12.atFinish p) := by
  intro s rs gs s' h hl
  obtain ⟨o, t', -, -, -, hk, rfl⟩ := K12.Seat.atFinish_ok p s _ rs gs h
  have w := H2K.Out.calls_walk OnBytes.Model.Reading.gl
    (H2K.Out.k12_calls p _ t' rs gs hk [] []) hl
  exact ⟨w.2, w.1.tidy⟩

/-- Kind K2's sub-protocol with rounds: from the sentence that is owed on "tidy". -/
theorem k2_tidyL
    (hK2 : ∀ p : K2.P2, p.firstTree = 0 →
      Fits (By TidyStay fun s : S => s.st) (K2.codeSwitchKind p : Block S Unit))
    (p : K2.P2) (h0 : p.firstTree = 0) : Fits (ByS TidyL) (K2.codeSwitchKind p : Block S Unit) :=
  fun hp s rs gs s' hf h _ =>
    ⟨(K2.yes_keeps_whole groundKeeps_grows h).1, hK2 p h0 hp s rs gs s' hf h⟩

/-- **AT THE PROOF FILE's SEAT: EVERY SUB-PROTOCOL OF THE FIRST CHAIN.** -/
theorem descPure_tidyL
    (hK2 : ∀ p : K2.P2, p.firstTree = 0 →
      Fits (By TidyStay fun s : S => s.st) (K2.codeSwitchKind p : Block S Unit))
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Fits (ByS TidyL) b :=
  descPure_fits stQuiet_tidyL admitOn_tidyL (k2_tidyL hK2) atFinish_tidyL h

/-- **"Tidy" at every reached state.** -/
theorem reach_tidyL {Pp Cl : Type} {ft : ℕ} {bs : List (Block S Cl)} {start : Pp → S}
    (h0 : ∀ z, Tidy (start z).st ∧ (start z).st.codes.lengthsOk = true)
    (hb : ∀ b ∈ bs, b.planOk = true → Fits (ByS TidyL) b) (hp : ∀ b ∈ bs, b.planOk = true)
    {k : ℕ} {a : Pp × S} (h : Reach ft bs start k a) :
    Tidy a.2.st ∧ a.2.st.codes = (start a.1).st.codes := by
  induction h with
  | zero z => exact ⟨(h0 z).1, rfl⟩
  | @succ k z s s' b _ hk hy ih =>
    obtain ⟨R, c, _, hs⟩ := hy
    have hm := List.mem_of_getElem? hk
    have w : TidyL s.st s'.st := steps_of_fits (hb b hm (hp b hm)) (hp b hm) ft s R c s' _ hs
    obtain ⟨e, t⟩ := w (by rw [ih.2]; exact (h0 z).2)
    exact ⟨t ih.1, e.trans ih.2⟩

end Meaning.K2
