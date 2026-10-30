-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/CarriesAtS.lean: K4's BLOCK AT THE CARRIED RECORD CARRIES WHAT WAS HEARD AND
THE LEDGER: its decision, its two runs of claims and its run behind the batching. Two definitions,
statements and proofs. FRAME's LAWS: no error term; nothing on soundness.

  `Carried hd s s'`: from s to s': what the reading hd finds at s it finds at s'; a ledger with its
    sizes at s (`S.fork?`, `OnBytes.PscRun.Sized`) is followed at s' by a later one with its sizes,
    at the library's order `Fo.Later` (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean).
    IT IS, UNFOLDED, `CarriesFo S.fork? hd s s'`
    (Johnson/Desc/First/LedgerAtFo.lean, over `Carries` of Johnson/Desc/Sound/FoldSteps.lean): these
    two files are not imported here; Lean takes the one for the other in
    Johnson/Desc/First/K4/CarriesFoK4.lean (`carried_iff`).
  `KeepsIn hd`: hd reads nothing that K4 writes: it finds the same in a layers' link whatever ledger
    and whatever «heard by K4» lie there and whatever the debt of rows is. It is enough for the laws
    here, not needed: a reading off what K4 heard is carried by the runs and is not served.
    `keepsIn_look`,
    `keepsIn_digits`: so the two readings that are asked: `S.lookHeard?` and the digits' lookup's
    (`fun s => s.tl?.bind (·.heard)`).
  `carried_of_later`, `carried_of_wrote`: the one step: a later ledger laid in the link, whatever
    else of K4's is written. `blockAtS_claims`: the block's two runs of claims, as they stand.
  `k4_runsStep`: EVERY RUN OF CLAIMS of `blockAtS p`, wherever it returns: `Carried hd`: unfolded,
    `(blockAtS p).RunsStep (CarriesFo S.fork? hd)`, the premise `KindsCarry.k4`.
  `k4_steps`: the like of the block's decision (`Block.Steps`). `k4_afterStep`: of its run behind
    the batching (`Block.AfterStep`).
  `k4_runs_look`, `k4_runs_digits`: `k4_runsStep` at the two readings.

Limits. They run over all records, also those that no run reaches: where the chain stands in no
layers' link the block and its runs refuse, and the laws hold for nothing there. NOTHING HERE SHOWS
THAT ANY DECISION OR RUN OF `blockAtS p` RETURNS ANYWHERE: a block that refuses all has every law of
this file for nothing. One direction, from a return.
-/
import Johnson.Desc.First.K4.RunsAtS
import Johnson.Desc.First.K4.AtSHears
import OnBytes.Tie.Pv.Lookup.Forest.FoForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open OnBytes.PscRun (Later Sized)
open VerifiableInference.Desc (Block named)
open VerifiableInference.Desc.First (S LayOwn)

/-- From s to s': what hd finds at s it finds at s'; a ledger with its sizes at s is followed at s'
by a later one with its sizes. -/
def Carried (hd : S → Option Forest.Heard) (s s' : S) : Prop :=
  (∀ g, hd s = some g → hd s' = some g) ∧
    ∀ F, s.fork? = some F → Sized F → ∃ F', s'.fork? = some F' ∧ _root_.Fo.Later F F' ∧ Sized F'

/-- hd reads nothing that K4 writes. -/
def KeepsIn (hd : S → Option Forest.Heard) : Prop :=
  ∀ (s : S) (a : LayOwn) (G : Fork) (w : Option Own) (d : Option Nat), s.here = .lay a →
    hd { s with here := .lay { a with F := G, own := w }, rowsOwed := d } = hd s

theorem keepsIn_look : KeepsIn S.lookHeard? := by
  intro s a G w d h
  simp [S.lookHeard?, h]

theorem keepsIn_digits : KeepsIn fun s => s.tl?.bind (·.heard) := by
  intro s a G w d h
  simp [S.tl?, h]

/-- The one step: a later ledger laid in the link, whatever else of K4's is written. -/
theorem carried_of_later {hd : S → Option Forest.Heard} (H : KeepsIn hd) {s : S} {a : LayOwn}
    {G : Fork} (w : Option Own) (d : Option Nat) (ha : s.here = .lay a) (hl : Later a.F G) :
    Carried hd s { s with here := .lay { a with F := G, own := w }, rowsOwed := d } := by
  refine ⟨fun g hg => by rw [H s a G w d ha]; exact hg, fun F hF hs => ?_⟩
  have e : F = a.F := by
    simp only [S.fork?, ha, Option.some.injEq] at hF
    exact hF.symm
  subst e
  exact ⟨G, rfl, ⟨hl.next, hl.ns, hl.keep⟩, hl.sized hs⟩

/-- What a run of K4's writes carries. -/
theorem carried_of_wrote {hd : S → Option Forest.Heard} (H : KeepsIn hd) {s s' : S} {a : LayOwn}
    {G : Fork} (hw : Wrote s a G s') (hl : Later a.F G) : Carried hd s s' := by
  obtain ⟨ha, rfl⟩ := hw
  exact carried_of_later H a.own _ ha hl

/-- The block's two runs of claims, as they stand. -/
theorem blockAtS_claims (p : Par) : (blockAtS p).claims =
    [("front", fun _ t => (named "the part is not there" (part? t)).bind fun q =>
        (runOf seatOwn "K4.claims-front"
          ((if p.k3Runs then formsFrontNoRows else formsFront) p.P p.g) q).map fun y =>
            (y.1, setPart t y.2)),
     ("back", fun _ t => (named "the part is not there" (part? t)).bind fun q =>
        (runOf seatOwn "K4.claims-back" formsBack q).map fun y => (y.1, setPart t y.2))] := rfl

/-- **Every run of claims of K4's block at the carried record carries.** -/
theorem k4_runsStep {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    ∀ c ∈ (blockAtS p).claims, ∀ (n : Nat) (s : S) (cl : List Aff) (s' : S),
      c.2 n s = .ok (cl, s') → Carried hd s s' := by
  intro c hc n s cl s' h
  rw [blockAtS_claims] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · obtain ⟨a, o, fs, G, _, hf, _, hw⟩ := runOfAtS h
    refine carried_of_wrote H hw ?_
    split at hf
    · exact formsFrontWith_later hf
    · exact formsFrontWith_later hf
  · rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨a, o, fs, G, _, hf, _, hw⟩ := runOfAtS h
      exact carried_of_wrote H hw (formsBack_later hf)
    · exact absurd hc List.not_mem_nil

/-- **The block's decision carries.** -/
theorem k4_steps {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    ∀ (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : S),
      (blockAtS p).decide s rs gs = .ok s' → Carried hd s s' := by
  intro s rs gs s' h
  obtain ⟨a, fo, o, G, ha, _, _, _, _, hh, rfl⟩ := blockAtS_hears h
  exact carried_of_later H (some o) none ha (hearFl_later hh)

/-- **The block's run behind the batching carries.** -/
theorem k4_afterStep {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    ∀ c ∈ (blockAtS p).after, ∀ (s s' : S), c.2 s = .ok s' → Carried hd s s' := by
  intro c hc s s' h
  have e : (blockAtS p).after = [("free-slot", fun t =>
      (named "the part is not there" (part? t)).bind fun q =>
        (freeSlot seatOwn p.hp q).map (setPart t))] := rfl
  rw [e] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · obtain ⟨a, hw⟩ := freeSlotAtS (p := p) (run := fun t =>
      (named "the part is not there" (part? t)).bind fun q =>
        (freeSlot seatOwn p.hp q).map (setPart t)) (by rw [e]; simp) h
    exact carried_of_wrote H hw (OnBytes.PscRun.Later.refl a.F)
  · exact absurd hc List.not_mem_nil

/-- At what the lookup on the calls was heard to return. -/
theorem k4_runs_look (p : Par) :
    ∀ c ∈ (blockAtS p).claims, ∀ (n : Nat) (s : S) (cl : List Aff) (s' : S),
      c.2 n s = .ok (cl, s') → Carried S.lookHeard? s s' :=
  k4_runsStep keepsIn_look p

/-- At what the lookup on the digits was heard to return. -/
theorem k4_runs_digits (p : Par) :
    ∀ c ∈ (blockAtS p).claims, ∀ (n : Nat) (s : S) (cl : List Aff) (s' : S),
      c.2 n s = .ok (cl, s') → Carried (fun s => s.tl?.bind (·.heard)) s s' :=
  k4_runsStep keepsIn_digits p

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.k4_runsStep
#print axioms OnBytes.Desc.First.K4.k4_steps
#print axioms OnBytes.Desc.First.K4.k4_afterStep
#print axioms OnBytes.Desc.First.K4.k4_runs_look
#print axioms OnBytes.Desc.First.K4.k4_runs_digits
