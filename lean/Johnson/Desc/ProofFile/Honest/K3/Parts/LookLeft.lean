-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/LookLeft.lean: the honest side of the kind "lookup" (K3): AT
ANY NUMBER OF PARTS OF KEYS: WHAT THE LOOKUP LEAVES: the statement LookLeft
(Honest/K3/Law/Statements.lean) AT ITS OWN NAME, at every face. CONDITIONAL ON HB. Theorems.

Honest/K3/Law/LookLeftOf.lean and LookOne.lean show LookLeft's sentence at a face with one part of
keys. The one part is spent there at one place: to have that the points which the hearing keeps are
the run's (PointsAgree). Honest/K3/Parts/LookHeard.lean hands that sentence at every face, with all
else that the proof takes. So the proof goes through with no premise on the parts.

  lookLeft_ofP   CONDITIONAL ON Lawful and on what the walk along the verifier's text hands out,
                 PointsAgree among it: Left (Honest/K3/Law/LookLeftOf.lean), which
                 is LookLeft's conclusion
  lookP          CONDITIONAL ON HB and Lawful: the hearing returns on the course's rounds; what it
                 heard is the run's; the invariant behind the last stage; the leaves' own slots
                 free; and Left
  lookLeftP      **CONDITIONAL ON HB: the statement LookLeft**

HB: five statements of the law of the masked sumcheck's honest part (Honest/K3/Law/SumWhole.lean).
LookLeft is itself conditional, on Lawful: the summands sum as they should.

Limits. NO MEMBER IS TYPED HERE: no course at a face with several parts of keys. Every lookup of a
proof file has one part. The stages are played alone. The text planesV is the kind's own; which text
a seated sub-protocol runs for the claims on the planes is not said here. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.LookHeard
import Johnson.Desc.ProofFile.Honest.K3.Law.LookLeftOf
import Johnson.Desc.ProofFile.Honest.K3.Law.StageStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Reading Aff Fork ofNat)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV planesV eqPairs)
open ProofFile.Honest.K3.Law

variable {W : Type}

/-- **What the lookup leaves, at every face.** CONDITIONAL ON Fit R, HeardIs R g, the invariant
behind the last stage, RowsWorth, LateRow, PointsAgree and Lawful R planes keys. No member
is typed here. -/
theorem lookLeft_ofP (R : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE)
    (G : Fork) (g : HeardV) (hF : Fit R) (hH : HeardIs R g)
    (hI : Inv R (stages R.f).length G) (h1 : RowsWorth R g G) (h2 : LateRow R g G)
    (P : PointsAgree R.f g R.a.base (R.t.heard ++ R.ds))
    (hLaw : Lawful R planes keys) : Left R planes keys g G := by
  have hall : ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H →
      MasksAre R mask → ∀ s' ∈ stages R.f, ∀ j, j < s'.tail R.f →
      (H.worldOf Reading.gl mask entry).slot (R.endSlot s' + j) = rd (R.T s' j) := by
    intro H mask entry hl hM s' hs' j hj
    exact hI.ends H mask entry hl hM s' (by rw [List.take_length]; exact hs') j hj
  refine ⟨fun H mask entry hl hM => ⟨fun y hy => h1 hLaw.sums y hy H mask entry hl hM, ?_⟩, ?_⟩
  · intro y hy
    rw [← hLaw.keyEnds y hy]
    exact formWorth W R _ (.key y.2 y.1) hF.ok (Or.inr ⟨y, hy, rfl⟩)
      (fun s' hs' j hj => hall H mask entry hl hM s' (List.mem_of_mem_take hs') j hj)
  · intro F' G' H cl mask entry hS hGF hpl hl hM y hy
    cases hr : MaskedSum.row g.leaves oneE {} F' with
    | none => simp [planesV, hr] at hpl
    | some z =>
      obtain ⟨y0, G0⟩ := z
      simp only [planesV, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpl
      obtain ⟨rfl, rfl⟩ := hpl
      have hlater : Later G H := hGF.trans ((MaskedSum.row_keeps hr).trans hl)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · have e := h2 _ hLaw.leaves F' G0 H y0 mask entry hS hGF hr hl hM
        show y0.value Reading.gl (H.worldOf Reading.gl mask entry) +
          rd (mulE g.leaves.eps (R.f.leaf g.theta g.alpha g.zb0)) *
            planes (eqPairs (R.f.mu + R.f.d) g.zb0) = 0
        rw [P.theta, P.alpha, P.zb0, e]
        have em : rd (mulE g.leaves.eps (R.f.leaf R.pts.theta R.pts.alpha R.zb0)) =
            rd g.leaves.eps * rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) := Reading.gl.mul _ _
        show rd g.leaves.eps * (1 - (1 + rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) *
            planes (eqPairs (R.f.mu + R.f.d) R.zb0))) +
          rd (mulE g.leaves.eps (R.f.leaf R.pts.theta R.pts.alpha R.zb0)) *
            planes (eqPairs (R.f.mu + R.f.d) R.zb0) = 0
        rw [em]
        ring
      · have e := hall H mask entry hlater hM .bits (mem_bits R.f) 0 (show 0 < 1 by omega)
        show (Aff.slot g.sBit).value Reading.gl (H.worldOf Reading.gl mask entry) +
          rd (subE zeroE oneE) * planes (eqPairs (R.f.mu + R.f.d) g.zb1) = 0
        rw [Aff.value_slot, hH.sBit, P.zb1]
        have e' : (H.worldOf Reading.gl mask entry).slot (R.endSlot .bits) = rd (R.T .bits 0) := e
        have es : rd (subE zeroE oneE) = 0 - 1 :=
          (Reading.gl.sub _ _).trans (by rw [Reading.gl.zero, Reading.gl.one])
        rw [e', hLaw.bits, es]
        show planes (eqPairs (R.f.mu + R.f.d) R.zb1) +
          (0 - 1) * planes (eqPairs (R.f.mu + R.f.d) R.zb1) = 0
        ring
      · show (Aff.ofConst (subE zeroE (ofNat R.f.count))).value Reading.gl
            (H.worldOf Reading.gl mask entry) + rd oneE * planes (countPairs R.f) = 0
        have e1 : rd oneE = 1 := Reading.gl.one
        rw [Aff.value_ofConst, Reading.gl.sub, Reading.gl.zero, e1, hLaw.count]
        show 0 - rd (ofNat R.f.count) + 1 * rd (ofNat R.f.count) = 0
        ring

/-- **The hearing returns, and what it leaves has its values, at every face.** CONDITIONAL ON HB,
Fit R, the invariant in front of the first stage, the course's rounds, and Lawful R planes keys. No
member is typed here. -/
theorem lookP (B : HB) (R : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE)
    (F : Fork) (x : List Fmt.RoundView) (hF : Fit R) (I0 : Inv R 0 F) (hx : R.rounds = some x)
    (hLaw : Lawful R planes keys) :
    ∃ g G, hearV R.f F x = some (g, G) ∧ HeardIs R g ∧ Inv R (stages R.f).length G ∧
      (∀ j, R.first + firstSlot R.f .leaves ≤ j →
        j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j) ∧
      Left R planes keys g G := by
  obtain ⟨g, G, hh, hH, hI, hfree, h1, h2, P⟩ :=
    lookHeardP (stageStep B) (leavesStep B) R F x hF I0 hx
  exact ⟨g, G, hh, hH, hI, hfree, lookLeft_ofP R planes keys G g hF hH hI h1 h2 P hLaw⟩

/-- **CONDITIONAL ON HB: the statement LookLeft (Honest/K3/Law/Statements.lean), at its own name: at
every face.** No member is typed here. -/
theorem lookLeftP (B : HB) : LookLeft := by
  intro W R planes keys F G x g hF I0 hx hh hLaw
  obtain ⟨g', G', hh', _, _, _, hL⟩ := lookP B R planes keys F x hF I0 hx hLaw
  rw [hh] at hh'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh')
  exact hL

end ProofFile.Honest.K3.Parts

#print axioms ProofFile.Honest.K3.Parts.lookLeft_ofP
#print axioms ProofFile.Honest.K3.Parts.lookP
#print axioms ProofFile.Honest.K3.Parts.lookLeftP
