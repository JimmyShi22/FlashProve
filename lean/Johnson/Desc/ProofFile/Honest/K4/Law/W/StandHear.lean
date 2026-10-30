-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/StandHear.lean: CONDITIONAL.

Not shown here. THAT THE VERIFIER's HEARING HAS RETURNED (the library's LedG), THAT ITS TAPE HAS
SAMPLED WHAT THE CHALLENGES HOLD (DrawnIs), AND K4Stand (Law/SlotsTrue.lean: the member's step has
accepted what the honest row has played): hypotheses; no example is known. By a walk of import lines
the closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms,
Bcs), through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under
Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness
or on any other property. No property is claimed.

Three small facts on what the hearing leaves, which the statements at a state behind the member's
step spend (Law/W/FootAtStand.lean, Law/W/BackAtStand.lean).

  `PV_size`, `rtV_size`   the norms' token point and the end point of the row products' token
      sumcheck have lt coordinates.
  `stand_hear`   the hearing's return at a state behind the member's step, with the look that it was
      handed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsNorms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Tape paired)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.K4 (Par seatS entries hear engFl)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)

/-! ## 1 Two sizes -/

section
variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} {ds : List Fmt.Drawn}

/-- The norms' token point. CONDITIONAL: on L, hD, hl. -/
theorem PV_size
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length) : o.H.PV.size = Q.P.y.h.lt := by
  obtain ⟨u1, hN, _⟩ := L.nt
  obtain ⟨_, _, _, a4, _⟩ := norms_vals hN ds hD hl
  rw [L.kPV]
  exact a4

/-- The end point of the row products' token sumcheck. CONDITIONAL: on L, hD, hl. -/
theorem rtV_size
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 2 ≤ ds.length) : o.H.tV.r.size = Q.P.y.h.lt := by
  rw [led_rtV L ds hD hl, List.size_toArray]
  refine drawnE_take_length ds _ _ ?_
  simp only [k4StartAt] at hl ⊢
  omega

end

/-! ## 2 The hearing's return -/

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **The hearing's return at a state behind the member's step.** CONDITIONAL: on Z. -/
theorem stand_hear {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    ∃ F, hear engFl { Q.P with tokv := s.tokv } Q.hp Q.g o.H.fo F
      (paired (roundsOf y.1) (entries Q.P Q.hp Q.g)) = some (o, A.F, []) := by
  obtain ⟨a, a₀, fo, _, ha0, _, hfo, hh, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  have hl : seatS.look s = some fo := by
    show (match s.here with | .lay a => a.fo | _ => none) = _
    rw [ha0]
    exact hfo
  obtain rfl : o.H.fo = fo := Option.some.inj ((stand_look Z).symm.trans hl)
  exact ⟨a.F, hh⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.PV_size
#print axioms ProofFile.Honest.K4.W.rtV_size
#print axioms ProofFile.Honest.K4.W.stand_hear
