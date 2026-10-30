-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/SizesOfLed.lean: CONDITIONAL.

Not shown here. THAT THE VERIFIER's HEARING HAS RETURNED (the library's LedG) AND THAT ITS TAPE HAS
SAMPLED WHAT THE CHALLENGES HOLD (DrawnIs): hypotheses; Law/PtsAtStand.lean has both at a state
behind the member's step. The sizes of the embedding's two points (o.H.ZE, o.H.tkh) are not reached.
That the hypotheses can hold together: no example is known. By a walk of import lines the closure
holds no module with RecCompile in its name, none under Johnson/Goal/ or Johnson/D/; it holds files
over the frame. Nothing on soundness, on completeness or on any other property.
No property is claimed.

Three sizes of what the hearing leaves. `own_h1`, `own_h2` (Law/W/RightStack.lean) and
`openedOwn_of` (Law/W/OwnOf.lean) ask the second and the third as they stand here; of the first they
ask that it is at least D.lL + lF D (at least lFe D): that the plan's lamS is so large is a public
fact that no statement here has. The three: by the laws of Law/PtsHear.lean, which write each point
in the challenges' own letters.

  `rs_size`   the batched sumcheck's challenges by bit are lamS in number.
  `rt_size`   the second token sumcheck's end point has lt coordinates.
  `ztF_size`   the lookup's token point has lt coordinates.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAt
import Johnson.Road.FormsKeysPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (Fork Level Tsc Forest.Heard lastOf)
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} {ds : List Fmt.Drawn}

/-- The batched sumcheck's challenges by bit. CONDITIONAL: on L, hD, hl. -/
theorem rs_size
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 4 ≤ ds.length) : o.K.rs.size = Q.hp.lamS := by
  rw [led_rs L ds hD hl, Array.size_reverse, List.size_toArray]
  refine drawnE_take_length ds _ _ ?_
  simp only [k4StartAt] at hl ⊢
  omega

/-- The second token sumcheck's end point. CONDITIONAL: on L, hD, hl. -/
theorem rt_size
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hD : DrawnIs t ds) (hl : k4StartAt Q 3 ≤ ds.length) :
    ∀ tT', o.H.tT = some tT' → tT'.r.size = Q.P.y.h.lt := by
  intro tT' hT
  obtain rfl := Option.some.inj (L.kTT.symm.trans hT)
  show tT.r.size = _
  rw [led_rt L ds hD hl, List.size_toArray]
  refine drawnE_take_length ds _ _ ?_
  simp only [k4StartAt] at hl ⊢
  omega

/-- The lookup's token point. CONDITIONAL: on L. -/
theorem ztF_size
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5) : o.H.ztF.size = Q.P.y.h.lt := by
  have h := led_ztF L
  cases e : lastOf fo.zx Q.P.y.h.lt with
  | error x =>
    rw [e] at h
    exact absurd h (by simp [Except.toOption])
  | ok Z =>
    rw [e] at h
    obtain rfl : Z = o.H.ztF := Option.some.inj h
    obtain ⟨h1, h2⟩ := OnBytes.Road.lastOf_ok e
    rw [h2, Array.size_extract]
    omega

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.rs_size
#print axioms ProofFile.Honest.K4.W.rt_size
#print axioms ProofFile.Honest.K4.W.ztF_size
