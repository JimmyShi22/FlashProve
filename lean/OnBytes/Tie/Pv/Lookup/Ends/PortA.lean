-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/PortA.lean: the value of four key forms, and of the padding's term, of an
attention sub-proof in the Lean verifier under OnBytes/ (here: the port), as the terms kfKR, kfWH,
kfWL and kfKFD.

Statements and proofs, over the port's World and its reading Reading.gl into the library's field
Cb.Gl.E. The forms are the port's own keyKR, keyKFD, padTerm (OnBytes/Model/AttentionClaimsA.lean),
keyWH and keyWL (OnBytes/Model/AttentionClaimsB.lean); the terms are those of AlgA, AlgA2 and
AlgA3 beside this file. No statement has a premise.
Main names:
  `toF_fOfNat`, `readE_ofNat`, `readE_scaleNat`: the port's numbers, read.
  `value_keyKR`, `value_keyWH`, `value_keyWL`: in every world W the value of the port's form is
    kfKR, kfWH or kfWL at W's slots, at the read sum of the pieces' weights (readE (sumW ..)) and,
    for keyWL, at the read zsl.
  `value_keyKFD`: the same with kfKFD; the public value gc is read off the port's own closed form:
    C LW ones(zs) for segment fm, else Om LW (1 - LE(zj, zi)).
  `value_padTerm`: the value of padTerm is the call's padding row, read, times (1 - the read wall);
    wall c z is the port's sum of the weights of all pieces of the call c at the point z.
Limits: nothing is stated here on keyIX (value_keyIX is in PortA2 beside this file). That W's slots
have the rule values of AlgA, AlgA2 and AlgA3 is proved nowhere: it is a premise wherever it stands.
Not stated here, but in PortA2 and AlgAW beside this file, each under premises of its
own: that the read sum of weights is lwAt (readE_sumW_pieces); that the read wall is the sum of the
weights wpAt of the call's pieces (readE_wall); that the padding row as read here is the cast of
tauN h q (t0N h q) (pad_read); that the closed form of the public value is the rule value of gcAt
(a premise). That the read zsl is the coordinate pt (n - (1 + b')) of unit_WL is proved in none of
these files.

-/
import OnBytes.Model.AttentionClaimsB
import OnBytes.Model.HideLaws
import OnBytes.Slice.ProgField
import OnBytes.Tie.Pv.Lookup.Ends.AlgA3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends.A

open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Attention (Seg ACall PlaneClaim Score Divide PW sumW keyKR keyKFD keyWL keyIX keyWH
  padTerm wall remForm indexForm onesOf leOf idOf ShD)

/-- The library's extension field. -/
abbrev GE : Type := Cb.Gl.E

/-- The port's reading into the library's field is readE. -/
theorem gl_val (x : E) : Reading.gl.val x = readE x := rfl

/-- A number as a word of the base field, read. -/
theorem toF_fOfNat (v : ℕ) : toF (fOfNat v) = (v : Cb.Gl.F) := by
  have hp : pW.toNat = Code.pGold := by rw [Code.pGold_eq]; rfl
  have h1 : v % pW.toNat < 2 ^ 64 := by
    have : v % pW.toNat < pW.toNat := Nat.mod_lt _ (by rw [hp]; exact Code.pGold_prime.pos)
    have h2 : pW.toNat < 2 ^ 64 := pW.toNat_lt
    omega
  unfold toF fOfNat
  rw [show (v % pW.toNat).toUInt64 = UInt64.ofNat (v % pW.toNat) from rfl,
    UInt64.toNat_ofNat_of_lt' h1, hp]
  exact ZMod.natCast_mod v Code.pGold

/-- **The port's ofNat, read.** -/
theorem readE_ofNat (v : ℕ) : readE (ofNat v) = (v : GE) := by
  unfold ofNat
  rw [readE_ofF, toF_fOfNat, map_natCast]

/-- **The port's scaleNat, read.** -/
theorem readE_scaleNat (x : E) (v : ℕ) : readE (scaleNat x v) = (v : GE) * readE x := by
  unfold scaleNat
  rw [readE_scale, toF_fOfNat, Algebra.smul_def, map_natCast]

variable (W : World GE)

/-- **keyKR, valued.** -/
theorem value_keyKR (pc : PlaneClaim) :
    (keyKR pc).value Reading.gl W =
      kfKR (W.slot pc.s0) (W.slot (pc.s0 + 1)) (W.slot (pc.s0 + 2)) (readE (sumW pc.pw)) := by
  simp only [keyKR, Aff.value_add, Aff.value_scale, Aff.value_slot, Aff.value_ofConst, gl_val,
    readE_ofNat, readE_scaleNat, kfKR]
  push_cast
  ring

/-- **keyWH, valued.** -/
theorem value_keyWH (d : Divide) :
    (keyWH d).value Reading.gl W =
      kfWH (W.slot d.s5h) (W.slot (d.s5h + 1)) (readE (sumW d.pwH)) := by
  simp only [keyWH, Aff.value_add, Aff.value_scale, Aff.value_slot, Aff.value_ofConst, gl_val,
    readE_ofNat, readE_scaleNat, kfWH]
  push_cast
  ring

/-- **keyWL, valued.** -/
theorem value_keyWL (d : Divide) :
    (keyWL d).value Reading.gl W =
      kfWL (readE d.zsl) (W.slot d.sACC) (W.slot d.sZO) (W.slot d.sZC) (W.slot d.sRH)
        (W.slot d.sRHP) (readE (sumW d.pwW)) := by
  simp only [keyWL, remForm, Aff.value_add, Aff.value_sub, Aff.value_scale, Aff.value_slot,
    Aff.value_ofConst, gl_val, readE_ofNat, readE_scaleNat, readE_sub, readE_one, kfWL]
  push_cast
  ring

/-- **padTerm, valued.** -/
theorem value_padTerm (c : ACall) (zk : Array E) :
    (padTerm c zk).value Reading.gl W =
      algebraMap Cb.Gl.F GE (toF (c.call.tauAt c.call.t0)) * (1 - readE (wall c zk)) := by
  simp only [padTerm, Aff.value_ofConst, gl_val, readE_scale, readE_sub, readE_one,
    Algebra.smul_def]

/-- **keyKFD, valued.** The public value is read off the port's own closed form. -/
theorem value_keyKFD (d : ShD) (k : Score) :
    (keyKFD d k).value Reading.gl W =
      kfKFD (W.slot k.s0) (W.slot (k.s0 + 1)) (W.slot (k.s0 + 2)) (W.slot (k.s0 + 3))
        (W.slot (k.s0 + 4)) (W.slot (k.s0 + 5)) (W.slot (k.s0 + 6))
        (if k.seg == Seg.fm then (d.C : GE) * readE (sumW k.pw) * readE (onesOf k.zs)
          else (d.Om : GE) * readE (sumW k.pw) * (1 - readE (leOf k.zj k.zi)))
        (readE (sumW k.pw)) := by
  by_cases hs : (k.seg == Seg.fm) = true
  · simp only [keyKFD, hs, if_true, Aff.value_add, Aff.value_sub, Aff.value_scale, Aff.value_slot,
      Aff.value_ofConst, gl_val, readE_ofNat, readE_scaleNat, readE_mul, kfKFD]
    push_cast
    ring
  · simp only [keyKFD, hs, Bool.false_eq_true, if_false, Aff.value_add, Aff.value_sub,
      Aff.value_scale, Aff.value_slot, Aff.value_ofConst, gl_val, readE_ofNat, readE_scaleNat,
      readE_mul, readE_sub, readE_one, kfKFD]
    push_cast
    ring

end OnBytes.Ends.A

#print axioms OnBytes.Ends.A.readE_ofNat
#print axioms OnBytes.Ends.A.value_keyKR
#print axioms OnBytes.Ends.A.value_keyWL
#print axioms OnBytes.Ends.A.value_keyKFD
