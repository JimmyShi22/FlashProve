-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/LookKeys.lean: kind K5: ONE premise on the lookup's side in the place
of three: where each call's key point is the lookup's cut of its end point, (the last iota
coordinates of zy | zx), and the library's z reads as (zx | zy): Look and EndsIn
(Johnson/Desc/First/Att/Claims/PointsTie.lean) and KeyPt
(Johnson/Desc/First/Att/Claims/PiecesTie.lean) follow.

Main names:
  `LookAll ρ fs zx zy p`: zx has dT and zy rK coordinates; the library's z is (zx | zy), read.
  `KeyIs fs zx zy key c`: key is (the last iota_c coordinates of zy | zx): the array of
    OnBytes/Model/Look.lean:411, as Johnson/Road/Lane5ZkZc.lean types it.
  `look_of`, `endsIn_of`, `keyPt_of`: the three. keyPt_of is the twin, for any reading, of
    zk_eq_zC_of_fit (Johnson/Road/Lane5ZkZc.lean), whose proof it follows.
Limit: that the record which the lookup's kind hands on holds these arrays under zk is that kind's
to show.
Used: CallsFit, callsFit_iota; pt, pt_extract.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PointsTie
import Johnson.Desc.First.Att.Claims.PiecesTie

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Pub Calls)

variable {Kf : Type} [Field Kf]

/-- The lookup's end point, and the library's z. -/
structure LookAll (ρ : Reading Kf) (fs : Model.Forest.Shape) (zx zy : Array E) (p : Pub Kf) :
    Prop where
  sx : zx.size = fs.dT
  sy : zy.size = fs.rK
  z : ∀ t, p.z t = pt ρ (zx ++ zy) t

/-- The key point of call c is the lookup's cut of its end point. -/
def KeyIs (fs : Model.Forest.Shape) (zx zy key : Array E) (c : Fin 4) : Prop :=
  key = zy.extract (fs.rK - fs.iota.getD c.val 0) zy.size ++ zx

theorem pt_append (ρ : Reading Kf) (a b : Array E) (i : ℕ) :
    pt ρ (a ++ b) i = if i < a.size then pt ρ a i else pt ρ b (i - a.size) := by
  unfold pt
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split_ifs <;> rfl

variable {ρ : Reading Kf} {fs : Model.Forest.Shape} {zx zy : Array E} {p : Pub Kf}

theorem look_of (A : LookAll ρ fs zx zy p) : Look ρ fs zx p :=
  ⟨A.sx, fun t ht => by rw [A.z, pt_append, if_pos (by rw [A.sx]; exact ht)]⟩

theorem endsIn_of {key : Array E} {c : Fin 4} (K : KeyIs fs zx zy key c) : EndsIn key zx := ⟨_, K⟩

/-- **The key point of call c, read, is the library's.** -/
theorem keyPt_of {S : Attention.Shape} (hF : L5.CallsFit S fs) (A : LookAll ρ fs zx zy p)
    {key : Array E} {c : Fin 4} (K : KeyIs fs zx zy key c) : KeyPt ρ fs key c p := by
  obtain ⟨hi, hle⟩ := L5.callsFit_iota hF c
  have hD : (L5.callsOf fs).Dk ≤ (L5.callsOf fs).a c := hF.2.1 c
  have hDk : (L5.callsOf fs).Dk = fs.dT := rfl
  have hsg : (L5.callsOf fs).sg = fs.rK := rfl
  have he : (L5.callsOf fs).e c = (L5.callsOf fs).a c - (L5.callsOf fs).Dk := rfl
  have hx := A.sx
  have hy := A.sy
  have hs : (zy.extract (fs.rK - (L5.callsOf fs).e c) zy.size).size = (L5.callsOf fs).e c := by
    rw [Array.size_extract, hy]
    omega
  unfold KeyIs at K
  rw [hi] at K
  subst K
  refine ⟨?_, fun t ht => ?_⟩
  · rw [Array.size_append, hs, hx]
    omega
  · rw [pt_append, hs]
    unfold Calls.zC
    by_cases h : t < (L5.callsOf fs).e c
    · rw [if_pos h, if_pos h, pt_extract ρ _ (Nat.le_refl _) (by rw [hy]; omega), A.z, pt_append,
        hx, hDk, hsg, if_neg (by omega)]
      congr 1
      omega
    · rw [if_neg h, if_neg h, A.z, pt_append, hx, if_pos (by omega)]

end K5Law

#print axioms K5Law.keyPt_of
