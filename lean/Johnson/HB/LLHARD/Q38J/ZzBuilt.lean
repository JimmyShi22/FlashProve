-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/HB/LLHARD/Q38J/ZzBuilt.lean: under the head, the parameters of the approximate range
proof that the lookups read at a segment are the built segment's own.

Why. `DigAheadOk` names the digits' array by `tl.ix.ZZ`, at the parameters tl that
`digAt` returns. The field "near" of the condition on the approximate range proof names it by
`Xl.tl.ix.ZZ`, at the built segment Xl. The join wants the two numbers to be one.

What is shown.
  `j_tl_built`: what `Look.tlAt (At.X Zp) l` returns is `Xl.tl`. By `IM.ground_tails`
    (Johnson/IMR/K8Seat.lean) and the two numbers of the scope (attention is covered; twelve groups:
    `publicO_at_scope`): three cases on l.
  `j_zz_built`: **`tl.ix.ZZ = Xl.tl.ix.ZZ`** where `digAt (At.X Zp) l = some (x, tl)`: `digAt` lays
    one field of these parameters anew, and not that one.

Grade. From the head alone.

Limits. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). The full size alone. Nothing on soundness.


-/
import Johnson.P5J.MgAtAll
import Johnson.IMR.K8Seat
import Johnson.Desc.First.Look.K3CallerTests
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Q38

open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- What the lookups' reader of the parameters returns is the built segment's. -/
theorem j_tl_built (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {tl' : HTailF2}
    (ht : VerifiableInference.Desc.First.Look.tlAt (P5J.At.X Zp) l = some tl') : tl' = Xl.tl := by
  obtain ⟨hT, Xh, eh, th, -⟩ := IM.ground_tails h.scope h.reads h.laid.pub hG
  have eW : G.W = P5J.At.X Zp := ProofFile.Law.blankBy_W hG
  have F := H2K.Sizes.publicO_at_scope h.scope h.laid.publicO
  have F4 : (P5J.At.X Zp).p4 = true := F.p4
  have FG : (P5J.At.X Zp).NGr = 12 := F.groups
  unfold VerifiableInference.Desc.First.Look.tlAt at ht
  rw [F4, FG] at ht
  have ht' : (if (l == 2 * 12) = true then some (P5J.At.X Zp).H.tl
      else if (l % 2 == 0) = true then (P5J.At.X Zp).G[l / 2]?.map (·.tl)
      else (P5J.At.X Zp).A[l / 2]?.map (·.seam.tl)) = some tl' := ht
  by_cases h24 : l = 24
  · subst h24
    rw [if_pos (by decide : ((24 : ℕ) == 2 * 12) = true)] at ht'
    obtain rfl : Xh = Xl := Option.some.inj (eh.symm.trans e3)
    rw [← Option.some.inj ht', th, eW]
  · rw [if_neg (fun c => h24 (by simpa using c))] at ht'
    by_cases he : l % 2 = 0
    · rw [if_pos (by simpa using he)] at ht'
      obtain ⟨hp, ehp, rfl⟩ := Option.map_eq_some_iff.1 ht'
      obtain ⟨hp', -, x1, -, e1, -, e2, t2, -⟩ := hT (l / 2) (by omega)
      rw [eW] at e1
      obtain rfl : hp' = hp := Option.some.inj (e1.symm.trans ehp)
      rw [show 2 * (l / 2) = l by omega] at e2
      obtain rfl : x1 = Xl := Option.some.inj (e2.symm.trans e3)
      exact t2.symm
    · rw [if_neg (by simpa using he)] at ht'
      obtain ⟨a, ea, rfl⟩ := Option.map_eq_some_iff.1 ht'
      obtain ⟨-, a', -, x2, -, e1, -, -, -, -, -, -, e2, t2, -⟩ := hT (l / 2) (by omega)
      rw [eW] at e1
      obtain rfl : a' = a := Option.some.inj (e1.symm.trans ea)
      rw [show 2 * (l / 2) + 1 = l by omega] at e2
      obtain rfl : x2 = Xl := Option.some.inj (e2.symm.trans e3)
      exact t2.symm

/-- **The digits' array bears one number in both writings.** -/
theorem j_zz_built (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hx : VerifiableInference.Desc.First.Look.digAt (P5J.At.X Zp) l = some (x, tl)) :
    tl.ix.ZZ = Xl.tl.ix.ZZ := by
  unfold VerifiableInference.Desc.First.Look.digAt at hx
  obtain ⟨x', -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨tl', ht', hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨sh, -, hx⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨-, rfl⟩ := Prod.mk.inj hx
  show tl'.ix.ZZ = Xl.tl.ix.ZZ
  rw [j_tl_built h hG hl e3 ht']

end Q38

#print axioms Q38.j_tl_built
#print axioms Q38.j_zz_built
