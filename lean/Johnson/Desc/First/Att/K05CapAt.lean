-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05CapAt.lean: the premises of K05_cap and K05_row on public numbers, as one
record; and
how much of it follows wherever the verifier's own function shape has returned the shape.

Main names:
  `CapAt P0 S p rows u1 u2`: kap = 4 · the plan's record is recOf P0 rows · the description's sizes
    are L5.dimOf S ·
    Sizes S · three equations of numbers · the place has two units, the first below the diagonal,
      the second on it.
  `K05_cap_at`, `K05_row_at`: the two theorems under CapAt.
  `capAt_of_shape`: Attention.shape cf = .ok S gives Sizes S and the three equations of numbers, at
    every cf. What
    is left of CapAt: kap = 4 and P0.D = L5.dimOf S (both hold of Att/K05Caller.lean's callerOf by
      definition), the
    plan's record, the two units.

Limits: the plan's record (Johnson/Road/Rows/PlaceAtt.lean [not in this library] tests
it by evaluation), the two units (a
fact on the
calls that shape lays) and an instance at a stored configuration are not shown in this file or in
what it imports.
Sources: Johnson/Road/Lane5AttShape.lean (Shaped, shaped_of_shape); Rows/AttReadLong.lean (Sizes,
sizes_of_shape).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5AttShape
import Johnson.Desc.First.Att.K05Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (recOf)

variable {K : Type} [Field K] [Fintype K] {M0 X : Type}

/-- **The premises on public numbers.** -/
structure CapAt (P0 : OwnPar K M0 X) (S : Attention.Shape) (p : Par) (rows : ℕ) (u1 u2 : UnitG) : Prop where
  kap : P0.kap = 4
  record : p.own = recOf P0 rows
  dim : P0.D = OnBytes.Road.L5.dimOf S
  sizes : OnBytes.Road.Rows.Sizes S
  lt : S.cf.lt = P0.D.lT
  np : (geoOf S).NP = (size18 P0.D).pairs
  np2 : S.NP = P0.D.nb
  units : (geoOf S).scores = [u1, u2]
  below : u1.below = true
  on : u2.below = false

theorem K05_cap_at (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {St : Type} (seat : Seat St) (p : Par) (s s' : St)
    (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s') (hz : ∀ F, seat.ledger s = some F → Sized F)
    {S : Attention.Shape} {rows : ℕ} {u1 u2 : UnitG} (c : CapAt P0 S p rows u1 u2) (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        CapSays (closedOf P0 Λ F.ns (numsPlan p.own F.next)) Λ.maskOf p.own F G' rs h
          (fun l => leftP (geoOf S) zk h G' = some l) (LookAll P0 S zk u1 u2) :=
  K05_cap P0 Λ seat p s s' rs hd hz c.kap rows c.record S c.dim c.sizes c.lt c.np c.units c.below c.on zk

theorem K05_row_at (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {St : Type} (seat : Seat St) (p : Par) (s s' : St)
    (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s') (hz : ∀ F, seat.ledger s = some F → Sized F)
    {S : Attention.Shape} {rows : ℕ} {u1 u2 : UnitG} (c : CapAt P0 S p rows u1 u2) (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        RowSays (closedOf P0 Λ F.ns (numsPlan p.own F.next)) Λ.maskOf p.own F G' rs h S zk
          (LookAll P0 S zk u1 u2) :=
  K05_row P0 Λ seat p s s' rs hd hz c.kap rows c.record S c.dim c.sizes c.lt c.np c.np2 c.units c.below c.on zk

/-- **Wherever the verifier's function shape has returned S.** -/
theorem capAt_of_shape {cf : Attention.Cfg} {S : Attention.Shape} (h : Attention.shape cf = Except.ok S)
    (P0 : OwnPar K M0 X) (hk : P0.kap = 4) (hD : P0.D = OnBytes.Road.L5.dimOf S) (p : Par) (rows : ℕ)
    (hrec : p.own = recOf P0 rows) {u1 u2 : UnitG} (hu : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true)
    (hb2 : u2.below = false) : CapAt P0 S p rows u1 u2 := by
  have Z := OnBytes.Road.Rows.sizes_of_shape h
  have Sh := OnBytes.Road.L5.shaped_of_shape h
  have hl := Z.lnT
  refine ⟨hk, hrec, hD, Z, ?_, ?_, ?_, hu, hb1, hb2⟩
  · rw [hD]
    show S.cf.lt = S.lnT - 1 + 1 + S.cf.lB
    have e1 := Sh.lnT
    rw [← Sh.cfg] at e1
    omega
  · rw [hD]
    rfl
  · rw [hD]
    rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_row_at
#print axioms VerifiableInference.Desc.First.Att.P.capAt_of_shape
