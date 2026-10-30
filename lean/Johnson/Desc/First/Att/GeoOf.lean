-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/GeoOf.lean: the place's numbers (Att/Geo.lean) out of OnBytes/Model's shape of an
attention sub-proof, field for field: no test, no arithmetic. A bridge; no part of the kind's text.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Geo
import OnBytes.Model.AttentionShape

set_option autoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Attention

def keysOf : Seg → Keys
  | .rm => .rm | .rd => .rd | .fm => .fm | .fd => .fd | .wl => .wl | .wh => .wh | .ix => .ix
def tabOf : Table → Tab
  | .kr => .kr | .kfd => .kfd | .r16 => .r16 | .wh => .wh
def tenOf (X : Model.TenAt) : Ten := { off := X.off, nl := X.nl, cnt := X.cnt, J := X.J }
def callOf (c : ACall) : CallG :=
  { tab := tabOf c.kind, sh := c.sh, n := c.call.n, t0 := c.call.t0, tau := c.call.tau, lists := c.segs.map keysOf
    pcs := c.pcs.toList.map fun pc => { keys := keysOf pc.seg, lam := pc.lam, a := pc.a, b := pc.b, off := pc.off } }
def geoOf (S : Shape) : Geo :=
  { lt := S.cf.lt, lB := S.cf.lB, lgk := S.cf.lgk, ldh := S.cf.ldh, lmS := S.cf.lmS, la := S.cf.la, lmb := S.cf.lmb, H := S.cf.H, NAs := S.cf.NAs
    T := S.T, B := S.B, nT := S.nT, hP := S.hP, G := S.G, HA := S.HA, dh := S.dh, dq := S.dq, Lam := S.Lam, u0 := S.u0, lnT := S.lnT
    nM := S.nM, nD := S.nD, ls := S.ls, kAs := S.kAs, kbA := S.kbA, fillH := S.fillH, fillO := S.fillO, fillQ := S.fillQ
    oMr := S.oMr, oZr := S.oZr, oIb := S.oIb, oRh := S.oRh, oRhp := S.oRhp, Smax := S.Smax
    atQ := tenOf S.atQ, atK := tenOf S.atK, atV := tenOf S.atV, atO := tenOf S.atO, calls := S.calls.map callOf }

end VerifiableInference.Desc.First.Att.P
