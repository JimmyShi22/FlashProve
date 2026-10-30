-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/AtS.lean: THE SEAT OF THE SMALLNESS TEST's FIRST HALF
  (Johnson/Desc/First/K8/Hear.lean) AT THE FIRST CHAIN's CARRIED RECORD
  (Johnson/Desc/First/State.lean). NO PART OF THE KIND's TEXT: where the places behind this one
  are `verify-on-bytes`'s, they read ITS record of the smallness test out of S: so what was heard is
  laid in that record's two fields, and what the kind asks is read off that record. Eight readings
  and one writing; no test lives here, but that a link is open (else every reading says "refuse").


-/
import Johnson.Desc.First.State
import Johnson.Desc.First.K8.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- The seat at S. Outside a link: closed = false and drawn = true: the kind refuses. -/
def atS : Seat S where
  closed s := (s.tl?.map (·.funClosed)).getD false
  nothingOwed s := s.closeOk
  drawn s := (s.tl?.map fun tl => !tl.cfF.isEmpty || tl.foldDrawn != 0).getD true
  matrices s := (s.tl?.map (·.NM)).getD 0
  ks s := (s.tl?.map fun tl => tl.mats.toList.map (·.k)).getD []
  ms s := (s.tl?.map fun tl => tl.mats.toList.map (·.m)).getD []
  tau s := (s.tl?.map (·.tau)).getD 0
  tabs s := (s.tl?.map fun tl => tl.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)).getD []
  lay s m first :=
    match s.tl? with
    | some tl => .ok (s.putTl { tl with cfF := m, cfFirst := first })
    | none => .error "the smallness test: no link is open"

end VerifiableInference.Desc.First.K8
