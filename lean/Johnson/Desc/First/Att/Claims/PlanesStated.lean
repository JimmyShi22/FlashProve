-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PlanesStated.lean: kind K5: the kind's instance of the planes' law (K3HostPlanes, Johnson/Meaning/PlanesLaw.lean)
IN THE WORLD IN WHICH EACH ENTRY OF THE ARRAY OF THE READS IS READ AS ITS STATED FUNCTION OF THE MATRICES (entryOf,
Johnson/Desc/First/Att/Claims/TabsByChoice.lean): there the premise "the tables are true" (AttAt) of k5_host_planes_seat
(Johnson/Desc/First/Att/Claims/PlanesHost.lean) HOLDS BY THE CHOICE OF THE ENTRIES (attAt_tablesP, Johnson/Desc/First/Att/Claims/AttAtTables.lean).

Why. The table of joints' item "formsT" reads the forms so: "with each entry of the array that is committed LATER read as the stated function
of the cells". So at the border behind the kind's block the planes' row wants the instance AT THAT WORLD, and no tie to the smallness test's
block: THAT THE COMMITTED ARRAY HOLDS THESE ENTRIES IS ANOTHER ITEM OF THE TABLE (tie), opened and closed elsewhere: IT IS NOT SHOWN AND NOT
TOUCHED HERE.
  `k5_host_planes_stated`: over every seat: the readers' return at every column, the lookup's hand-over, three facts on public data
    (shapeHid's return · MatsFit · the planes' matrix has 2 ^ lmb rows) and PosG give: there are i and K, the run's own, with: for all matrices
    M, every ledger G, every mask and every reading ν of the places that is M's planes' matrix: K3HostPlanes in G's world at the entries
    entryOf gl tl K M (the kind's tables at i).
Limits. K IS THE RUN's OWN NUMBER OF COLUMNS (what the seat reads off the ledger): that it is the plan's is not said here. No member is shown.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.PlanesHost
import Johnson.Desc.First.Att.Claims.AttAtTables

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf LookIn SeatC ParC)
open Meaning.Planes (K3HostPlanes)

variable {tl : HTailF2} {S : Attention.Shape} {gL : Forest.Heard}

theorem k5_host_planes_stated {St : Type} (seat : SeatC St) (c : ParC) (s : St)
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (hgeo : c.geo = geoOf S) (hmats : c.mats = matsOf tl.mats) (hp : PosG c.geo)
    (hr : P.readersOfK seat c s = some r) (hlook : seat.look s = some (P.lookOf S.cf.lmb gL))
    (hr0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.1 0 col).isSome)
    (hr1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.1 1 col).isSome)
    (hrP : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.2 col).isSome)
    (hs : Attention.shapeHid lid cf = .ok (S, fs)) (hm : MatsFit S tl) (hsh : gL.shape = fs)
    (hrows : (tl.mats.getD (S.cf.NAs + 2) {}).m = 2 ^ S.cf.lmb) :
    ∃ i K, P.inOf seat c s = some (i, K) ∧
      ∀ (M : Mats Cb.Gl.E) (G : Fork) (mask : ℕ → Cb.Gl.E) (ν : _root_.Fo.Pl → Cb.Gl.E),
        (∀ r < 2 ^ S.cf.lmb, ∀ c < Fo.planeCols gL.shape S.cf.lmb, M (S.cf.NAs + 2) r c = ν (.cell r c)) →
        K3HostPlanes gL.shape S.cf.lmb (Fo.rdL Reading.gl gL.zb0) (Fo.rdL Reading.gl gL.zb1) ν
          (fun f => f.value Reading.gl
            (G.worldOf Reading.gl mask (entryOf Reading.gl tl K M (oldOf S gL i).t.funs.toList)))
          (fun e col => (r.1 e col).getD (Aff.ofConst zeroE)) (fun col => (r.2 col).getD (Aff.ofConst zeroE)) := by
  obtain ⟨i, K, hi, H⟩ := k5_host_planes_seat (tl := tl) (S := S) (gL := gL) (Kf := Cb.Gl.E) seat c s (lid := lid) (cf := cf)
    (fs := fs) hgeo hmats hp hr hlook hr0 hr1 hrP
  obtain ⟨eg, _, _, _, _, lk, _, ht⟩ := inOf_some seat c s i K hi
  have ht' : P.tablesP i.g (matsOf tl.mats) c.nW lk i.p = some i.t := by
    rw [eg, ← hmats]; exact ht
  exact ⟨i, K, hi, fun M G mask ν h4 =>
    H Reading.gl _ M ν (attAt_tablesP ht' hs hm K M G mask) hsh hrows h4⟩

end K5Law

#print axioms K5Law.k5_host_planes_stated
