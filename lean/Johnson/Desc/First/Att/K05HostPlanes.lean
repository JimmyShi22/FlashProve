-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05HostPlanes.lean: THE ROW K05_host_planes: kind K5 PAYS THE TABLE OF JOINTS' ITEM worth "planes" OF AN ATTENTION
SEGMENT's LOOKUP ON THE CALLS (K3WorthPlanes, Johnson/Top/H/K3Worth.lean), FROM "THE THREE CLAIMS OF THE LOOKUP's RUN ON THE PLANES ARE WORTH 0
IN THE STATED WORLD": the world of a later ledger in which each entry of the array of the reads is read as its stated function of the
matrices (entryOf): which is how the table's item formsT reads the forms.
A joining of k5_host_planes_stated (Johnson/Desc/First/Att/Claims/PlanesStated.lean: "the caller's readers read truly" there, by the choice of
the entries) with k3WorthPlanes_of_host (Johnson/Top/H/K3WorthOfHost.lean).
  `K05_host_planes`: the statement. ITS PREMISES, BY SORT AND PAYER:
    PUBLIC (the plan's): hgeo · hmats · hp (PosG) · hs (shapeHid's return) · hm (MatsFit) · hrows · hok (FoNums.ok) · hsh (the heard shape is the
      plan's: the lookup's promise behind its block has it).
    ON THE RECORD sP AT WHICH THE RUN IS READ: hr · hr0 · hr1 · hrP (the kind's two readers return, at every column) · hlook (what the lookup
      hands the tables).
    THE LOOKUP's FILES': hPaid (K3PlanesPaid, Johnson/Top/H/K3LeftStatement.lean: had by k3PlanesPaid_of, Johnson/Top/H/K3OutPaid.lean) AT THE KIND's READERS (hbit · hpin: its letters bit | pin at sP are what
      the kind's readers return) · hran (the run ran: K3RanAt) · hl (H is a later ledger) · hf · hg (the record s holds that ledger and that
      heard record).
    THE DICTIONARIES: hz (the claims are worth 0 in the stated world: from the item formsT m 2 "planes") · h4 (the planes' matrix of M IS the
      lookup's places nu w).
Limits. A RULE OVER LETTERS; NO MEMBER. K is the run's own number of columns: the stated world of the table's filling has the plan's: that the
two are one is asked of whoever calls this (a clause of the promise). THAT THE COMMITTED ARRAY HOLDS THE STATED ENTRIES IS NOT TOUCHED: it is
the table's item tie. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.PlanesStated
import Johnson.Top.H.K3WorthOfHost

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf LookIn SeatC ParC)
open VerifiableInference.OnPublicFiles (K3PlanesPaid K3RanAt K3WorthPlanes k3WorthPlanes_of_host)

theorem K05_host_planes {St Cl W : Type} {tl : HTailF2} {S : Attention.Shape} {gL : Forest.Heard}
    (fork : St → Option Fork) (heard : St → Option Forest.Heard) (form : Cl → Aff)
    {planes : ℕ → St → Except String (List Cl × St)} {bit : St → ℕ → ℕ → Aff} {pin : St → ℕ → Aff}
    (hPaid : K3PlanesPaid fork heard form S.cf.lmb planes bit pin)
    (seat : SeatC St) (c : ParC) (sP : St)
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (hgeo : c.geo = geoOf S) (hmats : c.mats = matsOf tl.mats) (hp : PosG c.geo)
    (hr : P.readersOfK seat c sP = some r) (hlook : seat.look sP = some (P.lookOf S.cf.lmb gL))
    (hr0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.1 0 col).isSome)
    (hr1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.1 1 col).isSome)
    (hrP : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - S.cf.lmb) → (r.2 col).isSome)
    (hs : Attention.shapeHid lid cf = .ok (S, fs)) (hm : MatsFit S tl) (hsh : gL.shape = fs)
    (hrows : (tl.mats.getD (S.cf.NAs + 2) {}).m = 2 ^ S.cf.lmb)
    (hbit : bit sP = fun e col => (r.1 e col).getD (Aff.ofConst zeroE))
    (hpin : pin sP = fun col => (r.2 col).getD (Aff.ofConst zeroE))
    (first : ℕ) (nu : W → _root_.Fo.Pl → Cb.Gl.E) {s : St} {w : W} {F0 : Fork} (hf : fork s = some F0)
    (hg : heard s = some gL) (clP : List Cl) (GP H : Fork) (hok : FoNums.ok gL.shape = true)
    (hran : K3RanAt fork heard gL F0 planes sP clP GP) (hl : _root_.Fo.Later GP H) (M : Mats Cb.Gl.E)
    (h4 : ∀ r < 2 ^ S.cf.lmb, ∀ c < Fo.planeCols gL.shape S.cf.lmb, M (S.cf.NAs + 2) r c = nu w (.cell r c))
    (hz : ∀ i K, P.inOf seat c sP = some (i, K) → ∀ x ∈ clP, (form x).value Reading.gl
      (H.worldOf Reading.gl (fun j => nu w (.mask j)) (entryOf Reading.gl tl K M (oldOf S gL i).t.funs.toList)) = 0) :
    K3WorthPlanes fork heard gL.shape S.cf.lmb first nu s w := by
  obtain ⟨i, K, hi, Hh⟩ := k5_host_planes_stated (tl := tl) (S := S) (gL := gL) seat c sP hgeo hmats hp hr hlook hr0 hr1 hrP hs hm
    hsh hrows
  refine k3WorthPlanes_of_host fork heard form S.cf.lmb hPaid first nu hf hg sP clP GP H
    (entryOf Reading.gl tl K M (oldOf S gL i).t.funs.toList) hok hran hl (hz i K hi) ?_
  rw [hbit, hpin]
  exact Hh M H (fun j => nu w (.mask j)) (nu w) h4

end K5Law

#print axioms K5Law.K05_host_planes
