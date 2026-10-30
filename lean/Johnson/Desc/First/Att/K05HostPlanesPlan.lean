-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05HostPlanesPlan.lean: THE ROW K05_host_planes (Johnson/Desc/First/Att/K05HostPlanes.lean) AT A STORED PLAN: at every A with OfPlan A
(Johnson/Desc/First/Att/Claims/OfPlan.lean: the planner's return but for one field; that file's public_ofPlan: every attention plan X.A[g] of a return X of Verify.publicOf is so), at the claims' seat
seatCO (parCOf A) over the first chain's record: SIX OF ITS PUBLIC PREMISES FALL: hgeo · hmats (by the make) · hs (ofPlan_shape) · hm (matsFit_of_plan,
Johnson/Desc/First/Att/GuardPlan.lean, carried over the field) · hrows (ofPlan_rows) · lid | cf are no letters any more.
LEFT OF THE PUBLIC ONES: hp (PosG: a test of the kind's guard) · hok (FoNums.ok of the heard shape) · hsh (the heard shape is the plan's).
  `ofPlan_matsFit` · `K05_host_planes_plan`.
Limits: as that file's. NO MEMBER. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05HostPlanes
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.Desc.First.Att.GuardPlan
import Johnson.Desc.First.Att.SeatO

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf LookIn SeatC ParC)
open VerifiableInference.OnPublicFiles (K3PlanesPaid K3RanAt K3WorthPlanes)

theorem ofPlan_matsFit {A : Attention.Plan} (h : OfPlan A) : MatsFit A.S A.seam.tl := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := P.matsFit_of_plan (X := A0) h0
  exact ⟨h1, h2, h3, h4, h5⟩

theorem K05_host_planes_plan {Cl W : Type} {A : Attention.Plan} (hA : OfPlan A) {gL : Forest.Heard}
    (fork : First.S → Option Fork) (heard : First.S → Option Forest.Heard) (form : Cl → Aff)
    {planes : ℕ → First.S → Except String (List Cl × First.S)} {bit : First.S → ℕ → ℕ → Aff} {pin : First.S → ℕ → Aff}
    (hPaid : K3PlanesPaid fork heard form A.S.cf.lmb planes bit pin) (sP : First.S)
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hp : PosG (geoOf A.S))
    (hr : P.readersOfO A sP = some r)
    (hlook : (P.seatCO (P.parCOf A)).look sP = some (P.lookOf A.S.cf.lmb gL))
    (hr0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.1 0 col).isSome)
    (hr1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.1 1 col).isSome)
    (hrP : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.2 col).isSome)
    (hsh : gL.shape = A.fs)
    (hbit : bit sP = fun e col => (r.1 e col).getD (Aff.ofConst zeroE))
    (hpin : pin sP = fun col => (r.2 col).getD (Aff.ofConst zeroE))
    (first : ℕ) (nu : W → _root_.Fo.Pl → Cb.Gl.E) {s : First.S} {w : W} {F0 : Fork} (hf : fork s = some F0)
    (hg : heard s = some gL) (clP : List Cl) (GP H : Fork) (hok : FoNums.ok gL.shape = true)
    (hran : K3RanAt fork heard gL F0 planes sP clP GP) (hl : _root_.Fo.Later GP H) (M : Mats Cb.Gl.E)
    (h4 : ∀ r < 2 ^ A.S.cf.lmb, ∀ c < Fo.planeCols gL.shape A.S.cf.lmb, M (A.S.cf.NAs + 2) r c = nu w (.cell r c))
    (hz : ∀ i K, P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) sP = some (i, K) → ∀ x ∈ clP, (form x).value Reading.gl
      (H.worldOf Reading.gl (fun j => nu w (.mask j))
        (entryOf Reading.gl A.seam.tl K M (oldOf A.S gL i).t.funs.toList)) = 0) :
    K3WorthPlanes fork heard gL.shape A.S.cf.lmb first nu s w := by
  obtain ⟨lid, cf, hid⟩ := ofPlan_shape hA
  exact K05_host_planes (tl := A.seam.tl) (S := A.S) fork heard form hPaid (P.seatCO (P.parCOf A)) (P.parCOf A) sP rfl rfl hp hr
    hlook hr0 hr1 hrP hid (ofPlan_matsFit hA) hsh (ofPlan_rows hA) hbit hpin first nu hf hg clP GP H hok hran hl M h4 hz

end K5Law

#print axioms K5Law.ofPlan_matsFit
#print axioms K5Law.K05_host_planes_plan
