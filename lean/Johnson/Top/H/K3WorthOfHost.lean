-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/K3WorthOfHost.lean: THE PLANES' ROW, THE LAST JOINT, WHATEVER THE CALLING KIND: from "the calling kind's readers read
truly" (K3HostPlanes, Johnson/Meaning/PlanesLaw.lean) and "the three claims of the lookup's run on the planes are worth 0" to the
table's item worth "planes" (K3WorthPlanes, Johnson/Top/H/K3Worth.lean). A joining of three other files: no new
mathematics.
  `k3OutPlanes_of_host`: K3PlanesPaid (Johnson/Top/H/K3LeftStatement.lean; had by k3PlanesPaid_of, Johnson/Top/H/K3OutPaid.lean) at a
    run of the planes' claims, a later ledger H, and K3HostPlanes at the heard record's own two points in H's world gives K3OutPlanes:
    K3HostPlanes' three fields ARE K3PlanesPaid's three premises on the calling kind.
  `k3WorthPlanes_of_host`: so the item, at a record that holds that ledger and that heard record.
Limits. A RULE OVER LETTERS. The ledger F0 at which the run is said to have run (K3RanAt) is asked to be the ledger that the record s
holds. Nothing says who pays K3RanAt, "later", the claims' worth or K3HostPlanes. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutPaid
import Johnson.Top.H.K3Worth
import Johnson.Meaning.PlanesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open Meaning.Planes (K3HostPlanes)

section
variable {S Cl W : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard) (form : Cl → Aff) (lm : ℕ)

theorem k3OutPlanes_of_host {planes : ℕ → S → Except String (List Cl × S)} {bit : S → ℕ → ℕ → Aff} {pin : S → ℕ → Aff}
    (hPaid : K3PlanesPaid fork heard form lm planes bit pin) {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)
    (g : Forest.Heard) (F0 : Fork) (first : ℕ) (sP : S) (clP : List Cl) (GP H : Fork) (ν : _root_.Fo.Pl → K)
    (entry : ℕ → ℕ → ℕ → K) (hok : FoNums.ok g.shape = true) (hran : K3RanAt fork heard g F0 planes sP clP GP)
    (hl : _root_.Fo.Later GP H)
    (hz : ∀ c ∈ clP, (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0)
    (hh : K3HostPlanes g.shape lm (rdA ρ g.zb0) (rdA ρ g.zb1) ν
      (fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) (bit sP) (pin sP)) :
    K3OutPlanes g.shape lm first ν ρ g F0 :=
  hPaid K ρ g F0 first sP clP GP H ν entry hok hran hl hz hh.bit0 hh.bit1 hh.pin

theorem k3WorthPlanes_of_host {planes : ℕ → S → Except String (List Cl × S)} {bit : S → ℕ → ℕ → Aff} {pin : S → ℕ → Aff}
    (hPaid : K3PlanesPaid fork heard form lm planes bit pin) (first : ℕ) (nu : W → _root_.Fo.Pl → Cb.Gl.E) {s : S} {w : W}
    {g : Forest.Heard} {F0 : Fork} (hf : fork s = some F0) (hg : heard s = some g) (sP : S) (clP : List Cl) (GP H : Fork)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (hok : FoNums.ok g.shape = true) (hran : K3RanAt fork heard g F0 planes sP clP GP)
    (hl : _root_.Fo.Later GP H)
    (hz : ∀ c ∈ clP, (form c).value Reading.gl (H.worldOf Reading.gl (fun j => nu w (.mask j)) entry) = 0)
    (hh : K3HostPlanes g.shape lm (rdA Reading.gl g.zb0) (rdA Reading.gl g.zb1) (nu w)
      (fun f => f.value Reading.gl (H.worldOf Reading.gl (fun j => nu w (.mask j)) entry)) (bit sP) (pin sP)) :
    K3WorthPlanes fork heard g.shape lm first nu s w :=
  k3WorthPlanes_of_out fork heard g.shape lm first nu hf hg
    (k3OutPlanes_of_host fork heard form lm hPaid Reading.gl g F0 first sP clP GP H (nu w) entry hok hran hl hz hh)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3OutPlanes_of_host
#print axioms VerifiableInference.OnPublicFiles.k3WorthPlanes_of_host
