-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReadsPublic.lean: the premises of Johnson/Meaning/ReadsPlan.lean's
`k4_host_planes_plan` on the plan and on the group's number, paid at a member of the list of plans.

The verifier's public record holds the plans of all layer sub-proofs as what Layer.plansG returns.
Every member of that list is what Layer.planG returns for its number (the library's plansG_at,
OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean), and the list has one member for each group (the library's
plansFrom_length, Johnson/Road/HeadDict.lean).

Main theorems (namespace `Meaning.Reads`).
  `plan_of_plansG`: a member number g of what plansG returns is planG's at g, and g is below the
      number of groups.
  `k4_host_planes_public`: `k4_host_planes_plan` at such a member.

Limits. That the public record's list of plans is what plansG returns at its own record of the
layers, and that this record's lists of matrices are tailsOf's, stand as premises (Verify.publicOf
lays both so, OnBytes/Model/VerifyPublic.lean, LayerPlan.lean, by reading). The other premises of
`k4_host_planes_plan` stay. Nothing on soundness.
-/
import Johnson.Meaning.ReadsPlan
import Johnson.Road.HeadDict
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf planG plansFrom plansG)
open OnBytes.K.Kc
open Meaning.Planes

/-- A member of the list of plans is planG's, and its number is a group's. -/
theorem plan_of_plansG {P : Pub} {G : Array HPlan2} (hG : plansG P = .ok G) {g : ℕ} {hp : HPlan2}
    (hg : G[g]? = some hp) : (∃ O, planG P g O = .ok hp) ∧ g < P.y.NGr := by
  refine ⟨⟨_, _root_.Fo.Pub.plansG_at P G hG g hp hg⟩, ?_⟩
  unfold plansG at hG
  obtain ⟨l, hl, h⟩ := Road.ok_of_bind hG
  have e : G = l.toArray := (Except.ok.inj h).symm
  rw [e, List.getElem?_toArray] at hg
  rw [← Road.Hd.plansFrom_length P _ 0 none l hl]
  exact (List.getElem?_eq_some_iff.mp hg).1

/-- **The three clauses at the layers' forms, at a member of the public list of plans.** -/
theorem k4_host_planes_public (ρ : Reading Cb.Gl.E) {P : Pub} {hp : HPlan2}
    {g : ℕ} {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) {G : Array HPlan2} (hG : plansG P = .ok G)
    (hgp : G[g]? = some hp)
    (zb0 zb1 : List Cb.Gl.E) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf (Closed.closedAt hp.tl (Closed.layShapes P g))))
    {x : Θ.X} {msg : Θ.M} (h : relIn Θ.letters x msg)
    (hphi : ∀ n Fn, o.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
      Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE))
    (W : World Cb.Gl.E)
    (hu : ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (hp.tl.mats.getD f.mat {}).k,
      ∀ sg < (hp.tl.mats.getD f.mat {}).m / f.len,
        Θ.u3 msg (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val W.entry o.v.iU3 o.v.K3
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg))
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN (Closed.closedAt hp.tl (Closed.layShapes P g)) Θ msg (matIx o.v.y).iB r c =
        ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨⟨O, hO⟩, hg⟩ := plan_of_plansG hG hgp
  exact k4_host_planes_plan ρ hh hq hT hg hO zb0 zb1 hz0 hz1 Θ h hphi W hu ν h4

#print axioms plan_of_plansG
#print axioms k4_host_planes_public

end Meaning.Reads
