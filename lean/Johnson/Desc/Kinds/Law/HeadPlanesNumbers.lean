-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPlanesNumbers.lean: the two premises on numbers of
Law/HeadPlanesHost.lean and Law/RowPlanesHost.lean, as theorems, at every public record that
Verify.publicOf returns.

k6_host_planes asks of the plan's list of matrices: the planes' matrix has its rows in one block of
2 ^ lmbH, and at least the planes' columns. The library shows both of the head's plan in every
record that Verify.publicOf returns (Fo.PlaneMat.public_planeMatHB,
OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPub.lean), the second at the layout's own shape of the lookup
(HLy.fs). The form follows the layers' Johnson/Meaning/PlanesNumbers.lean.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  k6_numbers: both premises, at a lookup's record whose shape is the layout's.
  k6_host_planes_public: k6_host_planes_at without the two premises.
  rowPlanes_public: rowPlanes_host without the two premises.

Premises that nobody pays here. hsh: the shape in the lookup's record x.g1 is the layout's (HLy.fs):
the lookup's own block lays the shape of its place's parameters; that these are the layout's at the
head's link is the lookup's files' to show. hW: the public record is one that Verify.publicOf
returns. And those that stay of the two theorems: THE LAW OF THE READS, htr, hK0, h4, hlk, TabsLie.
Limits. As the two files'. No draw, no error term, nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.RowPlanesHost
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.NumsEq TwV Fo Meaning.Planes
open Cb.Fo.Pin
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8
open Planes

variable {pol KL : ByteArray} {layout : Option ByteArray} {W : OnBytes.Model.Verify.Public}

/-- **The two premises on numbers hold at every public record**, at a lookup's record with the
layout's shape. -/
theorem k6_numbers (hW : Verify.publicOf pol KL layout = .ok W) {g : Forest.Heard}
    (hsh : g.shape = W.HLy.fs) :
    (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).m / 2 ^ W.hS.lmbH = 1 ∧
      planeCols g.shape W.hS.lmbH ≤ (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).k := by
  have hB := Fo.PlaneMat.public_planeMatHB hW
  simp only [planeMatHB, Bool.and_eq_true, decide_eq_true_eq] at hB
  rw [hsh]
  exact ⟨hB.1.2, hB.2⟩

/-- **The three clauses at the seat's own reader, at a record in which the tables lie**, at a public
record. -/
theorem k6_host_planes_public {R : Type} [CommRing R] (ρ : Reading R)
    (hW : Verify.publicOf pol KL layout = .ok W) {s : S} {o : HeadOwn} {cov : Model.Head.Covered}
    {x : Model.Head.Heard} {t : Model.Head.Tables} (Z : TabsLie W.hS W.HLy W.H s o cov x t)
    (hsh : x.g1.shape = W.HLy.fs) (iU3 : Nat) {tr : HTree} (htr : o.F.trees[iU3]? = some tr)
    (hK0 : tr.K ≠ 0) {cellM : Nat → Nat → Nat → R}
    (ν : _root_.Fo.Pl → R)
    (h4 : ∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
      cellM (W.hS.NHf + 1 + 1) r c = ν (.cell r c))
    (Wd : World R)
    (hA : ReadsAll ρ o.tl.mats o.tl.funs Wd.entry iU3 tr.K cellM) :
    ∃ r, callerReaders (planesAt iU3) s = some r ∧
      K3HostPlanes x.g1.shape W.hS.lmbH (rdL ρ x.g1.zb0) (rdL ρ x.g1.zb1) ν
        (fun f => f.value ρ Wd) (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}) :=
  k6_host_planes_at ρ Z iU3 htr hK0 (k6_numbers hW hsh).1 (k6_numbers hW hsh).2 ν h4 Wd hA

/-- **The row's clause on "planes", at a record in which the tables lie**, at a public record. -/
theorem rowPlanes_public (hW : Verify.publicOf pol KL layout = .ok W) {sP : S} {o : HeadOwn}
    {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (Z : TabsLie W.hS W.HLy W.H sP o cov x t) (hlk : sP.look? = sP.lookHeard?)
    (hsh : x.g1.shape = W.HLy.fs) {tr : HTree} (htr : o.F.trees[readsOf W]? = some tr)
    (hK0 : tr.K ≠ 0) {cellM : Nat → Nat → Nat → K} (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
      cellM (W.hS.NHf + 1 + 1) r c = ν (.cell r c))
    (Wd : World K)
    (hA : ReadsAll Reading.gl o.tl.mats o.tl.funs Wd.entry (readsOf W) tr.K cellM) :
    K6OutP W W.hS.lmbH sP Wd ↔ K6InP W.hS.lmbH sP Wd ν :=
  rowPlanes_host W Z hlk htr hK0 (k6_numbers hW hsh).1 (k6_numbers hW hsh).2 ν h4 Wd hA

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_numbers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_host_planes_public
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_public
