-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeKeys.lean: the honest side of the kind "lookup"
(K3): what the lookup's row owes behind its sub-protocol: the item on the keys of the library's row
out. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: the item on the keys is `K3OutKeys`
(Johnson/Top/H/K3RowOut.lean). It says: the library's join, at the extension of each call's key
vector at that call's point, is 0. `Left` (Honest/K3/Law/LookLeftOf.lean) says what the lookup
leaves; `Dict` (Honest/K3/Law/Thread/ExchangeRows.lean) is `MasksAre`
(Honest/K3/Law/Statements.lean) at the mask entries of a reading. The joint key vector is
`OnBytes.Ends.jointKey` (OnBytes/Tie/Pv/Lookup/Ends/Joint.lean).

What is shown.
  1 `join_val`: on the library's side alone, in any field: what the join's form is worth, at a point
    given as one list, at key forms that are worth the calls' extensions, and at any number for
    the end form.
  2 `rdA_extract`, `rdA_append`, `toHeard_zk`, `zk_read`: the points of the program's structure,
    read as lists.
  3 `outKeys_of_worth`: the item. Conditional on `FoNums.ok h` and on one equation: the form left is
    worth alpha less the extension of the joint vector at the heard point.
  4 `outKeys_of_left`: the item, at every ledger later than the one behind the hearing. Conditional
    on `Left` at `keysOf D`, on `Dict`, on what was heard being the run's, and on the keys of D
    being the joint vector of the calls' vectors kv.

Hypotheses that remain.
  `hok`: `FoNums.ok h`.
  `hw`: (in `outKeys_of_worth`) the one equation on the worth of the form left; `hg`, `hk`, `hsz`
    tie the program's structure, the point and the form to what was heard.
  In `outKeys_of_left`:
  `hLeft`: `Left` at `Spec.keysOf D` (Honest/K3/Law/SpecLawful.lean).
  `hD`: `Dict`.
  `hH`, `hP`: what was heard is the run's (`HeardIs`, Honest/K3/Law/Statements.lean; `PointsAgree`,
    Honest/K3/HeardLaw.lean).
  `hp`, `hv`: one part of keys, of the shape's size; D has that size.
  `hkey`: the keys of D are the joint vector of the calls' vectors kv.
  `hL`: the ledger F' is later than the ledger G behind the hearing.
  In `join_val`: `hlen`, `hKF`: the point has dT + rK coordinates; each call's form is worth the
    extension of its key vector at its point. `hc`: (in `zk_read`) c is a call's number.
On `hkey`, at the named kv. It is not to be had from a hypothesis of the form "there are key vectors
such that ...": whoever opens such a hypothesis holds some vectors, not those of which the item
speaks. It follows from the filling's own text, by unfolding, where the structure's keys are defined
as the joint vector of named vectors.

How the proof goes. The library shows the item from one equation on the worth of the form that the
key tree leaves (`k3KeysHanded`, Johnson/Top/H/K3OutPaid.lean). `Left` says what that form is worth:
alpha less the extension of the one joint key vector at the tree's last point. Between the two
stands the join's algebra: the extension of the joint vector splits by calls and trees of padding
(`Fo.join_form_gap`, OnBytes/Tie/Pv/Lookup/Forest/FoGaps.lean).

Users. Honest/K3/Law/Thread/JoinBracket.lean [not in this library] calls `join_val`, `rdA_extract`
and `zk_read`.

Limits. One part of keys: a proof file's lookup. No instance of these hypotheses is exhibited in
this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRows
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecCourse
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecCongr
import Johnson.Top.H.K3OutPaid
import Johnson.HonestTrace.LookClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.Model.Forest (Shape)
open OnBytes.Slice (GE)
open OnBytes.HonestTrace.Look (Data)
open VerifiableInference.Desc.K3 (HeardV toHeard toHeardG)
open VerifiableInference.OnPublicFiles (K3OutKeys k3KeysHanded laterFo_of_psc)
open _root_.Fo (AffK joinK eK zk extL ptL rdA)

/-! ## 1 What the join's form is worth -/

/-- **What the join's form is worth**: alpha less the extension of the joint key vector at the
point, less the number that stands for the end form. Here ρ is the point as one list, the
highest variable first. -/
theorem join_val {K P : Type} [Field K] (h : FoNums.Sh) (hok : FoNums.ok h = true)
    (kv : Nat → Nat → K)
    (θ al : K) (ρ : List K) (hlen : ρ.length = h.dT + h.rK) (ν : P → K) (KF : Nat → AffK P K)
    (hKF : ∀ c, c < h.NC → AffK.val (KF c) ν =
      extL (kv c) (zk h.rK (h.iota.getD c 0) (ρ.take h.dT) (ρ.drop h.dT))) (worth : K) :
    AffK.val (joinK h θ al (eK h (ρ.drop h.dT)) (ρ.drop h.dT) KF (AffK.ofConst worth)) ν =
      al - Blocks.ext h.v (OnBytes.Ends.jointKey h kv θ) (ptL ρ) - worth := by
  have hrho : _root_.Fo.rhoP (h.dT + h.rK) (ptL ρ) = ρ := by
    rw [← hlen]
    exact _root_.Fo.rho_ptL _
  have hzx : _root_.Fo.zxOf h (⟨ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) = ρ.take h.dT := by
    show (_root_.Fo.rhoP (h.dT + h.rK) (ptL ρ)).take h.dT = _
    rw [hrho]
  have hzy : _root_.Fo.zyOf h (⟨ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) = ρ.drop h.dT := by
    show (_root_.Fo.rhoP (h.dT + h.rK) (ptL ρ)).drop h.dT = _
    rw [hrho]
  have hK0 : _root_.Fo.KFokAt h (fun _ : Fin 0 → K => kv)
      (_root_.Fo.zkOf h (⟨ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)))
      (fun c => AffK.ofConst
        (extL (kv c) (zk h.rK (h.iota.getD c 0) (ρ.take h.dT) (ρ.drop h.dT)))) (fun _ => 0) := by
    intro c _
    rw [AffK.val_ofConst]
    unfold _root_.Fo.zkOf
    rw [hzx, hzy]
    rfl
  have hC : _root_.Fo.CEok (⟨ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) al (AffK.ofConst al) :=
    by
    intro μ
    rw [AffK.val_ofConst]
    simp
  have g := _root_.Fo.join_form_gap (_root_.Fo.ok_prem hok) (fun _ : Fin 0 → K => kv) θ al
    (⟨ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) _ _ (fun _ => 0) hK0 hC
  rw [hzy, _root_.Fo.val_joinK] at g
  have hM : _root_.Fo.MGap (⟨ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) h.v
      (OnBytes.Ends.jointKey h kv θ) (fun _ => 0) =
      Blocks.ext h.v (OnBytes.Ends.jointKey h kv θ) (ptL ρ) := by
    unfold _root_.Fo.MGap
    simp
  rw [hM] at g
  simp only [AffK.val_ofConst] at g
  rw [_root_.Fo.val_joinK, AffK.val_ofConst,
    Finset.sum_congr rfl fun c hc => by rw [hKF c (Finset.mem_range.1 hc)]]
  linear_combination g

/-! ## 2 The program's structure's points, read as lists -/

theorem rdA_extract {K : Type} [CommRing K] (ρ : Reading K) (a : Array E) (i j : Nat) :
    rdA ρ (a.extract i j) = ((rdA ρ a).drop i).take (j - i) := by
  unfold rdA
  rw [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop]

theorem rdA_append {K : Type} [CommRing K] (ρ : Reading K) (a b : Array E) :
    rdA ρ (a ++ b) = rdA ρ a ++ rdA ρ b := by
  unfold rdA
  rw [Array.toList_append, List.map_append]

/-- The calls' points in the program's structure: the last coordinates of zy, then all of zx. -/
theorem toHeard_zk {h : Shape} {gV : HeardV} {g : OnBytes.Model.Forest.Heard}
    (hg : toHeard h (toHeardG gV) = some g) :
    g.zk = (Array.range h.NC).map fun c =>
      g.zy.extract (h.rK - h.iota.getD c 0) g.zy.size ++ g.zx := by
  unfold toHeard at hg
  have hk : (toHeardG gV).keys = gV.keys := rfl
  rw [hk] at hg
  match hkk : gV.keys, hg with
  | [(point, form)], hg =>
    simp only at hg
    split at hg
    · obtain rfl := Option.some.inj hg
      rfl
    · exact absurd hg (by simp)

/-- Call c's point, read. -/
theorem zk_read {K : Type} [CommRing K] (ρ : Reading K) {h : Shape} {gV : HeardV}
    {g : OnBytes.Model.Forest.Heard} (hg : toHeard h (toHeardG gV) = some g) (c : Nat)
    (hc : c < h.NC) :
    rdA ρ (g.zk.getD c #[]) = zk h.rK (h.iota.getD c 0) (rdA ρ g.zx) (rdA ρ g.zy) := by
  rw [toHeard_zk hg]
  have e : ((Array.range h.NC).map fun c =>
      g.zy.extract (h.rK - h.iota.getD c 0) g.zy.size ++ g.zx).getD c #[] =
      g.zy.extract (h.rK - h.iota.getD c 0) g.zy.size ++ g.zx := by
    simp [Array.getD, hc]
  rw [e, rdA_append, rdA_extract]
  unfold zk
  congr 1
  exact List.take_of_length_le (by simp [rdA])

/-! ## 3 The item, from one equation on the worth of the form left -/

/-- **The item on the keys.** Conditional on `FoNums.ok h` and on one equation. Here F' is the
ledger at which the item is asked, and point is the key tree's last point as the
description's structure has it. No instance of these hypotheses is exhibited in this file. -/
theorem outKeys_of_worth {h : Shape} {gV : HeardV} {g : OnBytes.Model.Forest.Heard}
    (hg : toHeard h (toHeardG gV) = some g) (hok : FoNums.ok h = true) (point : Array E)
      (form : Aff)
    (hk : gV.keys = [(point, form)]) (hsz : point.size = h.dT + h.rK) (F' : Fork) (lm first : Nat)
    (ν : _root_.Fo.Pl → GE) (entry : Nat → Nat → Nat → GE) (kv : Nat → Nat → GE)
    (hw : form.value Reading.gl (F'.worldOf Reading.gl (fun j => ν (.mask j)) entry) =
      Reading.gl.val gV.alpha - Blocks.ext h.v
        (OnBytes.Ends.jointKey h kv (Reading.gl.val gV.theta)) (ptL (rdA Reading.gl point))) :
    K3OutKeys h lm first ν kv Reading.gl g F' := by
  obtain ⟨point', form', hk', hs, _, ht, ha, hc, _, _, hzx, hzy⟩ := toHeard_parts hg
  obtain ⟨rfl, rfl⟩ : point' = point ∧ form' = form := by
    rw [hk] at hk'
    simpa [eq_comm] using hk'
  have hlen : (rdA Reading.gl point').length = h.dT + h.rK := by simp [rdA, hsz]
  have ezx : rdA Reading.gl g.zx = (rdA Reading.gl point').take h.dT := by
    rw [hzx, rdA_extract]
    simp
  have ezy : rdA Reading.gl g.zy = (rdA Reading.gl point').drop h.dT := by
    rw [hzy, rdA_extract]
    exact List.take_of_length_le (by simp [rdA])
  have key := k3KeysHanded GE Reading.gl lm g F' F' first ν entry kv (by rw [hs]; exact hok)
    (laterFo_of_psc (OnBytes.PscRun.Later.refl F')) (by
      rw [hs, ht, ha, hc, ezy,
        join_val h hok kv _ _ (rdA Reading.gl point') hlen ν _ (fun c hcN => by
          rw [AffK.val_ofConst, zk_read Reading.gl hg c hcN, ezx, ezy]), hw]
      ring)
  rw [hs] at key
  exact key

/-! ## 4 The item, from `Left` -/

/-- **The item on the keys of the row out**, at every ledger later than the one behind the hearing.
Conditional on `Left` at `keysOf D`, on `Dict`, on what was heard being the run's, and on the keys
of D being the joint vector of the calls' vectors kv. No instance of these hypotheses is exhibited
in this file. -/
theorem outKeys_of_left {W P : Type} (R : Course W) (planes : List (E × E) → GE) (D : Data P KE)
    (gV : HeardV) (G : Fork) (h : Shape) (g : OnBytes.Model.Forest.Heard)
    (hg : toHeard h (toHeardG gV) = some g) (hok : FoNums.ok h = true) (hp : R.f.parts = [h.v])
    (hH : HeardIs R gV) (hP : PointsAgree R.f gV R.a.base (R.t.heard ++ R.ds))
    (hLeft : Left R planes (Spec.keysOf D) gV G) (kv : Nat → Nat → GE) (hv : D.v = h.v)
    (hkey : ∀ x, x < 2 ^ h.v → D.key x = OnBytes.Ends.jointKey h kv (up R.pts.theta) x)
    (F' : Fork) (hL : OnBytes.PscRun.Later G F') (lm first : Nat) (ν : _root_.Fo.Pl → GE)
    (hD : Dict R ν) : K3OutKeys h lm first ν kv Reading.gl g F' := by
  obtain ⟨point, form, hk, _⟩ := toHeard_parts hg
  have e1 : point = R.pts.keyPt 0 h.v := by
    have := hP.keys
    rw [hk, hp] at this
    simpa using this
  have e2 : form = R.form (.key 0 h.v) := by
    have := hH.keys
    rw [hk, hp] at this
    simpa using this
  have hsz : point.size = h.dT + h.rK := by
    rw [e1]
    exact Spec.size_keyPt _ _ _ 0 _
  refine outKeys_of_worth hg hok point form hk hsz F' lm first ν (fun _ _ _ => 0) kv ?_
  have w := (hLeft.1 F' _ (fun _ _ _ => 0) hL hD).2 (h.v, 0) (by rw [hp]; simp)
  rw [e2, w, hP.theta, hP.alpha, e1]
  congr 1
  show OnBytes.HonestTrace.Look.ext D.v D.key (byBit (R.pts.keyPt 0 h.v)) = _
  rw [hv, Congr.ext_same h.v _ _ hkey,
    OnBytes.HonestTrace.Look.ext_blocks h.v _ _
      (by rw [byBit_length]; exact Spec.size_keyPt _ _ _ 0 _)]
  congr 1
  show ptL ((R.pts.keyPt 0 h.v).toList.reverse.map up).reverse = _
  rw [← List.map_reverse, List.reverse_reverse]
  rfl

#print axioms ProofFile.Honest.K3.Law.Exchange.outKeys_of_worth
#print axioms ProofFile.Honest.K3.Law.Exchange.outKeys_of_left
#print axioms ProofFile.Honest.K3.Law.Exchange.join_val
#print axioms ProofFile.Honest.K3.Law.Exchange.rdA_extract
#print axioms ProofFile.Honest.K3.Law.Exchange.rdA_append
#print axioms ProofFile.Honest.K3.Law.Exchange.toHeard_zk
#print axioms ProofFile.Honest.K3.Law.Exchange.zk_read

end ProofFile.Honest.K3.Law.Exchange
