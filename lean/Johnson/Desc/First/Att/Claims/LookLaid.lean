-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/LookLaid.lean: kind K5: the three tables on the lookup's matrix of
planes lie in the list of the record's tables, each with array number 2.

Main names:
  `Laid2 s t mat len phi`: a table lies in the list placed so far, with its first entry, matrix,
    length and weights, and its array is number 2. `stable_laid2`, `sp_add2`: the kind's own add
    (Johnson/Desc/First/Att/TablesP.lean) writes tree := 2. `sp_placeAll2`: what placeAll lays for
    tBit0, tBit1 and tPin.
  `look_laid`: at h := oldOf S gL i (Johnson/Desc/First/Att/Claims/Any.lean): for each of tBit0,
    tBit1, tPin there is Fn in h.t.funs with Fn.tree = 2, Fn.start the table's first entry, Fn.mat =
    NAs + 2, Fn.len = 2^lmb and Fn.phi the weight vector that the lookup hands in: the proposition
    LaidAt of Johnson/Meaning/PlanesKit.lean, word for word. From the return of tablesP and PosG.
Why: TabAt (Johnson/Road/Rows/AttRead.lean) and tabs_look
(Johnson/Desc/First/Att/Claims/TablesAt.lean) do not say which array a table lies in.
Limit: PosG is a plan fact that no test of the verifier asks
(Johnson/Desc/First/Att/Claims/PlanLaw.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.TablesAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Placed Fun1 Geo T LookIn Pts ScoreP TablesP)

/-- A table lies in the list, and its array is number 2. -/
def Laid2 (s : Placed) (t mat len : ℕ) (phi : Array E) : Prop :=
  ∃ f ∈ s.funs.toList, f.tree = 2 ∧ f.start = t ∧ f.mat = mat ∧ f.len = len ∧ f.phi = phi

theorem stable_laid2 (t mat len : ℕ) (phi : Array E) : Stable fun s => Laid2 s t mat len phi :=
  fun _ _ ⟨f, hf, r⟩ x => ⟨f, x.1 f hf, r⟩

theorem sp_add2 (mats : Array (ℕ × ℕ)) (mat len : ℕ) (phi : Array E) (e : ℕ) (he : 0 < e) :
    Sp (P.add mats mat len phi e) fun a s => Laid2 s a mat len phi := by
  intro s a s' h
  refine ⟨(sp_add mats mat len phi e he s a s' h).1, ?_⟩
  obtain ⟨_, rfl, rfl⟩ := add_some h
  exact ⟨Fun1.mk mat len phi 2 s.next, by simp, rfl, rfl, rfl, rfl, rfl⟩

/-- The three tables on the lookup's matrix, with their array's number. -/
theorem sp_placeAll2 (g : Geo) (mats : Array (ℕ × ℕ)) (nW : ℕ) (lk : LookIn) (p : Pts) (hp : PosG g) :
    Sp (P.placeAll g mats nW lk p) fun t s => t.funs = s.funs ∧
      Laid2 s t.tBit0 (g.NAs + 2) (2 ^ g.lmb) lk.phiB0 ∧ Laid2 s t.tBit1 (g.NAs + 2) (2 ^ g.lmb) lk.phiB1 ∧
      Laid2 s t.tPin (g.NAs + 2) (2 ^ g.lmb) lk.phiP := by
  unfold P.placeAll
  refine (Sp.bind (Sp.lift _) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addAs' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addAs' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addAs' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_mapM _ (fun (k : ScoreP) => QRow g mats (P.tok g k.wI k.zi))
      (fun k => sp_addRow' g mats _ hp) (fun k => stable_QRow g mats _) p.scores).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addRow' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addRow' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addRow' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addRow' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addRow' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addRow' g mats _ hp).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind (Sp.lift _) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addLong' g mats _ _ _ _ hp.gSo).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_mapM _ (fun (k : ScoreP) (y : ℕ × ℕ) (s : Placed) =>
        QLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).1 k.zi)
          (g.fillQ * g.T / 2 ^ g.la) y.1 s ∧
        QLong g mats (g.NAs + 3) (P.lastCoords k.sc.r g.ldh) (P.tok g (P.scoreTiles g k).2 k.zj)
          (g.fillQ * g.T / 2 ^ g.la) y.2 s)
      (fun k => (Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun tQ =>
        Sp.bind (sp_addLong' g mats _ _ _ _ hp.gSq) (stable_QLong g mats _ _ _ _) fun tK =>
        Sp.pure (tQ, tK)).mono (by rintro y s ⟨tQ, q1, tK, q2, rfl⟩; exact ⟨q1, q2⟩))
      (fun k y => (stable_QLong g mats _ _ _ _ _).and (stable_QLong g mats _ _ _ _ _)) p.scores).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addLong' g mats _ _ _ _ hp.gSq).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addLong' g mats _ _ _ _ hp.gSq).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addLong' g mats _ _ _ _ hp.gSq).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addLong' g mats _ _ _ _ hp.gSq).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind ((sp_addLong' g mats _ _ _ _ hp.gSq).mono fun _ _ _ => trivial) (fun _ => stable_true) fun _ =>
    Sp.bind (Sp.lift _) (fun _ => stable_true) fun _ =>
    Sp.bind (sp_weights _ _) (fun _ => stable_const _) fun phiB0 =>
    Sp.bind (sp_add2 mats _ _ phiB0 _ hp.kbA) (fun a => stable_laid2 a _ _ _) fun tBit0 =>
    Sp.bind (sp_weights _ _) (fun _ => stable_const _) fun phiB1 =>
    Sp.bind (sp_add2 mats _ _ phiB1 _ hp.kbA) (fun a => stable_laid2 a _ _ _) fun tBit1 =>
    Sp.bind (sp_weights _ _) (fun _ => stable_const _) fun phiP =>
    Sp.bind (sp_add2 mats _ _ phiP _ hp.kbA) (fun a => stable_laid2 a _ _ _) fun tPin =>
    sp_tail _ _ _).mono ?_
  rintro t s ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, rfl, tB0, qB0, _, rfl, tB1, qB1, _, rfl, tPn, qPn, rfl⟩
  exact ⟨rfl, qB0, qB1, qPn⟩

open OnBytes.Road.Rows in
/-- **The three tables on the lookup's matrix lie in the list of the record's tables, each with array number 2**: at their first entries, on matrix number NAs + 2, in blocks of 2^lmb rows, under the three weight vectors that the lookup hands in. -/
theorem look_laid {tl : HTailF2} {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {nW : ℕ} {lk : LookIn}
    (hg : i.g = P.geoOf S) (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t) (hp : PosG i.g) :
    (∃ Fn ∈ (oldOf S gL i).t.funs.toList, Fn.tree = 2 ∧ Fn.start = (oldOf S gL i).t.tBit0 ∧
      Fn.mat = S.cf.NAs + 2 ∧ Fn.len = 2 ^ S.cf.lmb ∧ Fn.phi = lk.phiB0) ∧
    (∃ Fn ∈ (oldOf S gL i).t.funs.toList, Fn.tree = 2 ∧ Fn.start = (oldOf S gL i).t.tBit1 ∧
      Fn.mat = S.cf.NAs + 2 ∧ Fn.len = 2 ^ S.cf.lmb ∧ Fn.phi = lk.phiB1) ∧
    (∃ Fn ∈ (oldOf S gL i).t.funs.toList, Fn.tree = 2 ∧ Fn.start = (oldOf S gL i).t.tPin ∧
      Fn.mat = S.cf.NAs + 2 ∧ Fn.len = 2 ^ S.cf.lmb ∧ Fn.phi = lk.phiP) := by
  unfold P.tablesP at ht
  have h' : (P.placeAll i.g (matsOf tl.mats) nW lk i.p {}).bind (fun y => some y.1) = some i.t := ht
  cases hr : P.placeAll i.g (matsOf tl.mats) nW lk i.p {} with
  | none => rw [hr] at h'; cases h'
  | some y =>
    rw [hr] at h'
    have e : y.1 = i.t := Option.some.inj h'
    obtain ⟨ef, q0, q1, q2⟩ := (sp_placeAll2 i.g (matsOf tl.mats) nW lk i.p hp {} y.1 y.2 hr).2
    rw [e] at ef q0 q1 q2
    unfold Laid2 at q0 q1 q2
    rw [← ef, hg] at q0 q1 q2
    have back : ∀ {t : ℕ} {phi : Array E},
        (∃ f ∈ i.t.funs.toList, f.tree = 2 ∧ f.start = t ∧ f.mat = S.cf.NAs + 2 ∧ f.len = 2 ^ S.cf.lmb ∧
          f.phi = phi) →
        ∃ Fn ∈ (oldOf S gL i).t.funs.toList, Fn.tree = 2 ∧ Fn.start = t ∧ Fn.mat = S.cf.NAs + 2 ∧
          Fn.len = 2 ^ S.cf.lmb ∧ Fn.phi = phi := by
      rintro t phi ⟨f, hf, r⟩
      refine ⟨funBack f, ?_, r⟩
      show funBack f ∈ (i.t.funs.map funBack).toList
      rw [Array.toList_map]
      exact List.mem_map.2 ⟨f, hf, rfl⟩
    exact ⟨back q0, back q1, back q2⟩

end K5Law
