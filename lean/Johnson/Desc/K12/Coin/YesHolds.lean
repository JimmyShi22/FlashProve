-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/YesHolds.lean: WHAT ELSE A YES OF THE PIECE HOLDS, FOR WHOEVER PAYS A PROMISE
OR SPENDS THE CONCLUSION. Statements and proofs.

  `yes_free`: the plan's count of roots in front of the test is the record's.
  `k12_fits`, `yes_fits`: the layout's k and h are the first stage's (the frame's guard "the group
    is the first stage's", `firstFits`, Johnson/Desc/K12/Frame.lean): so the batching lays an entry
    by the same two numbers by which the stage reads it.
  `yes_kept`: the row that the batching returns on "BAT"'s round as shown has no kept form.
Beside `yes_acc` | `yes_accO` (Acc.lean, OwnArm.lean), `yes_pass0` (LawN.lean), `yes_labels`
(Labels.lean). By `Reduction.Leads.conseq` each may be added to a law's conclusion at no cost; by
`leads_of_yes` and `BatAtY` (LawY.lean) each is at the hand of whoever pays a promise.
A tool.
-/
import Johnson.Desc.K12.Coin.Labels

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK
open H2K.FoldLaw (bind_ok)
open H2K.First (Plain)

theorem yes_free {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (dB :: dt))) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b) : π.nums.free = x.1.roots := by
  obtain ⟨_, k, hst, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x τ b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: dt) τ)
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2 τ).opened = .ok (b.1, k) :=
    hst
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  exact (k12_guards π he x.1 b.1 _ _ hp hdec).1

/-- A yes of the block's decision: the layout that the batching returns has the first stage's k and
h. -/
theorem k12_fits (p : P12) (he : p.early = true) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (e : Fmt.Entry) (r : Fmt.RoundView)
      (row : GroupRow) (L : GroupLayout) (S' : Statement), p.nums.stages = first :: rest ∧
      First.Close.bat t0.st t0.g e r = .ok (row, L, S') ∧ L.k = first.k ∧ L.h = first.h := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, hfr, hbat, hgrp, _⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  obtain ⟨first', rest', ds', e1', e2', l1, _⟩ := H2K.FrameLens.lens_top (Cl := Unit) guardedProximityTestParts p hp
  obtain rfl := Option.some.inj (e2'.symm.trans e2)
  obtain ⟨hfr', _, _⟩ := frontK_ok p _ _ _ _ hfr
  have hF : tF = t0 := by
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  have nB : (batAt guardedProximityTestParts p (ds'.zip p.oracles) : Blk').rounds.length = 1 := by
    show (((ds'.zip p.oracles).take 1).map (·.1)).length = 1
    rw [List.length_map, l1]
  rw [nB] at hbat
  obtain ⟨hbat', _⟩ := batK_labels p _ _ _ _ _ hbat
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ hbat'
  refine ⟨first, rest, e, r, row, L, S', e1, hb, ?_⟩
  obtain ⟨g, hg, hf⟩ := (Option.any_eq_true _ _).1 hgrp
  simp only [firstFits, Bool.and_eq_true, beq_iff_eq] at hf
  simp only [guardedProximityTestParts] at hg
  split at hg
  · rename_i x L' G hpass _
    obtain ⟨_, rfl⟩ := Passing.claim.inj hpass
    split at hg
    · obtain rfl := Option.some.inj hg
      exact ⟨hf.1.2, hf.2⟩
    · cases hg
  · cases hg

theorem yes_fits {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (dB :: dt))) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π x.1 a rest G0 Ly D) : Ly.k = a.k ∧ Ly.h = a.h := by
  obtain ⟨_, k, hst, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x τ b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: dt) τ)
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2 τ).opened = .ok (b.1, k) :=
    hst
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨first, rest', e, r, row, L, S', e1, hbat, h1, h2⟩ := k12_fits π he x.1 b.1 _ _ hp hdec
  obtain ⟨G1, _, g2, _⟩ := bat_front _ _ _ _ _ _ _ hbat
  obtain ⟨rfl, _⟩ := List.cons.inj (e1.symm.trans hf.1)
  obtain rfl := Option.some.inj (g2.symm.trans hf.2.2.1)
  exact ⟨h1, h2⟩

/-- Where the piece says yes behind (m, c): the row that the batching returns on "BAT"'s round as
(m, c) shows it, at whatever entry, has no kept form. -/
theorem yes_kept {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str)
    (m : (roundT (ckP .two) dB).up.Msg) (c : (roundT (ckP .two) dB).up.Chal)
    (τ : Iop.Tr (uLT (ckP .two) dt)) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB dt e₀ εt).ior.red.out x (m, c, τ) = some b) (en : Fmt.Entry)
    (row : GroupRow) (Ly : GroupLayout) (S' : Statement)
    (h : First.Close.bat x.1.st x.1.g en (noDigest (r0Of dB m c)) = .ok (row, Ly, S')) :
    row.kept = #[] := by
  obtain ⟨_, k, hst, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x (m, c, τ) b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: dt) (m, c, τ))
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2 (m, c, τ)).opened =
      .ok (b.1, k) := hst
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨_, _, e, r, row', L, S'', hr, hbat, hgp⟩ := k12_guards π he x.1 b.1 _ _ hp hdec
  have hr0 : r = noDigest (r0Of dB m c) := by
    have h1 : ((rvT (ckP .two) (dB :: dt) (m, c, τ)).map noDigest).take 1 =
        [noDigest (r0Of dB m c)] := rfl
    rw [hr] at h1
    exact (List.cons.inj h1).1
  subst hr0
  cases bat_unique _ _ _ _ _ _ _ hbat h
  obtain ⟨first, rest, _, e1, _⟩ := H2K.FrameLens.lens_top (Cl := Unit) guardedProximityTestParts π hp
  obtain ⟨D, _, hok⟩ := H2K.First.gpOk_inv π _ first rest row Ly e1 rfl hgp
  exact (H2K.First.good_of_ok π first row D hok).rowKept

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yes_kept
#print axioms VerifiableInference.Desc.K12.Coin.yes_free
#print axioms VerifiableInference.Desc.K12.Coin.yes_fits
