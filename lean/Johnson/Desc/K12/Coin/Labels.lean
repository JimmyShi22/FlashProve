-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Labels.lean: THE BLOCK's OWN TEST ON THE LABELS PAYS A PART OF THE PROMISE.
Definitions, statements and proofs.

The batching's part of `guardedProximityTestParts` asks `labelsOk` (Johnson/Desc/K12/Law/FirstCut.lean): in turn, the
label of each tree that the first switch's rounds declare to open is the number of the book's tree
at the place D.ts. A law in the plain form owes its conclusion only where the verifier puts out: so
what a yes holds may be handed to whoever pays the promise.

  `batK_labels`, `k12_labels`: a yes of the block's decision holds `labelsOk` at the record behind
    the batching. After `batK_ok` (Law/Top.lean) and `k12_guards` (Law/TopH.lean).
  `labels_eq`: what `labelsOk` says, as an equation of two lists.
  `yes_labels`: where the piece puts out at any transcript: at whatever the record fixes, that
    equation.
With `leads_of_yes` (LawY.lean: a promise is owed only where the verifier ever puts out) whoever
pays `FirstOpens` may lean on that equation.
Limits: those of LawN.lean and OwnArm.lean. NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.K12.Coin.OwnArm
import Johnson.Desc.K12.Law.LabelsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK
open H2K.FoldLaw (bind_ok)
open H2K.First (gpOf Plain labelsOk labelsL)

theorem batK_labels (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (guardedProximityTestParts.bat p cut).decide t rs gs = .ok t1) :
    (batJ p cut).decide t rs gs = .ok t1 ∧ labelsOk p t1 = true := by
  obtain ⟨h1, _⟩ := ranged_ok _ _ _ _ _ _ h
  obtain ⟨_, _, h1⟩ := bind_ok h1
  obtain ⟨t', ha, hb⟩ := bind_ok h1
  obtain ⟨_, _, hc⟩ := bind_ok hb
  obtain ⟨_, hg, hc⟩ := bind_ok hc
  cases hc
  have hg' := needD_ok hg
  rw [Bool.and_eq_true] at hg'
  exact ⟨ha, hg'.2⟩

/-- A yes of the block's decision holds `labelsOk` at the record behind the batching. -/
theorem k12_labels (p : P12) (he : p.early = true) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
      First.Close.bat t0.st t0.g e r = .ok (row, L, S') ∧
      labelsOk p { t0 with st := S', pass := .claim row L } = true := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, hfr, hbat, _, _⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
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
  obtain ⟨hbat', hg⟩ := batK_labels p _ _ _ _ _ hbat
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ hbat'
  exact ⟨e, r, row, L, S', hb, hg⟩

theorem labels_eq (p : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (D : Plain) (hs : p.nums.stages = a :: rest)
    (hp : t.pass = .claim row L) (hD : gpOf p t a L = some D) (h : labelsOk p t = true) :
    D.opens.map (·.1.tree) = D.ts.map (H2K.First.numAt D.book) := by
  unfold labelsOk labelsL at h
  rw [hs, hp] at h
  dsimp only at h
  rw [hD] at h
  simpa [H2K.First.ok] using h

/-- Where the piece puts out at any transcript, the labels' equation holds at what the record
fixes. -/
theorem yes_labels {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (dB :: dt))) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π x.1 a rest G0 Ly D) :
    D.opens.map (·.1.tree) = D.ts.map (H2K.First.numAt D.book) := by
  obtain ⟨_, k, hst, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x τ b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: dt) τ)
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2 τ).opened = .ok (b.1, k) :=
    hst
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨e, r, row, L, S', hbat, hl⟩ := k12_labels π he x.1 b.1 _ _ hp hdec
  obtain ⟨G1, g1, g2, rfl⟩ := bat_front _ _ _ _ _ _ _ hbat
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain rfl := Option.some.inj (g1.symm.trans f2)
  obtain rfl := Option.some.inj (g2.symm.trans f3)
  exact labels_eq π _ a rest row L D f1 rfl (f4 row) hl

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yes_labels
