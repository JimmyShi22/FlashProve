-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/ValsGeneral.lean

Definitions and theorems, all general: none stands under the head (the terms:
Johnson/HonestTrace/U3Fit/SeatsAtHead.lean), none at a size. Where the makers of the values of "U3"
(Johnson/HonestTrace/U3Rows.lean) return: unfoldings of "fitsSeg", "placeIn", "declared", "headVals"
and "valsAt". Public data alone. A SegVals is carried whole; its field vec, a function that awaits
the trace's cells, is applied nowhere here.

Main definitions:
* "fitsLook", "fitsMats": of "fitsSeg", its two clauses on the lookup's rounds, and its five clauses
  on the public X and the plan's list of matrices.
* "LookFits Z sps seg own h": a named premise: "fitsLook" holds at whatever "placeIn" returns at the
  kind K3 and at the segment's own kind (K4, K5 or K6).
* "placeBy": the text of "placeIn" typed a second time, as a function of the table of steps.

Main theorems:
* "fitsSeg_halves": "fitsSeg" accepts just where "fitsLook", n != 0 and "fitsMats" do. "fitsSeg_ok":
  so it returns where the three say yes.
* "placeIn_by" (by rfl), "declared_by": the two readers as functions of what they read.
* "headVals_returns": "headVals" returns where its six steps do; its n and its front are said.
* "valsAt_head": at a segment whose built data is of the sort 2, "valsAt" is "headVals".

Limits. Three theorems are equations without a premise ("fitsSeg_halves", "placeIn_by",
"declared_by"); the three that end in a return or in "valsAt" are conditional, and this file shows
none of their premises. "LookFits" holds idly where one of the two calls of "placeIn" rejects:
whoever needs "fitsLook" itself has to bring both returns. It is shown under the head in
Johnson/HonestTrace/U3Fit/LookFits.lean. Of the layers' and of attention's maker nothing is said but
"fitsSeg", which all three makers ask.
Not claimed: that a maker returns. No property of a release, of a verifier or of a prover is
claimed.
-/
import Johnson.HonestTrace.U3Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Honest.K3 (matsOwn tlOf)
open ProofFile.Honest.K4 (k4LookRounds)
open ProofFile.Honest.K6 (headParAt headInFront)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.First (Cut)

/-! ## 1 "fitsSeg" -/

/-- Of "fitsSeg": its two clauses on the lookup's rounds. -/
def fitsLook (Z : Pub) (h : Forest.Shape) (look0 own0 : Nat) : Bool :=
  VerifiableInference.Desc.K3.entriesFit (VerifiableInference.Desc.K3.faceOf h)
      (declared Z look0 (k4LookRounds h)) &&
    look0 + k4LookRounds h == own0

/-- Of "fitsSeg": its five clauses on the public X and the plan's list of matrices. -/
def fitsMats (X : Verify.Public) (seg : Nat) (mats : Array TMat) : Bool :=
  (matsOwn X seg).length == mats.size && ((matsOwn X seg).all fun m => m.2.1 != "") &&
    ((matsOwn X seg).all fun m => m.1 ≤ seg) && sizesOf (tlOf X seg).mats == sizesOf mats &&
    borrowedFit X seg

/-- **GENERAL IN ALL LETTERS: "fitsSeg" accepts just where its three parts do.** -/
theorem fitsSeg_halves (Z : Pub) (G : Ground) (seg : Nat) (h : Forest.Shape) (look0 own0 n : Nat)
    (mats : Array TMat) :
    (errOf (fitsSeg Z G seg h look0 own0 n mats)).isNone =
      (fitsLook Z h look0 own0 && n != 0 && fitsMats G.W seg mats) := by
  unfold fitsSeg fitsLook fitsMats
  cases VerifiableInference.Desc.K3.entriesFit (VerifiableInference.Desc.K3.faceOf h)
      (declared Z look0 (k4LookRounds h)) <;>
    cases look0 + k4LookRounds h == own0 <;> cases n != 0 <;>
    cases (matsOwn G.W seg).length == mats.size <;>
    cases ((matsOwn G.W seg).all fun m => m.2.1 != "") <;>
    cases ((matsOwn G.W seg).all fun m => decide (m.1 ≤ seg)) <;>
    cases sizesOf (tlOf G.W seg).mats == sizesOf mats <;> cases borrowedFit G.W seg <;> rfl

/-- So it returns where the three say yes. -/
theorem fitsSeg_ok {Z : Pub} {G : Ground} {seg : Nat} {h : Forest.Shape} {look0 own0 n : Nat}
    {mats : Array TMat} (hl : fitsLook Z h look0 own0 = true) (hn : n ≠ 0)
    (hm : fitsMats G.W seg mats = true) : fitsSeg Z G seg h look0 own0 n mats = .ok () := by
  have k := fitsSeg_halves Z G seg h look0 own0 n mats
  rw [hl, hm, bne_iff_ne.2 hn] at k
  cases e : fitsSeg Z G seg h look0 own0 n mats with
  | ok u => rfl
  | error s =>
    rw [e] at k
    cases k

/-- **A NAMED PREMISE: the lookup's two clauses at a segment**: at whatever "placeIn" returns at the
kind K3 and at the segment's own kind. own: K4, K5 or K6. h: the lookup's shape. -/
def LookFits (Z : Pub) (sps : List Spot) (seg : Nat) (own : KindName) (h : Forest.Shape) : Prop :=
  ∀ k3 k, placeIn Z sps seg .K3 = .ok k3 → placeIn Z sps seg own = .ok k →
    fitsLook Z h k3.2 k.2 = true

/-! ## 2 "placeIn" and "declared" of what they read -/

/-- "placeIn" of the table of steps alone. -/
def placeBy (cuts : List Cut) (sps : List Spot) (seg : Nat) (k : KindName) :
    Except String (Spot × Nat) := do
  let sp ← have_ "U3: the segment has no place of a kind that is read"
    (sps.find? fun sp => sp.place.link == some seg && sp.place.kind == k)
  let c ← have_ "U3: a place has no step" sp.cuts.head?
  let n ← have_ "U3: the table of steps lacks a place's first step"
    (if cuts.any fun d => d.look == c.look then
      some ((cuts.takeWhile fun d => d.look != c.look).foldl (fun n d => n + d.take) 0)
    else none)
  pure (sp, n)

/-- GENERAL: the two are one. -/
theorem placeIn_by (Z : Pub) (sps : List Spot) (seg : Nat) (k : KindName) :
    placeIn Z sps seg k = placeBy Z.cuts sps seg k := rfl

/-- GENERAL: "declared" reads of the declared rounds their entries alone. -/
theorem declared_by (Z : Pub) (first n : Nat) :
    declared Z first n = ((Z.D.1.map (·.entry)).drop first).take n := by
  unfold declared
  rw [List.map_take, List.map_drop]

/-! ## 3 The output head's maker -/

/-- **GENERAL: the output head's maker returns where its six steps do.** -/
theorem headVals_returns {Z : Pub} {G : Ground} {cov : Head.Covered} {sps : List Spot} {seg : Nat}
    {k6 k3 : Spot × Nat} (p6 : placeIn Z sps seg .K6 = .ok k6)
    (p3 : placeIn Z sps seg .K3 = .ok k3)
    (hd : declared Z k6.2 ((headParAt G).rounds.map (·.entry)).length =
      (headParAt G).rounds.map (·.entry))
    (hc : headInFront (headParAt G) 8 = ((headParAt G).rounds.map (·.entry)).length)
    (hs : cov.sized G.W.hS.T = true)
    (hf : fitsSeg Z G seg G.W.HLy.fs k3.2 k6.2 (G.W.H.nU.getD 2 0) G.W.H.tl.mats = .ok ()) :
    ∃ V, headVals Z G cov sps seg = .ok V ∧ V.n = G.W.H.nU.getD 2 0 ∧
      V.front = k6.2 + ((headParAt G).rounds.map (·.entry)).length := by
  unfold headVals
  rw [p6, p3]
  simp only [bind, Except.bind, ask, hd, hc, hs, hf, beq_self_eq_true, if_true, pure, Except.pure]
  exact ⟨_, rfl, rfl, rfl⟩

/-- **GENERAL: at a segment whose built data is of the sort 2, "valsAt" is the output head's
maker.** -/
theorem valsAt_head {Z : Pub} {G : Ground} {sps : List Spot} {seg : Nat} {Y : Stages.LinkH}
    (hs : spotsOf Z.cuts = some sps) (hb : G.built[seg]? = some Y) (hk : Y.kind = 2)
    (cov : Head.Covered) : valsAt Z G cov seg = headVals Z G cov sps seg := by
  unfold valsAt
  rw [hs, hb]
  simp only [have_, bind, Except.bind, ask, hk]
  rfl

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.fitsSeg_halves
#check @OnBytes.HonestTrace.U3.Fit.fitsSeg_ok
#check @OnBytes.HonestTrace.U3.Fit.placeIn_by
#check @OnBytes.HonestTrace.U3.Fit.declared_by
#check @OnBytes.HonestTrace.U3.Fit.headVals_returns
#check @OnBytes.HonestTrace.U3.Fit.valsAt_head
#print axioms OnBytes.HonestTrace.U3.Fit.fitsSeg_halves
#print axioms OnBytes.HonestTrace.U3.Fit.fitsSeg_ok
#print axioms OnBytes.HonestTrace.U3.Fit.placeIn_by
#print axioms OnBytes.HonestTrace.U3.Fit.declared_by
#print axioms OnBytes.HonestTrace.U3.Fit.headVals_returns
#print axioms OnBytes.HonestTrace.U3.Fit.valsAt_head
