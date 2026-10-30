-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngLemma.lean: THE KIND K12's LEMMA IN THE GAME, AT A KEY FILE's RANGES' TEST, WITH EVERY TEST WITH CODE AMONG ITS PREMISES PAID BY THE RANGES' BLOCK. The lemma is the kind's own files' (k12_lemma): nothing of it is proved anew. Statements and proofs.
OBJECT. The kind's lemma `k12_lemma` (Johnson/Desc/K12/Law/K12Lemma.lean) at the place `rangesParams N` and the record at which the ranges' seat's asking has returned.
USER. Johnson/RunOne/Law/RngAnyCl.lean (rng_lemma_cl).
LETTERS. N and the record t0 are free. The two heavy fields of the kind's condition (the codes' facts; the small counts) stay premises.

The setting. That lemma says: under the kind's condition at a place (two tests with code; the facts on codes at the radii; a bound on the chain's error counts), two numbers of the place, the variant's test on the plan, one more test on the plan, and, for a first
round on which the batching returns, a record `FrontK` (the batching's return; the test gpOk at the record behind it; the plain data made): if no witness stands within the chain's radius for the batched claim at the word read off the members' written trees, the
prover is doomed towards "the block's step at the written view says no, or a test of work fails".

What is said.
  `frontK_asked`: where the ranges' seat's asking has returned and the batching returns without a kept form on a first round as shown, `FrontK` holds, at plain data D at which every clause of gpOk says yes.
  `rng_lemma`: AT THE PLACE's NUMBERS OFF THE PLAN (rangesParams N): from THE RANGES' BLOCK's TEST ON THE PLAN and THE RANGES' SEAT's ASKING AT THE RECORD t0, with the two heavy fields of the kind's condition as premises: the kind's chain c with `c.Holds` and its errors below εs, such
    that for every first round on which the batching returns without a kept form there are plain data D WITH `FrontK` AT D (so D is pinned: gpOf … = some D: the D of Johnson/RunOne/Law/RngSized.lean's cond_of_yes at the same row) and: for all written rounds and oracles of
    the group's trees as deep as the book's: NO WITNESS WITHIN THE RADIUS ⇒ DOOMED.
WHAT IS LEFT AS PREMISES, EACH WITH ITS OWNER. hcodes (`CodesAt`: radii below the distances, the counts, the lists, the base case's codes at the place's stages): whoever holds the theorems on codes at the release's radii. hsmall: the numbers'. `DeepK`: the reading's. "No
kept form": the variant's own guard gives it of the row that its yes has batched (Johnson/RunOne/Law/RngCond.lean: bat_of_yes). "No witness" of the BATCHED claim: from "no witness of all the rows" (Johnson/RunOne/Law/RngHolds.lean: noneNear_iff) by the batching's converse: its
two groups of files'.
Limits. THOSE OF k12_lemma (Johnson/Desc/K12/Law/K12Lemma.lean), ALL: the verifier in it is the block's step AT THE WRITTEN VIEW with all tests of work: that a view from bytes is the written view is owed; by that lemma's writers' word that verifier has said yes nowhere. The condition's two heavy fields are shown of
no place at the release's radii. THE VERIFIER IS A FIXED TEXT, NO LETTER: a block that says yes to all would fail that lemma's proof; one that says no to all meets the lemma by its form. The record t0 is a letter: at a key file's state it is the record that the seat's entering makes of the state
(Johnson/RunOne/Law/RngAtKeyD.lean: keyD_yes). NO SOUNDNESS IS CLAIMED.

-/
import Johnson.RunOne.Law.RngCond
import Johnson.Desc.K12.Law.K12Lemma

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace Johnson.RunOne.Law.RngLemma
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc.Key Johnson.RunOne.Law.RngAsked
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.First.Close (bat)
open H2K.Pub (sgOf writtenOf WR chainFrom K12Condition CodesAt)
open H2K.First (gpL gpOk_inv Plain)
open H2K.JointK (FrontK DeepK accK wAt yOf WO k12_lemma)

/-- Where the ranges' seat's asking has returned and the batching returns without a kept form, what stands in front of the game holds. -/
theorem frontK_asked {p : P12} {t0 : T12} (ha : asksOnRecord p t0 = .ok ()) {r0 : Fmt.RoundView} {e : Fmt.Entry}
    {row : GroupRow} {Ly : GroupLayout} {S' : Statement}
    (hb : bat t0.st t0.g e (noDigest r0) = .ok (row, Ly, S')) (h0 : row.kept = #[]) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : Plain), p.nums.stages = a :: rest ∧
      H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D := by
  obtain ⟨_, a, rest, _, hs, _, _, _, _, a4, _⟩ := asked_at_bat ha hb h0
  obtain ⟨D, hD, hok⟩ := gpOk_inv p _ a rest row Ly hs rfl a4
  exact ⟨a, rest, D, hs, hok, ⟨hb, a4, hD⟩⟩

/-- **The kind's lemma in the game at a key file's ranges' test, every test with code among its premises paid by the ranges' block.** -/
theorem rng_lemma {σ : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ}
    {N : H2U.PlaceNums} (hp : (rangesTest (Cl := Unit) laid back N).planOk = true) {t0 : T12}
    (ha : asksOnRecord (rangesParams N) t0 = .ok ()) {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {εs : ℝ≥0∞}
    (hcodes : CodesAt L mC mS mW rad (rangesParams N).nums.stages)
    (hsmall : ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      (rangesParams N).nums.stages = a :: rest → writtenOf (rangesParams N).nums = some (w0 :: l) →
      chainFrom (.at L mC mS mW rad) rest a l = some c → Err.Below c.err εs) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      (rangesParams N).nums.stages = a :: rest ∧ writtenOf (rangesParams N).nums = some (w0 :: l) ∧
      c.rds = l.map WR.rd ∧ c.rad = rad (sgOf a) ∧ c.Holds ∧ Err.Below c.err εs ∧
      ∀ (F : ℕ) (r0 : Fmt.RoundView) (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement),
        bat t0.st t0.g e (noDigest r0) = .ok (row, Ly, S') → row.kept = #[] →
        ∃ (D : Plain) (hok : H2K.First.ok (gpL (rangesParams N) a row D) = true),
          FrontK (rangesParams N) t0 a r0 e row Ly S' D ∧
          ∀ (rd : ℕ → ℕ) (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO), DeepK D W0 fM →
            (∀ w, ¬ (sgOf a).RIn c.rad (stmG (sgOf a) row, yOf (rangesParams N) a row D hok rd W0) w) →
            Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ =>
              accK (rangesParams N) F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = false := by
  obtain ⟨hpV, he, han, _, hsp⟩ := planOk_ok hp
  obtain ⟨_, _, _, _, _, _, _, hpub, _⟩ := asksRecord_ok ha
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, hL⟩ :=
    k12_lemma t0 (⟨hpub, hsp, hcodes, hsmall⟩ : K12Condition L mC mS mW rad (rangesParams N) t0.st.codes εs)
      he han hpV
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, fun F r0 e row Ly S' hb h0 => ?_⟩
  obtain ⟨a', rest', D, hs', hok, hfr⟩ := frontK_asked ha hb h0
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs'.symm.trans e1)
  exact ⟨D, hok, hfr, fun rd W0 fM hd hno => hL F r0 e row Ly S' D hok hfr rd W0 fM hd hno⟩

end Johnson.RunOne.Law.RngLemma

#print axioms Johnson.RunOne.Law.RngLemma.frontK_asked
#print axioms Johnson.RunOne.Law.RngLemma.rng_lemma
