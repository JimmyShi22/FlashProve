-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/LayersAtHead.lean

Under the head (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean) and one more premise, the
maker of the values of "U3" at a layers' segment ("layersVals", Johnson/HonestTrace/U3Rows.lean)
returns at each of the twelve groups. The premise: "LookFits Zp spotsWritten (2 * g) .K4
G.W.layers.y.fo" (Johnson/HonestTrace/U3Fit/ValsGeneral.lean). Theorems; no definition. Public data
alone. A SegVals is carried whole; its field vec, a function that awaits the trace's cells, is
applied nowhere here.

Main theorems:
* "layersVals_returns" (no head): the maker returns where its steps do; its n and front are said.
* "nine_of_reads" (no head): where the layout has routed experts ("y.h.p3 = true"), what "readsOf"
  returns has at least nine variables at both gated levels: by the refusal in "readsOf" itself.
* "layersVals_at_head": the maker returns V with "V.n = colsW (2 * g)"; "V.front" is the written
  rows' rounds up to and with row 14 (2 g) + 4 of "cutFirstFull".
* "layers_return": so "valsAt" returns at the twelve layers' segments (2 g, g below 12), at every
  cov.

Limits. The head is a premise: the full size and the format's second hash function alone. "LookFits" is a
premise here, at each group; "lookFits_layers" (Johnson/HonestTrace/U3Fit/LookFits.lean) shows it
under the head. No closed fact and no raised option of its own; files that it imports have them.
Not claimed: anything on the vector's entries or on "ready". No property of a release, of a verifier
or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.LayersLaid
import Johnson.HonestTrace.U3Fit.ValsSorts
import Johnson.Road.K4.RefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay Reads readsOf tableAsks layTables)
open ProofFile (Pub Ground Spot)
open ProofFile.Honest.K3 (tlOf)
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA TS)

/-- **GENERAL: the layers' maker returns where its steps do.** -/
theorem layersVals_returns {Z : Pub} {G : Ground} {sps : List Spot} {seg g : Nat}
    {hp : Layer.HPlan2} {k4 k3 : Spot × Nat}
    {y : List Layer.TableAt × List (Layer.TableAsk × List (Nat × Nat)) × Nat}
    (e : G.W.G[g]? = some hp) (p4 : placeIn Z sps seg .K4 = .ok k4)
    (p3 : placeIn Z sps seg .K3 = .ok k3)
    (hc : OnBytes.Desc.First.K4.covers G.W.layers = true)
    (h9 : 9 ≤ G.W.layers.rd.muH ∧ 9 ≤ G.W.layers.rd.muH2)
    (hd : declared Z k4.2 (OnBytes.Desc.First.K4.entries G.W.layers hp g).length =
      OnBytes.Desc.First.K4.entries G.W.layers hp g)
    (hm : ((G.W.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)) = sizesOf hp.tl.mats)
    (hl : layTables (sizesOf hp.tl.mats) (tableAsks G.W.layers.y G.W.layers.rd g) 0 = some y)
    (hn : y.2.2 = hp.nU.getD 2 0)
    (hf : fitsSeg Z G seg G.W.layers.y.fo k3.2 k4.2 y.2.2 hp.tl.mats = .ok ()) :
    ∃ V, layersVals Z G sps seg g = .ok V ∧ V.n = y.2.2 ∧
      V.front = k4.2 + (OnBytes.Desc.First.K4.entries G.W.layers hp g).length := by
  unfold layersVals
  rw [e, p4, p3]
  simp only [have_, bind, Except.bind, ask, OnBytes.Desc.First.K4.Honest.matsOf, hc, hd, hm, hl, hn,
    decide_eq_true h9.1, decide_eq_true h9.2, beq_self_eq_true, Bool.and_self, if_true, pure,
    Except.pure]
  rw [← hn, hf]
  exact ⟨_, rfl, rfl, rfl⟩

/-- **GENERAL: "readsOf"'s own refusal.** -/
theorem nine_of_reads {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) (h3 : y.h.p3 = true) :
    9 ≤ rd.muH ∧ 9 ≤ rd.muH2 := by
  unfold readsOf at h
  obtain ⟨hb, h2⟩ := OnBytes.Road.ok_of_refuse h
  have e := (Except.ok.inj h2).symm
  subst e
  rw [h3] at hb
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, Bool.true_and] at hb
  exact ⟨hb.1.2, hb.2⟩

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD AND THE LOOKUP's TWO CLAUSES: THE LAYERS' MAKER RETURNS AT GROUP g.** -/
theorem layersVals_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12)
    (hL : LookFits Zp spotsWritten (2 * g) .K4 G.W.layers.y.fo) :
    ∃ V, layersVals Zp G spotsWritten (2 * g) g = .ok V ∧ V.n = colsW (2 * g) ∧
      (cutFirstFull[14 * (2 * g) + 4]?).map (fun c => rowsBeforeW (14 * (2 * g) + 4) + c.2.2.1) =
        some V.front := by
  have hX := IM.ground_publicK h.laid.pub hG
  obtain ⟨k4, k3, hp, q4, q3, w4, -, e, hd, hlen⟩ := layersDeclared_at_head h hG hg
  obtain ⟨y, hl, hn, hcol, hn0⟩ := layersLaid_at_head h hG hg e
  obtain ⟨-, -, -, -, -, -, q⟩ := layersNums_at_head h hG
  have hm : fitsMats G.W (2 * g) hp.tl.mats = true := by
    have k := fitsMats_at_head h hG (seg := 2 * g) (by omega)
    rw [tlOf_even (marks_at_head h hG) hg e] at k
    exact k
  obtain ⟨V, hV, e1, e2⟩ := layersVals_returns e q4 q3
    (OnBytes.Road.K4.refPub_in_scope h.scope h.reads hX hg).covers
    (nine_of_reads (Meaning.P34.more_of_public hX).1 q) hd
    ((Meaning.P34.mats_of_public hX g).trans (Meaning.P34.tails_of_public hX e).1.symm) hl hn
    (fitsSeg_ok (hL k3 k4 q3 q4) hn0 hm)
  refine ⟨V, hV, e1.trans hcol, ?_⟩
  rw [e2, w4]
  cases hc : cutFirstFull[14 * (2 * g) + 4]? with
  | none =>
    rw [hc] at hlen
    cases hlen
  | some c =>
    rw [hc] at hlen
    have : c.2.2.1 = (OnBytes.Desc.First.K4.entries G.W.layers hp g).length :=
      Option.some.inj hlen
    show some (rowsBeforeW (14 * (2 * g) + 4) + c.2.2.1) = _
    rw [this]

/-- So "valsAt" returns at the twelve layers' segments, at every cov. -/
theorem layers_return (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hL : ∀ g < 12, LookFits Zp spotsWritten (2 * g) .K4 G.W.layers.y.fo) (cov : Head.Covered) :
    ∀ g < 12, ∃ V, valsAt Zp G cov (2 * g) = .ok V := by
  intro g hg
  obtain ⟨V, hV, -⟩ := layersVals_at_head h hG hg (hL g hg)
  exact ⟨V, by rw [valsAt_layers_at_head h hG hg cov]; exact hV⟩

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.layersVals_returns
#check @OnBytes.HonestTrace.U3.Fit.nine_of_reads
#check @OnBytes.HonestTrace.U3.Fit.layersVals_at_head
#check @OnBytes.HonestTrace.U3.Fit.layers_return
#print axioms OnBytes.HonestTrace.U3.Fit.layersVals_returns
#print axioms OnBytes.HonestTrace.U3.Fit.nine_of_reads
#print axioms OnBytes.HonestTrace.U3.Fit.layersVals_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.layers_return
