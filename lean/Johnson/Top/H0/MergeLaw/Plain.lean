-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Plain.lean: the merge's law at its written rounds, one statement at a time.
Definitions, and theorems with their proofs.

Main names:
  `tie_of_ended`: the library's clauses on a sumcheck's record that is `Ended` at what was heard.
  `MergeSays`: what the merge's yes says, at one typed record, one tuple of entries and one typed
    statement: the values heard, pinned by facts on the two records; and: if the typed target is the
    reading of the ledger's public part, the side condition holds, the row form at the sent end
    value is worth 0 in a world that fits the entries, and the summand's map at the point is the
    sent value less the mask entry times the last challenge, then every claim on the weights holds.
  `merge_plain`: for each fixed tuple of entries and each statement the prover has lost
    (`Iop.Doomed`), at the maps' image of the proved block's errors, towards: wherever the maps
    pass,
    the stretch fits the declared rounds, the words are below the prime and `headMergeDecide` says
    yes, `MergeSays` holds.

Spent: `merge_carry`, `decide_view`, `typed_out`, `conv`'s two laws (this folder); `G_mid`
(Johnson/Top/H0/K11Caller/Mid.lean); the library's `sum_said`, `SumSaid.row`, `sum_end`, `sum_ini`.

Limits. The entries are fixed before the game. The written rounds are letters under `MergeDs`: none
is taken from a plan. `pass` is a premise. One statement at a time: no one error for all statements.
The premises inside `MergeSays` are paid by nobody here. It is no soundness of the protocol. Nothing
on hiding.

-/
import Johnson.Top.H0.MergeLaw.Carry
import Johnson.Top.H0.K11Caller.Mid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Psc (Weight)
open OnBytes.Model (Reading World wsForkStart)
open OnBytes.Model.Road (Ended)
open VerifiableInference.Desc (roundsFit noDigest fieldPrimeWord)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headClaimMergeKind)
open OnBytes.Tie.Pv.Lay.Eng (SumSaid sum_said sumTr sumOut sum_end merge_fits)
open _root_.Run (ckP)

/-- The library's three clauses on a sumcheck's record that is `Ended` at what was heard: as in
`hear_tie`, from the record alone. -/
theorem tie_of_ended (L : MergeL GE) {p : OnBytes.Model.Psc} {C : OnBytes.Model.Aff} {T mu cY beta v
    : E} {first : ℕ}
    {qs : List (Nat × List E × E)}
    (a4 : Ended p C T mu p.eps first (List.replicate L.k (Weight.plain 3)) (qs.map fun q => (q.2.1,
        q.2.2)) 1 [cY] beta)
    (hn : qs.length = L.k) (hq : ∀ q ∈ qs, q.2.1.length = 2) (st : L.St) (hβ : Reading.gl.val beta ≠
        0) :
    (∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World GE) (m : L.J → GE),
      L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st) p.first →
      L.toSum.T.par.inc st m = Reading.gl.val p.target - p.start.value Reading.gl W →
      ((p.rowForm v {}).value Reading.gl W = 0 ↔
        L.toSum.T.par.UHolds (sumOut Reading.gl L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
          p.target mu p.eps (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ => Reading.gl.val v)
              m)) ∧
    ∀ m : L.J → GE,
      (L.toSum.T.par.EHolds (sumOut Reading.gl L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
          p.target mu p.eps (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ => Reading.gl.val v)
              m () ↔
        L.f st m (L.toSum.Q.outPt L.toSum.M
            (sumOut Reading.gl L.toSum (fun st => pick (L.toSum.T.par.vars st)) st p.target mu
              p.eps (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ => Reading.gl.val v)) =
          Reading.gl.val v - m L.cAt * Reading.gl.val beta) := by
  have hl : (qs.map fun q => (q.2.1, q.2.2)).map (·.1.length) = List.ofFn L.toSum.M.n := by
    have h2 : (qs.map fun q => (q.2.1, q.2.2)).map (·.1.length) = List.replicate L.k 2 := by
      rw [List.map_map, List.eq_replicate_iff]
      refine ⟨by simp [hn], ?_⟩
      intro b hb
      obtain ⟨q, hqm, rfl⟩ := List.mem_map.1 hb
      exact hq q hqm
    rw [h2]
    exact (List.ofFn_const _ _).symm
  have s := sum_said Reading.gl L.toSum (fun st => pick (L.toSum.T.par.vars st)) st a4 hβ
    (fun _ => Reading.gl.val v) (merge_fits Reading.gl L st) hl rfl
  refine ⟨?_, ?_⟩
  · intro Ex y W m D1 D2
    refine s.row Reading.gl L.pick_ok Ex y W _ {} m D1 D2
      (by
        rw [OnBytes.Model.Aff.value_empty]
        exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim) ?_
    show ([(1 : GE) * [Reading.gl.val v].prod]).sum = _
    simp
  · intro m
    exact sum_end Reading.gl L.toSum _ st p.target mu p.eps _ [cY] beta hβ (fun _ => Reading.gl.val
        v) m ()

/-- **What the merge's yes says, at one typed record G, one tuple of entries m and one typed
statement x₀**: the record's facts; and: if the
typed target at the drawn element is the reading of the ledger's public part, the side condition
holds, the row form at the sent end value
is worth 0 in a world that fits m ((D1), (D2)), and the summand's map at the point is the sent value
less the mask entry times the last
challenge, then EVERY claim on the weights holds. -/
def MergeSays (P : HeadMergeP) (G : WeightsL GE) (m : G.J → GE) (x₀ : G.St) (s s' : S) : Prop :=
  ∃ (a a' : HeadOwn) (claim : OnBytes.Model.WsClaim) (x0 : OnBytes.Model.Head.Heard) (wo :
      OnBytes.Model.WsForkOut)
    (x mu cY beta v T : E) (qs : List (Nat × List E × E)) (hβ : Reading.gl.val beta ≠ 0),
    s.here = .head a ∧ s'.here = .head a' ∧ a.claim = some claim ∧ a.x = some x0 ∧ a'.wo = some wo ∧
    a.F.publicPart (wsForkStart #[x0.sV] (OnBytes.Model.powers x 1)) = some T ∧ wo.p.target = T ∧
        wo.beta = beta ∧
    wo.rm.toList = qs.map (·.2.2) ∧
    wo.recs = (#[claim].zip (OnBytes.Model.powers x 1)).toList.map (fun y =>
      OnBytes.Model.wsRowPart P.lay y.1 (OnBytes.mulE y.2 (OnBytes.Model.wsEpsT P.lay y.1 wo.rm))) ∧
    (∃ Gf : OnBytes.Model.Fork, ({ a.F with next := a.F.next + 1 + 2 * P.lay.lk + 2 } :
        OnBytes.Model.Fork).hideRun wo.sFv #[v] beta =
      some Gf ∧ Gf.shown wo.sFv = some wo.fvp ∧ a'.F = { Gf with planClaimsF := P.nLin }) ∧
    (∀ i : Fin G.k, G.L.toSum.Q.outPt G.L.toSum.M
        (sumOut Reading.gl G.L.toSum (fun st => pick (G.L.toSum.T.par.vars st)) (x₀, Reading.gl.val
            x) wo.p.target mu
          wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ => Reading.gl.val v) i =
      Reading.gl.val (((qs.map fun q => (q.2.1, q.2.2)).getD i.1 ([], zeroE)).2)) ∧
    (G.L.tg (x₀, Reading.gl.val x) = Reading.gl.val T → G.Rd x₀ m →
      (∃ W : World GE,
        G.L.toSum.T.par.W (x₀, Reading.gl.val x) m =
          OnBytes.Road.Hd.place W.slot (G.L.toSum.T.par.vars (x₀, Reading.gl.val x)) wo.p.first ∧
        G.L.toSum.T.par.inc (x₀, Reading.gl.val x) m = Reading.gl.val wo.p.target - wo.p.start.value
            Reading.gl W ∧
        (wo.p.rowForm v {}).value Reading.gl W = 0) →
      G.L.f (x₀, Reading.gl.val x) m (G.L.toSum.Q.outPt G.L.toSum.M
          (sumOut Reading.gl G.L.toSum (fun st => pick (G.L.toSum.T.par.vars st)) (x₀,
              Reading.gl.val x) wo.p.target mu
            wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ => Reading.gl.val v)) =
        Reading.gl.val v - m G.L.cAt * Reading.gl.val beta →
      ∀ c, G.Cl x₀ m c)

/-- **THE MERGE's LAW AT ITS WRITTEN ROUNDS, ONE STATEMENT AT A TIME.** -/
theorem merge_plain (P : HeadMergeP) (G : WeightsL GE) (Ex : ExtSpec) {dZ d0 : RDT} {ds : List RDT}
    {dY dV : RDT}
    (hk : ds.length = G.k) (hkP : G.k = P.lay.lk) (H : MergeDs dZ d0 ds dY dV) (m : G.J → GE) (a :
        G.St × Ex.Str) (s : S) :
    Doomed (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV])))
      ((mergeMaps G Ex dZ d0 ds dY dV hk).err (G.eps (Kc := Unit) (G.L.V1 Ex))) (fun τ =>
      (mergeMaps G Ex dZ d0 ds dY dV hk).pass τ = true →
      roundsFit (headClaimMergeKind P).rounds ((rvT (ckP .two) _ τ).map noDigest) = true →
      (∀ r ∈ (rvT (ckP .two) _ τ).map noDigest, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧
          x.2.2 < fieldPrimeWord) →
      ∀ s', headMergeDecide P s ((rvT (ckP .two) _ τ).map noDigest) = .ok s' → MergeSays P G m a.1 s
          s') := by
  refine merge_carry P G Ex hk H _ s _ (MergeSays P G m a.1 s) (K11Caller.G_mid G (G.L.V1 Ex) m a)
      ?_
  intro τ s' hf hw h hbad
  obtain ⟨h0, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hβ, e1, e2, e3, e4, e5, e6, e7, e8, hn,
      hq, hrm, hrecs, hE, hled,
    hview⟩ := decide_view P G Ex hk τ hf hw h
  refine ⟨h0, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hβ, e1, e2, e3, e4, e5, e6, e7, e8, hrm,
      hrecs, hled,
    OnBytes.Tie.Pv.Lay.Eng.sum_ini Reading.gl G.L.toSum _ _ _ _ _ _ _ _ hβ _, ?_⟩
  intro htg hRd hrow hev
  rw [← hkP] at hE hn
  obtain ⟨tRow, tEnd⟩ := tie_of_ended (v := v) G.L hE hn hq (a.1, Reading.gl.val x) hβ
  rw [hview] at hbad
  have hout := typed_out G Ex a.1 a.2 x mu wo.p.eps cY beta v T (qs.map fun q => (q.2.1, q.2.2)) hβ
      htg
  rw [← e7] at hout
  obtain ⟨W, D1, D2, hz⟩ := hrow
  refine hbad (_, _) (congrArg (Option.map fun xo => (xo, (G.blk (G.L.V1 Ex)).imp a.2 _)) hout) hRd
      ?_ ?_
  · exact (G.L.row_iff _ m).1 ((uholds_conv G.L _ m).2 ((tRow Ex a.2 W m D1 D2).1 hz))
  · exact (ev_conv G.L _ m).2 ((tEnd m).2 hev)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_plain
