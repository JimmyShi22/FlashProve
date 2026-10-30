-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Out.lean: from the decision's yes on the written rounds as they are shown,
to
the typed transcript. Theorems with their proofs.

Main names:
  `tapeE_strict`: the merge's maker of the tape: all items of every round behind the first are
    scalars.
  `flatOf_noDigest`, `zip_noDigest`: a round without its sealed digest is the same plain data.
  `decide_view`: where the stretch fits the block's declared rounds, every drawn element's words are
    below the prime and `headMergeDecide` says yes, there are the values heard, pinned by facts on
    the two records, and the image of the transcript under `mergeMaps` is `sumTr` at them.

Limits. "If it says yes, then". Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.View

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading wsForkStart)
open OnBytes.K.Kc (leading flatOf)
open VerifiableInference.Desc (roundsFit noDigest fieldPrimeWord need named)
open VerifiableInference.Desc.First.Look (elemsOf tapeS)
open VerifiableInference.OnPublicFiles (MergeCaller)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headClaimMergeKind mergeEntries mergeTapeE)
open OnBytes.Tie.Pv.Lay.Eng (sumTr sumOut)
open _root_.Run (ckP)

/-- The merge's maker of the tape: all items of every round behind the first are scalars. -/
theorem tapeE_strict {rs : List Fmt.RoundView} {es : List Fmt.Entry} {tp : OnBytes.K.Kc.Tape} (h :
           mergeTapeE rs es = .ok tp) :
    ∀ r ∈ rs.tail, elemsOf r.vals = some (leading r.vals) := by
  match rs, es, h with
  | [], _, h => simp [mergeTapeE] at h
  | _ :: _, [], h => simp [mergeTapeE] at h
  | r :: rs, e :: es, h =>
    by_cases h1 : VerifiableInference.Desc.First.Door.batchEntryB e = true
    · by_cases h2 : VerifiableInference.Desc.First.Door.batchRoundB e r = true
      · cases ht : tapeS rs es with
        | none => simp [mergeTapeE, need, named, h1, h2, ht, bind, Except.bind] at h
        | some t => exact tapeS_strict rs es t ht
      · simp [mergeTapeE, need, h1, h2, bind, Except.bind] at h
    · simp [mergeTapeE, need, h1, bind, Except.bind] at h

/-- A round without its sealed digest is the same plain data. -/
theorem flatOf_noDigest (r : Fmt.RoundView) (e : Option Fmt.Entry) : flatOf (noDigest r) e = flatOf r e :=
    rfl

theorem zip_noDigest : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry),
    (((rs.map noDigest).zip es).map fun x => flatOf x.1 (some x.2)) = (rs.zip es).map fun x =>
        flatOf x.1 (some x.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | r :: rs, e :: es => by
    simp only [List.map_cons, List.zip_cons_cons, zip_noDigest rs es, flatOf_noDigest]

/-- **From the decision's yes on the written rounds as they are shown, to the typed transcript.** -/
theorem decide_view (P : HeadMergeP) (G : WeightsL GE) (Ex : ExtSpec) {dZ d0 : RDT} {ds : List RDT}
    {dY dV : RDT}
    (hk : ds.length = G.k) (τ : Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV])))) {s s' : S}
    (hfit : roundsFit (headClaimMergeKind P).rounds ((rvT (ckP .two) _ τ).map noDigest) = true)
    (hw : ∀ r ∈ (rvT (ckP .two) _ τ).map noDigest, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 <
        fieldPrimeWord ∧ x.2.2 < fieldPrimeWord)
    (h : headMergeDecide P s ((rvT (ckP .two) _ τ).map noDigest) = .ok s') :
    ∃ (a a' : HeadOwn) (claim : OnBytes.Model.WsClaim) (x0 : OnBytes.Model.Head.Heard) (wo :
        OnBytes.Model.WsForkOut)
      (x mu cY beta v T : E) (qs : List (Nat × List E × E)) (hβ : Reading.gl.val beta ≠ 0),
      s.here = .head a ∧ s'.here = .head a' ∧ a.claim = some claim ∧ a.x = some x0 ∧ a'.wo = some wo
          ∧
      a.F.publicPart (wsForkStart #[x0.sV] (OnBytes.Model.powers x 1)) = some T ∧ wo.p.target = T ∧
          wo.beta = beta ∧
      qs.length = P.lay.lk ∧ (∀ q ∈ qs, q.2.1.length = 2) ∧ wo.rm.toList = qs.map (·.2.2) ∧
      wo.recs = (#[claim].zip (OnBytes.Model.powers x 1)).toList.map (fun y =>
        OnBytes.Model.wsRowPart P.lay y.1 (OnBytes.mulE y.2 (OnBytes.Model.wsEpsT P.lay y.1 wo.rm)))
            ∧
      OnBytes.Model.Road.Ended wo.p (wsForkStart #[x0.sV] (OnBytes.Model.powers x 1)) T mu wo.p.eps
          a.F.next
        (List.replicate P.lay.lk (OnBytes.Psc.Weight.plain 3)) (qs.map fun q => (q.2.1, q.2.2)) 1
            [cY] beta ∧
      (∃ Gf : OnBytes.Model.Fork, ({ a.F with next := a.F.next + 1 + 2 * P.lay.lk + 2 } :
          OnBytes.Model.Fork).hideRun wo.sFv #[v] beta =
        some Gf ∧ Gf.shown wo.sFv = some wo.fvp ∧ a'.F = { Gf with planClaimsF := P.nLin }) ∧
      (mergeMaps G Ex dZ d0 ds dY dV hk).view τ =
        (((), ()), Reading.gl.val x, ((), Reading.gl.val mu), Reading.gl.val wo.p.eps,
          sumTr Reading.gl G.L.toSum (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ =>
              Reading.gl.val v) := by
  obtain ⟨b', wo', hb', hwo', hne⟩ := beta_nonzero P hfit hw h
  obtain ⟨a, a', tp, Gf, claim, x0, wo, ha, ha', hcl, hx, hwo, ht, hm, hF', _⟩ := decide_inv h
  have hab : b' = a' := by
    rw [ha'] at hb'
    exact (Here.head.inj hb').symm
  have hww : wo' = wo := by
    rw [hab, hwo] at hwo'
    exact (Option.some.inj hwo').symm
  rw [hww] at hne
  obtain ⟨hlen, htp⟩ := tapeIs _ _ tp ht
  have hstrict := tapeE_strict ht
  obtain ⟨x, mu, cY, beta, v, T, r1, rY, rV, qs, hn, hq, et, hT, hE, hrm, hbeta, _, hhide, hshown,
      hrecs⟩ := hear_ended hm
  rw [hbeta] at hne
  obtain ⟨mZ', cZ', m0', c0', τ'⟩ := τ
  rw [zip_noDigest] at htp
  rw [et] at htp
  have hrv : rvT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV])) (mZ', cZ', m0', c0', τ') =
      rvOne dZ mZ' cZ' :: rvOne d0 m0' c0' :: rvT (ckP .two) (ds ++ [dY, dV]) τ' := rfl
  rw [hrv] at htp hlen hstrict
  simp only [mergeEntries, List.zip_cons_cons, List.map_cons, List.cons.injEq] at htp
  obtain ⟨t0, t1, t2⟩ := htp
  have h0 : (rvOne dZ mZ' cZ').drawn.elems.map E.ofTriple = [x] := (congrArg (·.drawn) t0).symm
  have h1s : leading (rvOne d0 m0' c0').vals = [mu] := (congrArg (·.sent) t1).symm
  have h1' : (rvOne d0 m0' c0').drawn.elems.map E.ofTriple = [wo.p.eps] := (congrArg (·.drawn)
      t1).symm
  have hs1 : elemsOf (rvOne d0 m0' c0').vals = some [mu] := by
    have := hstrict (noDigest (rvOne d0 m0' c0')) (by simp)
    rw [← h1s]
    exact this
  have h2 : HeardAs (rvT (ckP .two) (ds ++ [dY, dV]) τ') (qs.map (fun q => (q.2.1, q.2.2)) ++
      [([cY], beta)]) v := by
    refine heardAs_of_tape _ _ _ rY rV cY beta v qs _ _ ?_ ?_ t2.symm
    · simpa [mergeEntries] using hlen
    · intro r hr
      exact hstrict (noDigest r) (by
        simp only [List.map_cons, List.tail_cons, List.mem_cons, List.mem_map]
        exact Or.inr ⟨r, hr, rfl⟩)
  exact ⟨a, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hne, ha, ha', hcl, hx, hwo,
    by simpa using hT, hE.target, hbeta,
    hn, hq, hrm, by simpa using hrecs, by simpa using hE, ⟨Gf, hhide, hshown, hF'⟩,
    whole_view G Ex hk mZ' cZ' m0' c0' τ' x mu wo.p.eps cY beta v _ hne h0 hs1 h1' h2⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.decide_view
