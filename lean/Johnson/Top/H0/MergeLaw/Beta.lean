-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Beta.lean: the merge's last challenge reads other than 0 in the library's
extension field. Theorems with their proofs.

Main names:
  `roundsFit_at`: where a stretch fits a list of declared rounds (`roundsFit`,
    Johnson/Desc/Block.lean), the round at a place of the list passes the test on draws other than
    0.
  `nzFit_one`: that test at an entry with one drawn element, which is marked as never 0.
  `gl_ne_zero`: a triple of words below the prime that is not (0, 0, 0) reads other than 0.
  `beta_nonzero`: where the stretch fits the block's declared rounds, every drawn element's words
    are below the prime, and the decision says yes.
  `words_of_okViewW`: the premise on words, out of the description's own test on a view's words.
  `claim_says_gl`: `claim_says` (Johnson/Top/H0/MergeLaw/Says.lean) at `Reading.gl`, with its
  premise on
    the last challenge paid.

The library's toE_inj and toE_zeroE (OnBytes/Slice/Field.lean) and `Reading.gl`
(OnBytes/Model/HideLaws.lean) are spent: statements on plain values.

Limits. The decision itself does not ask that the challenge is not 0: the step in front of it does.
`claim_says_gl` keeps three premises of `claim_says`: `Sized`, (D1) and (D2). Nothing on soundness,
on
an honest prover or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E zeroE)
open OnBytes.K.Kc (Tape flatOf)
open OnBytes.Model (Reading RoundName)
open VerifiableInference.Desc (roundsFit drawsMarkedNonzeroHaveNonzeroWords viewWordsBelowPrime fieldPrimeWord)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headClaimMergeKind mergeEntries)

/-- Where the rounds fit a list of declared rounds, the round at a place of the list passes the test
on draws other than 0. -/
theorem roundsFit_at : ∀ (A : List Fmt.DeclaredRound) (d : Fmt.DeclaredRound) (B : List Fmt.DeclaredRound) (rs :
                List Fmt.RoundView),
    roundsFit (A ++ d :: B) rs = true →
    ∃ rsA r rsB, rs = rsA ++ r :: rsB ∧ rsA.length = A.length ∧ drawsMarkedNonzeroHaveNonzeroWords d r = true
  | [], d, B, [], h => by simp [roundsFit] at h
  | [], d, B, r :: rs, h => by
    simp only [List.nil_append, roundsFit, Bool.and_eq_true] at h
    exact ⟨[], r, rs, rfl, rfl, h.1.2⟩
  | a :: A, d, B, [], h => by simp [roundsFit] at h
  | a :: A, d, B, r :: rs, h => by
    simp only [List.cons_append, roundsFit, Bool.and_eq_true] at h
    obtain ⟨rsA, r', rsB, e, hl, hz⟩ := roundsFit_at A d B rs h.2
    exact ⟨r :: rsA, r', rsB, by rw [e]; rfl, by simp [hl], hz⟩

/-- A word below the prime, as the format's test has it. -/
theorem ok_of_lt {w : UInt64} (h : w < fieldPrimeWord) : Fmt.Fld.two.ok w = true := by
  have : w.toNat < fieldPrimeWord.toNat := UInt64.lt_iff_toNat_lt.1 h
  simpa [Fmt.Fld.ok, Fmt.Fld.p, fieldPrimeWord] using this

/-- A triple of words below the prime that is not (0, 0, 0) reads other than 0 in the library's
extension field. -/
theorem gl_ne_zero {x : Fmt.Ext} (h1 : x.1 < fieldPrimeWord) (h2 : x.2.1 < fieldPrimeWord) (h3 : x.2.2 < fieldPrimeWord) (hx
                            : x ≠ (0, 0, 0)) :
    Reading.gl.val (E.ofTriple x) ≠ 0 := by
  intro h
  have h' : OnBytes.Slice.toE x = OnBytes.Slice.toE Fmt.Fld.zeroE := by
    rw [OnBytes.Slice.toE_zeroE]
    exact h
  refine hx (OnBytes.Slice.toE_inj x Fmt.Fld.zeroE ?_ (by decide) h')
  simp [Fmt.Fld.okE, ok_of_lt h1, ok_of_lt h2, ok_of_lt h3]

/-- What a tape made of a stretch holds of the draws, round by round. -/
theorem tape_drawn {rs : List Fmt.RoundView} {es : List Fmt.Entry} (h : rs.length = es.length) :
    ((rs.zip es).map fun x => flatOf x.1 (some x.2)).map (·.drawn) = rs.map fun r =>
        r.drawn.elems.map E.ofTriple := by
  have : ((rs.zip es).map fun x => flatOf x.1 (some x.2)).map (·.drawn) =
      ((rs.zip es).map Prod.fst).map fun r => r.drawn.elems.map E.ofTriple := by
    simp [flatOf, List.map_map, Function.comp_def]
  rw [this, List.map_fst_zip (by omega)]

/-- The test on draws other than 0, at an entry with one drawn element, which is marked so. -/
theorem nzFit_one {d : Fmt.DeclaredRound} {r : Fmt.RoundView} {x : Fmt.Ext} (hE : d.entry.drawE = 1) (hN :
               d.entry.drawNZ = 1)
    (hr : r.drawn.elems = [x]) (h : drawsMarkedNonzeroHaveNonzeroWords d r = true) : x ≠ (0, 0, 0) := by
  unfold drawsMarkedNonzeroHaveNonzeroWords at h
  cases hk : Fmt.kindOf d.entry.name with
  | none => simp [hk] at h
  | some k =>
    by_cases hs : k = .seeds
    · simpa [hk, hs, Fmt.dsElems, Fmt.dsSeeds, hE, hN, hr] using h
    · simpa [hk, hs, Fmt.dsElems, hE, hN, hr] using h

/-- **The last challenge reads other than 0.** -/
theorem beta_nonzero (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (hfit : roundsFit (headClaimMergeKind P).rounds rs = true)
    (hw : ∀ r ∈ rs, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord)
    (h : headMergeDecide P s rs = .ok s') :
    ∃ a' wo, s'.here = .head a' ∧ a'.wo = some wo ∧ Reading.gl.val wo.beta ≠ 0 := by
  obtain ⟨a, a', tp, G, _, _, wo, _, ha', _, _, hwo, ht, hm, _⟩ := decide_inv h
  obtain ⟨hlen, htp⟩ := tapeIs rs _ tp ht
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, _, et, _, _, _, hbeta, _⟩ := hear_ended hm
  refine ⟨a', wo, ha', hwo, ?_⟩
  have hD := tape_drawn hlen
  rw [← htp, et] at hD
  have hrounds : (headClaimMergeKind P).rounds =
      ((({ name := RoundName.batSigma.name, work := P.work, drawE := 1, rows := 1 } : Fmt.Entry) ::
        { name := RoundName.pscEpsilon.name, work := P.work, msg := 24, drawE := 1 } ::
        List.replicate P.lay.lk
          { name := RoundName.pscRound.name, work := P.work, msg := 48, drawE := 1 }).map
          fun e => ({ entry := e } : Fmt.DeclaredRound)) ++
      { entry :=
          { name := RoundName.pscY.name, work := P.work, msg := 24, drawE := 1, drawNZ := 1 } } ::
      [{ entry := { name := RoundName.pscValues.name, msg := 24 } }] := by
    simp [headClaimMergeKind, mergeEntries]
  rw [hrounds] at hfit
  obtain ⟨rsA, r, rsB, ers, hlA, hz⟩ := roundsFit_at _ _ _ _ hfit
  have hlA' : rsA.length = P.lay.lk + 2 := by simpa using hlA
  rw [ers] at hD
  have hD' : ([x] :: [wo.p.eps] :: qs.map fun q => [q.2.2]) ++ [beta] :: [[]] =
      rsA.map (fun r => r.drawn.elems.map E.ofTriple) ++
        (r.drawn.elems.map E.ofTriple) :: rsB.map (fun r => r.drawn.elems.map E.ofTriple) := by
    simpa [rd, List.map_map, Function.comp_def] using hD
  have hcut := (List.append_inj hD' (by simp [hn, hlA'])).2
  simp only [List.cons.injEq] at hcut
  have hel : r.drawn.elems.map E.ofTriple = [beta] := hcut.1.symm
  obtain ⟨x0, hx0, hb0⟩ : ∃ x0, r.drawn.elems = [x0] ∧ E.ofTriple x0 = beta := by
    cases hr : r.drawn.elems with
    | nil => simp [hr] at hel
    | cons y l =>
      cases l with
      | nil => exact ⟨y, rfl, by simpa [hr] using hel⟩
      | cons _ _ => simp [hr] at hel
  have hne : x0 ≠ (0, 0, 0) := nzFit_one rfl rfl hx0 hz
  have hmem : r ∈ rs := by rw [ers]; simp
  obtain ⟨w1, w2, w3⟩ := hw r hmem x0 (by rw [hx0]; simp)
  rw [hbeta, ← hb0]
  exact gl_ne_zero w1 w2 w3 hne

/-- The premise on words, out of the description's own test on a view's words. -/
theorem words_of_okViewW {v : Fmt.View} (h : viewWordsBelowPrime v = true) :
    ∀ r ∈ v.rounds, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord := by
  intro r hr x hx
  simp only [viewWordsBelowPrime, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have := (h.1 r hr).1 x hx
  exact ⟨this.1.1, this.1.2, this.2⟩

open Iop Cb Cb.Pv.Lay in
open OnBytes.Model (World) in
open OnBytes.Model.Road (Sized) in
open OnBytes.Tie.Pv.Lay.Eng (sumOut) in
open VerifiableInference.Desc (Claim) in
open Johnson.Desc.First.ForkMerge (headMergeClaim) in
/-- **What the merge's claim says, in the library's extension field, with the premise on the last
challenge paid**: `claim_says` at
`Reading.gl`, where the stretch has passed the step's test on rounds and the test on a view's words.
-/
theorem claim_says_gl (P : HeadMergeP) (L : MergeL Cb.Gl.E) (hk : L.k = P.lay.lk) {s s' : S} {rs :
    List Fmt.RoundView}
    (hfit : roundsFit (headClaimMergeKind P).rounds rs = true)
    (hw : ∀ r ∈ rs, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord)
    (h : headMergeDecide P s rs = .ok s') (st : L.St) :
    ∃ (a a' : HeadOwn) (wo : OnBytes.Model.WsForkOut) (mu c beta v : E) (qs : List (Nat × List E ×
        E))
      (hβ : Reading.gl.val beta ≠ 0),
      s.here = .head a ∧ s'.here = .head a' ∧ a'.wo = some wo ∧ wo.beta = beta ∧
      ∀ (_ : Sized a.F) (n : Nat) (s₂ s₃ : S) (a₂ : HeadOwn) (cls : List Claim),
        s₂.here = .head a₂ → a₂.wo = a'.wo → headMergeClaim n s₂ = .ok (cls, s₃) →
        ∃ form, cls = [{ form := form }] ∧
          ∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World Cb.Gl.E) (m : L.J → Cb.Gl.E),
            L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st) wo.p.first →
            L.toSum.T.par.inc st m = Reading.gl.val wo.p.target - wo.p.start.value Reading.gl W →
            (form.value Reading.gl W = 0 ↔
              L.toSum.T.par.UHolds (sumOut Reading.gl L.toSum (fun st => pick (L.toSum.T.par.vars
                  st)) st
                wo.p.target mu wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [c] beta hβ
                fun _ => Reading.gl.val v) m) := by
  obtain ⟨a, a', wo, mu, c, beta, v, qs, ha, ha', hwo, hbeta, H⟩ := claim_says Reading.gl P L hk h
      st
  obtain ⟨b', wo', hb', hwo', hne⟩ := beta_nonzero P hfit hw h
  have hab : b' = a' := by
    rw [ha'] at hb'
    exact (Here.head.inj hb').symm
  have hww : wo' = wo := by
    rw [hab, hwo] at hwo'
    exact (Option.some.inj hwo').symm
  rw [hww, hbeta] at hne
  exact ⟨a, a', wo, mu, c, beta, v, qs, hne, ha, ha', hwo, hbeta, fun hz => H hz hne⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.beta_nonzero
#print axioms VerifiableInference.Desc.First.MergeLaw.claim_says_gl
