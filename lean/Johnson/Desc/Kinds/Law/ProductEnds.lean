-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ProductEnds.lean.
WHAT IT DOES NOT SHOW. A TOY: an honest prover's rounds BUILT IN
LEAN; no file in scope; not what the prover's program sends. That a kind's two tables are what its
reads say: not here. Premises: the ledger in front is WellLaid and Fresh. beta may be 0. No
soundness, no probability, nothing on hiding.
WHAT IT IS. "sumcheck z 2" OF A PRODUCT OF TWO TABLES A, B, SENT HONESTLY, WITH THE HONEST END
VALUES, FOR ALL DRAWS: one statement for the head's two sumchecks of that make ("normed"; the head's
own).
  SmAB           the summand, the further variable last: Law/Normed.lean's SmN and
                 Law/Lemma2b.lean's SmP are it, by rfl, at their points and tables.
  product_hend   the summand at the challenges is the product of the two end values as shown.
  product_sends  for every eps and challenges: rounds t, canonical, on which sumcheck z 2 returns;
                 a Fresh ledger behind; SumTrueG; no draw is bad under Law/SumLaw.lean's badG; in
                 every world whose slots are the hidden scalars behind the rounds: the claimed
                 sum's variable is worth sig; the sumcheck's own form, on the end values as shown,
                 is worth 0; the two end values' variables are worth the tables' extensions at the
                 challenges.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE okE)
open OnBytes.Model (Aff Fork Reading World)
open Polynomial
open Came (val)
open Part.MaskedSum (Var Call rvOf readAll leadScalars movesOf ownSlots rowForm challenges)
open OnBytes.Desc.First.P1 (IsSum mle ext1)
open Came (vsG kG cvG tqG muG specG hcoefG sEndG badG)

/-- The summand of a product of two tables, the further variable last. -/
noncomputable def SmAB (z : Point) (A B : List Bool → K) (mask : Nat → E) (F0 : Fork) :
    List K → K := fun rs =>
  mle ((vsG z).length + 1) (ext1 (vsG z).length A (rd (mask (sEndG z 2 F0)))) rs *
    mle ((vsG z).length + 1) (ext1 (vsG z).length B (rd (mask (sEndG z 2 F0 + 1)))) rs

theorem vsG_len (z : Point) : (vsG z).length = z.size := by
  unfold vsG
  rw [List.length_map, Array.length_toList]

theorem product_hend (z : Point) (A B : List Bool → K) (mask : Nat → E) (F0 : Fork)
    (rsE : List E) (hr : rsE.length = z.size + 1) (sh0 sh1 : E)
    (h0 : rd sh0 = mle (vsG z).length A ((rsE.take z.size).map rd) +
      rd (rsE.getLastD zeroE) * rd (mask (sEndG z 2 F0 + 0)))
    (h1 : rd sh1 = mle (vsG z).length B ((rsE.take z.size).map rd) +
      rd (rsE.getLastD zeroE) * rd (mask (sEndG z 2 F0 + 1))) :
    SmAB z A B mask F0 (rsE.map rd) = rd (sh0 * sh1) := by
  have hlen : ((rsE.take z.size).map rd).length = (vsG z).length := by
    rw [List.length_map, List.length_take, hr, vsG_len]
    omega
  unfold SmAB
  rw [map_split rsE _ hr, Part.MaskedSum.product_at (vsG z).length _ _ _ _ _ _ hlen, rd_mul, h0,
    h1]
  simp only [Nat.add_zero]

/-- "sumcheck z n" at the truth, in Law/SumLaw.lean's letters: the claimed sum hides the true sum;
each round's completed polynomial is the true round polynomial. (Law/NormTrue.lean's ProductsTrue
and Law/RowTrue.lean's NormedTrue are it at their letters.) -/
def SumTrueG (z : Point) (n : Nat) (hn : 1 ≤ n) (Sm : List K → K) (sig : K)
    (hS : IsSum ((⟨1, vsG z, some ⟨2, n⟩⟩ : Call).all.map (Var.wt Reading.gl)) Sm sig)
    (mask : Nat → E) (F0 : Fork) (t : List Fmt.RoundView) : Prop :=
  ∀ R c0, readAll (kG z n) t = some R → leadScalars (kG z n) t = some [c0] →
    cvG mask F0 c0 = sig ∧
    ∀ i m, (movesOf Reading.gl (kG z n).all R.rounds
        (addE R.mu (mulE R.eps (tgt c0))))[i]? = some m →
      m.1 = tqG z n hn Sm sig hS mask F0 (rd (tgt c0)) sig (rd R.mu) (rd R.eps)
        (((movesOf Reading.gl (kG z n).all R.rounds
          (addE R.mu (mulE R.eps (tgt c0)))).take i).map (·.2))

variable [Sizes] [Policy] [Request] [Token]

/-- **"sumcheck z 2" OF A PRODUCT OF TWO TABLES, SENT HONESTLY, FOR ALL DRAWS.** -/
theorem product_sends (z : Point) (A B : List Bool → K) (mask : Nat → E) {F0 : Fork}
    (W0 : WellLaid F0) (sig : K)
    (hS : IsSum ((⟨1, vsG z, some ⟨2, 2⟩⟩ : Call).all.map (Var.wt Reading.gl))
      (SmAB z A B mask F0) sig) {m : Nat}
    (hF : Fresh F0 (1 + (ownSlots (callOf 1 z 2).all + 2 + m))) (eps : E)
    (rsE : List E) (hr : rsE.length = z.size + 1)
    (oke : okE eps = true) (okr : ∀ x ∈ rsE, okE x = true) :
    ∃ (t : List Fmt.RoundView) (S : Sum) (G : Fork),
      Shaped (eps :: rsE) t (sumcheck.rounds z.size 2) ∧
      t.length = z.size + 3 ∧ Canonical t ∧ sumcheck z 2 F0 t = some (S, G, []) ∧
      G.next = F0.next + 1 + ownSlots (callOf 1 z 2).all + 2 ∧ G.ns = F0.ns ∧ Fresh G m ∧
      SumTrueG z 2 (by omega) (SmAB z A B mask F0) sig hS mask F0 t ∧
      NoBad (badG z 2 (by omega) (SmAB z A B mask F0) sig hS mask F0) t ∧
      S.r = (rsE.take z.size).toArray ∧
      ∀ Wd : World K, (∀ j, F0.next ≤ j → j < G.next → Wd.slot j = rd (hidden G mask j)) →
        val Wd S.claimed.var = sig ∧
        val Wd (S.left ((S.end_ 0).shown * (S.end_ 1).shown)) = 0 ∧
        val Wd (S.end_ 0).var = mle (vsG z).length A (S.r.toList.map rd) ∧
        val Wd (S.end_ 1).var = mle (vsG z).length B (S.r.toList.map rd) := by
  generalize hvals : endsOf mask (sEndG z 2 F0) 2
    (fun j => if j = 0 then mle (vsG z).length A ((rsE.take z.size).map rd)
      else mle (vsG z).length B ((rsE.take z.size).map rd))
    (rd (rsE.getLastD zeroE)) = values
  have hv : values.length = 2 := by rw [← hvals, endsOf_length]
  have okv : ∀ x ∈ values, okE x = true := by
    rw [← hvals]
    exact endsOf_ok _ _ _ _ _
  generalize hc0 : ofK (sig + rd (mask F0.next)) = c0
  have hcv : cvG mask F0 c0 = sig := by
    unfold cvG
    rw [← hc0, rd_ofK]
    ring
  obtain ⟨MU, hMU⟩ : ∃ MU, MU = muG z 2 (by omega) (SmAB z A B mask F0) sig hS mask F0
    (rd (tgt c0)) sig := ⟨_, rfl⟩
  obtain ⟨t, l, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := sumcheck_honest z (n := 2) (by omega)
    (F := F0) (m := m) W0 c0 hF (hcoefG mask F0) (SmAB z A B mask F0) sig MU
    (tqG z 2 (by omega) (SmAB z A B mask F0) sig hS mask F0 (rd (tgt c0)) sig MU)
    (fun e rs hl => by
      rw [hMU]
      exact (specG z 2 (by omega) (SmAB z A B mask F0) sig hS mask F0 (rd (tgt c0))
        sig).2.2.2.2.2.2 rfl _ e rs hl)
    eps rsE values hr hv (by rw [← hc0]; exact okE_ofK _) oke okr okv
  obtain ⟨S, G, b1, b2, b3, b4, b5⟩ := a7 []
  rw [List.append_nil] at b1
  have b3' : G.next = F0.next + 1 + ownSlots (callOf 1 z 2).all + 2 := b3
  obtain ⟨c0', R, T', c1, c2, _, c4, _, c6, c7, c8, c9⟩ := sumcheck_ends W0 b1 mask
  have hRR : R = ⟨ofK _, eps, l, values⟩ := Option.some.inj (c2.symm.trans a3)
  have hcc : c0' = c0 := by
    have := Option.some.inj (c1.symm.trans a4)
    simpa using this
  subst hRR hcc
  have hSr : S.r = (rsE.take z.size).toArray := by
    rw [c6]
    show ((l.map (·.2)).take (z.toList.map (Var.point · 3)).length).toArray = _
    rw [a5, List.length_map, Array.length_toList]
  have hsE : F0.next + 1 + ownSlots (callOf 1 z 2).all = sEndG z 2 F0 := rfl
  have hq : ∀ (i : Nat) (m' : K[X] × K), (movesOf Reading.gl (kG z 2).all l
      (addE (ofK MU) (mulE eps (tgt c0'))))[i]? = some m' →
      m'.1 = tqG z 2 (by omega) (SmAB z A B mask F0) sig hS mask F0 (rd (tgt c0')) sig
        (rd (ofK MU)) (rd eps) (((movesOf Reading.gl (kG z 2).all l
          (addE (ofK MU) (mulE eps (tgt c0')))).take i).map (·.2)) := by
    intro i m' hm
    have hp := poly_of_honest _ _ _ a6 i m' hm
    rw [rd_ofK]
    exact hp
  refine ⟨t, S, G, a0, a1, a2, b1, b3', b4, b5, ?_,
    noBadG_true z 2 (by omega) _ sig hS mask F0 a3 a4 hcv hq, hSr, ?_⟩
  · intro R c0'' hR hl
    have hRR : R = ⟨ofK _, eps, l, values⟩ := Option.some.inj (hR.symm.trans a3)
    have hcc : c0'' = c0' := by
      have := Option.some.inj (hl.symm.trans a4)
      simpa using this
    subst hRR hcc
    exact ⟨hcv, hq⟩
  · intro Wd hWs
    have hcl : (((hidOf F0.next [c0']).getD 0 {}).var).value Reading.gl Wd = sig := by
      rw [hidOf_one]
      show OnBytes.Model.Aff.value Reading.gl Wd (Aff.slot (F0.next + 0)) = _
      rw [OnBytes.Model.Aff.value_slot, Nat.add_zero, hWs _ (le_refl _) (by rw [b3']; omega), c7]
      exact hcv
    have hsh : ∀ q, q < 2 → rd (S.end_ q).shown =
        (if q = 0 then mle (vsG z).length A ((rsE.take z.size).map rd)
          else mle (vsG z).length B ((rsE.take z.size).map rd)) +
        rd (rsE.getLastD zeroE) * rd (mask (sEndG z 2 F0 + q)) := by
      intro q hq
      rw [(c9 q hq).1]
      show rd (values.getD q zeroE) = _
      rw [← hvals, endsOf_getD _ _ _ _ _ hq]
    have hend : ∀ q, q < 2 → val Wd (S.end_ q).var =
        if q = 0 then mle (vsG z).length A ((rsE.take z.size).map rd)
          else mle (vsG z).length B ((rsE.take z.size).map rd) := by
      intro q hq
      rw [(c9 q hq).1]
      show OnBytes.Model.Aff.value Reading.gl Wd (Aff.slot _) = _
      rw [OnBytes.Model.Aff.value_slot, hWs _ (by omega) (by rw [b3']; omega), (c9 q hq).2]
      show rd (values.getD q zeroE) - rd ((l.map (·.2)).getLastD zeroE) * _ = _
      rw [a5, ← hvals, endsOf_getD _ _ _ _ _ hq, hsE]
      ring
    refine ⟨by rw [c4]; exact hcl, ?_, ?_, ?_⟩
    · unfold Sum.left
      rw [b2]
      refine a8 Wd _ {} hcl (fun i hi => ?_) ?_
      · show Wd.slot (F0.next + 1 + i) = _
        rw [hWs _ (by omega) (by rw [b3']; omega), c8 i hi]
        rfl
      · rw [OnBytes.Model.Aff.value_empty, add_zero]
        exact product_hend z A B mask F0 rsE hr _ _ (hsh 0 (by omega)) (hsh 1 (by omega))
    · rw [hend 0 (by omega), hSr]
      rfl
    · rw [hend 1 (by omega), hSr]
      rfl

end VerifiableInference.Desc.Kinds.Head.Law
