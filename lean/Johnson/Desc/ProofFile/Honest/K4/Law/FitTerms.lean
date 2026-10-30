-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FitTerms.lean: CONDITIONAL. Statements with their proofs.

What is here: one of the fifteen clauses of `k4MakersFit` (Honest/K4/Part.lean), the clause on the
makers of the public test on the parts of the feed-forward layers' own rounds (the sub-protocol K4),
GENERAL IN THE INPUT w AND THE SAMPLED VALUES p: THE SECOND TOKEN SUMCHECK's JOB IS MADE AND HAS ITS
CALL's PUBLIC SHAPE (`jobTerms`, Johnson/Desc/K4/Honest/Terms.lean). FROM: that `Sides.of` has
returned (Law/SidesWhole.lean has that from public premises); the public facts `K4Plan`, hU, hl; the
test with code `pansB` at the plan's own arguments; the lookup's token point has lt coordinates.
How. At every point of lt coordinates the reads are made (`readsAt_of_lay`), the values to be shown
are made and are as many as the verifier counts (`endsOn_there`), the panels are made at these
values (`panels_return`) and so are the second pass's products (`trips_there`): the four files lie
in Johnson/Road/K4/C/. So a row is made for each token. The maker's three tests: the products are as
many at each token as at the first (`trips_rel`, Law/SkelTerms.lean); their weights are the same
(`sameWeights_true`, there); the cube's sizes fit (`fits_of`).

Not shown here. That `pansB` is true (Johnson/Road/K4/C/PansBPlan.lean has it from the verifier's
lines and five facts on the plan; not called here). That a plan with the public facts exists. A
RETURN AND A SHAPE: nothing on what a table, a product or an end value is worth. Nothing on
soundness, on completeness or on any other property. No property is claimed.

  `tok_step`   at a point of lt coordinates: the reads, the values, the products
  `tokenRows_there`   a row for each token
  `terms_fit_on`   the job, made of what `Sides.of` has returned
  `terms_fit`   **the clause**, in the form ∃ j, the maker returns j, and j has the call's shape
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelTerms
import Johnson.Desc.ProofFile.Honest.K4.Law.AtEnds
import Johnson.Road.K4.C.TripsThere
import Johnson.Road.K4.C.EndsThere
import Johnson.Road.K4.C.TermsOpen
import Johnson.Road.K4.C.TermsPubKit
import Johnson.Road.K4.C.TermsField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 eqTab longPoint orderDefault)
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks nEndT)
open OnBytes.Road (admitted_of_layout)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (envPub envOf_pub amapM_there readsAt_of_lay ptAt_has tok_two endsOn_there
  panels_return trips_there sides_fields sides_seven tokenRows_trips tokenRows_size
  termsCube endMapsOf aMapsOf bMapsOf)
open OnBytes.Desc.First.K4.RtPub (pansB blankEnv nclpOf)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw (fits_of)
open Inst.Model.FFSeg (Dim)

/- under this namespace the bare name is the frame's -/
local notation "firstC" => OnBytes.Road.K4.C.firstOf

/- `Sides` in full: the frame has a name ProofFile.Honest.Sides -/
variable {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides} {iU3 : ℕ}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- CONDITIONAL on every hypothesis named. **At a point of lt coordinates**: the reads, the values
to be shown, as many as the verifier counts, and the second pass's products are made. -/
theorem tok_step (A : K4Plan hS pc Q.P Q.g tl D) (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hPB : pansB Q.P (blankEnv Q.P Q.hp Q.g iU3 r.1) Q.hp.lamS (nclpOf Q.hp Q.g) = true)
    (h : Sides.of Q w p = some S) {z : Array E} (hz : z.size = Q.P.y.h.lt) (et : Array E)
    (hh : ℕ → ℕ → E) :
    ∃ R sh tr, S.readsTok z = some R ∧ endsOn S R = some sh ∧ sh.size = nEndT Q.P.y ∧
      S.trips R et hh sh = some tr := by
  obtain ⟨eQ, ew, ef, hv, _, _, _⟩ := sides_fields h
  obtain ⟨_, _, hy, hlow, hT, _, _⟩ := sides_seven A h
  obtain ⟨H0, _, _, hE⟩ := OnBytes.Road.K4.C.sides_ends h
  have ev : S.v = envPub Q r.1 iU3 p.fo.zk := Option.some.inj (hv.symm.trans (envOf_pub hU hl p))
  have ht : S.v.tab = r.1 := by rw [ev]; rfl
  have hyQ : S.v.y = Q.P.y := by rw [ev]; rfl
  have Ad := admitted_of_layout A.lay A.sw.p3
  have hp3 : S.v.y.h.p3 = true := by
    rw [hyQ, Ad.shape]
    exact A.sw.p3
  have hla : Q.P.y.ls + Q.P.y.h.lt = Q.P.y.h.la := by
    rw [Ad.shape, Ad.la]
  have hTQ : Q.P.y.T = 2 ^ Q.P.y.h.lt := by
    rw [← hyQ]
    exact hT
  have hY : (longPoint S.zlow z).size = Q.P.y.h.la := by
    unfold longPoint
    rw [Array.size_append, hlow, hyQ, hz, hla]
  obtain ⟨R, hR0⟩ := readsAt_of_lay hl w p.fo [("rt", z), ("Y", longPoint S.zlow z)]
  have hR : S.readsTok z = some R := by
    unfold Sides.readsTok
    rw [eQ, ew, ef]
    exact hR0
  obtain ⟨p1, _⟩ := tok_two Q.P.y S.zlow z hz hY
  have H := ptAt_has (v := S.v) A.reads hl hR0 hTQ hla ht
  obtain ⟨sh, hsh, hn⟩ := endsOn_there hE hp3 H p1
  rw [hyQ] at hn
  obtain ⟨pans, _, hPan, _, _, _, hEnd⟩ := panels_return h hU hl hPB hn
  obtain ⟨fin, hfin⟩ := hEnd (Array.replicate Q.hp.lamS zeroE) (Array.replicate 2 zeroE)
    (Array.replicate (1 + Q.P.y.LamM) zeroE) (Array.replicate (nclpOf Q.hp Q.g) zeroE) zeroE zeroE
    Array.size_replicate Array.size_replicate Array.size_replicate Array.size_replicate
  have htr := trips_there (S := S) (r := r) (by rw [eQ]; exact A.reads) (by rw [eQ]; exact hl)
    (by rw [eQ]; exact hTQ) (by rw [eQ]; exact hla) ht (by rw [eQ]; exact hz)
    (by rw [eQ]; exact hY) hR hPan hfin et hh
  obtain ⟨tr, htr'⟩ := Option.isSome_iff_exists.mp htr
  exact ⟨R, sh, tr, hR, hsh, hn, htr'⟩

/-- CONDITIONAL on every hypothesis named. **A row is made for each token.** -/
theorem tokenRows_there (A : K4Plan hS pc Q.P Q.g tl D) (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hPB : pansB Q.P (blankEnv Q.P Q.hp Q.g iU3 r.1) Q.hp.lamS (nclpOf Q.hp Q.g) = true)
    (h : Sides.of Q w p = some S) : ∃ rows, tokenRows S = some rows := by
  obtain ⟨_, _, _, hv, _, _, _⟩ := sides_fields h
  have hyQ : S.v.y = Q.P.y := by
    rw [Option.some.inj (hv.symm.trans (envOf_pub hU hl p))]
    rfl
  unfold tokenRows
  refine amapM_there _ fun t _ => ?_
  obtain ⟨R, sh, tr, hR, hsh, _, htr⟩ := tok_step A hU hl hPB h
    (z := bitsOf S.v.y.h.lt t) (by rw [bitsOf_size, hyQ]) (eqTab (bitsOf S.v.y.h.lt t))
    (fun lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + t) zeroE)
  exact Option.isSome_iff_exists.mpr ⟨(sh, tr), Option.bind_eq_some_iff.mpr ⟨R, hR,
    Option.bind_eq_some_iff.mpr ⟨sh, hsh, Option.bind_eq_some_iff.mpr ⟨tr, htr, rfl⟩⟩⟩⟩

/-- CONDITIONAL on every hypothesis named. **The job is made of what `Sides.of` has returned, and
has its call's shape.** -/
theorem terms_fit_on (A : K4Plan hS pc Q.P Q.g tl D) (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hPB : pansB Q.P (blankEnv Q.P Q.hp Q.g iU3 r.1) Q.hp.lamS (nclpOf Q.hp Q.g) = true)
    (h : Sides.of Q w p = some S) (hzt : (ztOf Q p).size = Q.P.y.h.lt) :
    ∃ j, jobTermsOn S = some j ∧
      k4JobFits (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) j = true := by
  obtain ⟨rows, hrows⟩ := tokenRows_there A hU hl hPB h
  obtain ⟨_, _, _, hv, _, _, ezt⟩ := sides_fields h
  obtain ⟨_, _, _, _, hT, _, _⟩ := sides_seven A h
  have hyQ : S.v.y = Q.P.y := by
    rw [Option.some.inj (hv.symm.trans (envOf_pub hU hl p))]
    rfl
  have hsz : rows.size = 2 ^ S.v.y.h.lt := by rw [tokenRows_size hrows, hT]
  have hpos : 0 < S.v.y.T := by
    rw [hT]
    exact Nat.two_pow_pos _
  obtain ⟨R0, sh0, tr0, hR0, _, htr0, hg0⟩ := tokenRows_trips hrows hpos
  have hfirst : firstC rows = tr0 := by
    unfold OnBytes.Road.K4.C.firstOf
    rw [Array.getD_eq_getD_getElem?, hg0]
    rfl
  -- the sizes at each token
  have hsizes : (rows.all fun x => x.1.size == nEndT S.v.y && x.2.size == (firstC rows).size) =
      true := by
    rw [Array.all_eq_true]
    intro t ht
    have ht' : t < S.v.y.T := by rw [← tokenRows_size hrows]; exact ht
    obtain ⟨R, sh, tr, hR, hsh, htr, hg⟩ := tokenRows_trips hrows ht'
    have ex : rows[t] = (sh, tr) := by
      have := Array.getElem?_eq_getElem ht
      rw [hg] at this
      exact (Option.some.inj this).symm
    rw [ex, hfirst]
    obtain ⟨R', sh', _, hR', hsh', hn', _⟩ := tok_step A hU hl hPB h
      (z := bitsOf S.v.y.h.lt t) (by rw [bitsOf_size, hyQ]) #[] (fun _ _ => zeroE)
    obtain rfl : R = R' := Option.some.inj (hR.symm.trans hR')
    obtain rfl : sh = sh' := Option.some.inj (hsh.symm.trans hsh')
    have K := sidesSkel_refl S
    have k1 := readsTok_has K (z := bitsOf S.v.y.h.lt t) (z₀ := bitsOf S.v.y.h.lt 0)
      (by rw [bitsOf_size, bitsOf_size])
    rw [hR, hR0] at k1
    have k2 := trips_rel K k1 (eqTab (bitsOf S.v.y.h.lt t)) (eqTab (bitsOf S.v.y.h.lt 0))
      (fun lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + t) zeroE)
      (fun lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + 0) zeroE) sh sh0
    rw [htr, htr0] at k2
    have k3 : tr.size = tr0.size := k2
    show (sh.size == nEndT S.v.y && tr.size == tr0.size) = true
    rw [hyQ, hn', k3]
    simp
  have hsame : (rows.all fun x => x.2.map (·.1) == (firstC rows).map (·.1)) = true :=
    sameWeights_true S hrows
  -- the cube
  have hfit : (termsCube S rows).fits = true := by
    refine fits_of _ ?_ ?_ ?_ ?_ ?_
    · show (orderDefault S.v.y.h.lt).length = S.v.y.h.lt
      simp [orderDefault]
    · intro v hv'
      show v ∈ orderDefault S.v.y.h.lt
      simpa [orderDefault] using hv'
    · intro t ht
      show t.size = 2 ^ S.v.y.h.lt
      have ht' : t ∈ (endMapsOf S.v.y rows ++ aMapsOf rows ++ bMapsOf rows).toList := ht
      simp only [endMapsOf, aMapsOf, bMapsOf, Array.toList_append, Array.toList_map,
        List.mem_append, List.mem_map] at ht'
      rcases ht' with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> rw [Array.size_map, hsz]
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have hk' : k < (firstC rows).size := List.mem_range.mp hk
      have hm : (termsCube S rows).maps.size =
          nEndT S.v.y + (firstC rows).size + (firstC rows).size := by
        show (endMapsOf S.v.y rows ++ aMapsOf rows ++ bMapsOf rows).size = _
        simp [endMapsOf, aMapsOf, bMapsOf]
        omega
      rw [hm]
      constructor
      · show nEndT S.v.y + k < _
        omega
      · show nEndT S.v.y + (firstC rows).size + k < _
        omega
    · intro rho hr
      have h' : Way.point S.zt = Way.point rho := hr
      rw [← Way.point.inj h', ezt, hzt, ← hyQ]
      rfl
  refine ⟨{ lead := [(termsCube S rows).total], cube := termsCube S rows, dY := 1
            ends := fun rs =>
              ((endMapsOf S.v.y rows).map fun t => mle t ((termsCube S rows).pointOf rs)).toList
            atEnds := fun rs e =>
              (S.summand e.toArray ((termsCube S rows).pointOf rs)).getD zeroE }, ?_, ?_⟩
  · unfold jobTermsOn
    rw [hrows]
    show (if (!((termsCube S rows).fits &&
        (rows.all fun x => x.2.map (·.1) == (firstC rows).map (·.1)) &&
        rows.all fun x => x.1.size == nEndT S.v.y && x.2.size == (firstC rows).size)) = true
      then none else some _) = some _
    rw [hfit, hsame, hsizes]
    rfl
  · unfold k4JobFits
    rw [hfit]
    simp [k4TokenShape, termsCube, endMapsOf, hyQ,
      VerifiableInference.Desc.Part.MaskedSum.Var.d]

/-- CONDITIONAL on every hypothesis named. **THE SECOND TOKEN SUMCHECK's JOB IS MADE AND HAS ITS
CALL's PUBLIC SHAPE.** -/
theorem terms_fit (A : K4Plan hS pc Q.P Q.g tl D) (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hPB : pansB Q.P (blankEnv Q.P Q.hp Q.g iU3 r.1) Q.hp.lamS (nclpOf Q.hp Q.g) = true)
    (h : Sides.of Q w p = some S) (hzt : (ztOf Q p).size = Q.P.y.h.lt) :
    ∃ j, jobTerms Q w p = some j ∧ k4JobFits ((k4Shapes Q).getD 2 ⟨0, [], none⟩) j = true := by
  obtain ⟨j, hj, hf⟩ := terms_fit_on A hU hl hPB h hzt
  refine ⟨j, ?_, hf⟩
  unfold jobTerms
  rw [h]
  exact hj

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tok_step
#print axioms ProofFile.Honest.K4.tokenRows_there
#print axioms ProofFile.Honest.K4.terms_fit_on
#print axioms ProofFile.Honest.K4.terms_fit
