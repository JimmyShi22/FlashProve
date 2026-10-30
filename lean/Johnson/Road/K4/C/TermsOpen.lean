-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TermsOpen.lean: CONDITIONAL.

Not shown here. That the maker returns anywhere: each law starts from its return. Nothing on what a
value is worth, but for valAffQ_tok and valAffQ_up, which carry TokReads.lean's hypotheses. No
example is known.
No property is claimed.

THE MAKER OF THE SECOND TOKEN SUMCHECK's JOB, OPENED. The text of tokenRows and jobTermsOn
(Johnson/Desc/K4/Honest/Terms.lean) as equations, for whoever reasons about the job: its rows token
by token with their products, its cube under names of its own, the three tests that the maker has
passed, and the job field by field. Beside them: valAff? in terms of affFits and valAff, at a token
point and at the corners.

  tokenRows_trips   the rows at token t: the reads, the shown values, the products.
  tokenRows_size    there is one row for each token.
  endMapsOf, firstOf, aMapsOf, bMapsOf, termsCube   the cube's parts, to the letter of the maker's
                    text.
  jobTermsOn_whole  the rows, the three tests, and the job field by field.
  valAffQ_some      valAff? returns x exactly if affFits is true and x is valAff's value.
  valAffQ_tok       where valAff? returns at a token point it returns at every corner, and the value
                    is the combination of the corners' under the point's equality weights.
  valAffQ_up        the way back: from a return at one corner, AND THE READS AT EVERY CORNER, to the
                    return at the point.
-/
import Johnson.Road.K4.C.TokReads
import Johnson.Road.K4.C.TermsEnds
import Johnson.Road.K4.C.RowMaps
import Johnson.Desc.K4.Honest.Terms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Env TableAsk TableAt layTables tableAsks nEndT)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Reads Sides Job Cube Tab Trip matsOf readsAt valAff
  valAff? affFits endsOn tokenRows jobTermsOn mle)

local notation "cornerAt" => OnBytes.Desc.First.K4.Honest.bitsOf

/-- **The maker's rows at token t**: the reads at the corner, the values that the sumcheck is to
show there, and the products of the second pass's panels there. -/
theorem tokenRows_trips {S : Sides} {rows : Array (Array E × Array Trip)}
    (h : tokenRows S = some rows) {t : ℕ} (ht : t < S.v.y.T) :
    ∃ R sh tr, S.readsTok (cornerAt S.v.y.h.lt t) = some R ∧ endsOn S R = some sh ∧
      S.trips R (eqTab (cornerAt S.v.y.h.lt t))
        (fun lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + t) zeroE) sh = some tr ∧
      rows[t]? = some (sh, tr) := by
  unfold tokenRows at h
  obtain ⟨y', hy, hb⟩ := amapM_get h (i := t) (x := t) (by simp [ht])
  obtain ⟨R, hR, h1⟩ := Option.bind_eq_some_iff.mp hy
  obtain ⟨sh, hs, h2⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨tr, htr, h3⟩ := Option.bind_eq_some_iff.mp h2
  obtain rfl := Option.some.inj h3
  exact ⟨R, sh, tr, hR, hs, htr, hb⟩

/-- There is one row for each token. -/
theorem tokenRows_size {S : Sides} {rows : Array (Array E × Array Trip)}
    (h : tokenRows S = some rows) : rows.size = S.v.y.T := by
  unfold tokenRows at h
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [List.size_toArray, (list_mapM_some _ _ _ hL).1, Array.length_toList, Array.size_range]

/-- The end values' tables. -/
def endMapsOf (y : Lay) (rows : Array (Array E × Array Trip)) : Array Tab :=
  (Array.range (nEndT y)).map fun i => rows.map fun x => x.1.getD i zeroE

/-- The first token's products. -/
def firstOf (rows : Array (Array E × Array Trip)) : Array Trip := (rows.getD 0 (#[], #[])).2

/-- The first factors' tables. -/
def aMapsOf (rows : Array (Array E × Array Trip)) : Array Tab :=
  (Array.range (firstOf rows).size).map fun k =>
    rows.map fun x => (x.2.getD k (zeroE, zeroE, zeroE)).2.1

/-- The second factors' tables. -/
def bMapsOf (rows : Array (Array E × Array Trip)) : Array Tab :=
  (Array.range (firstOf rows).size).map fun k =>
    rows.map fun x => (x.2.getD k (zeroE, zeroE, zeroE)).2.2

/-- The job's cube. -/
def termsCube (S : Sides) (rows : Array (Array E × Array Trip)) : Cube :=
  { n := S.v.y.h.lt, order := orderDefault S.v.y.h.lt, way := .point S.zt
    maps := endMapsOf S.v.y rows ++ aMapsOf rows ++ bMapsOf rows
    pairs := (List.range (firstOf rows).size).map fun k =>
      (((firstOf rows).getD k (zeroE, zeroE, zeroE)).1, nEndT S.v.y + k,
        nEndT S.v.y + (firstOf rows).size + k) }

/-- **The job, whole**: its rows, the three tests that the maker has passed, and the job field by
field. -/
theorem jobTermsOn_whole {S : Sides} {J : Job} (h : jobTermsOn S = some J) :
    ∃ rows, tokenRows S = some rows ∧ (termsCube S rows).fits = true ∧
      (rows.all fun x => x.2.map (·.1) == (firstOf rows).map (·.1)) = true ∧
      (rows.all fun x => x.1.size == nEndT S.v.y && x.2.size == (firstOf rows).size) = true ∧
      J = { lead := [(termsCube S rows).total], cube := termsCube S rows, dY := 1
            ends := fun rs =>
              ((endMapsOf S.v.y rows).map fun t => mle t ((termsCube S rows).pointOf rs)).toList
            atEnds := fun rs e =>
              (S.summand e.toArray ((termsCube S rows).pointOf rs)).getD zeroE } := by
  unfold jobTermsOn at h
  obtain ⟨rows, hr, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · cases h
  · rename_i hc
    obtain rfl := Option.some.inj h
    have hc' : ((termsCube S rows).fits &&
        (rows.all fun x => x.2.map (·.1) == (firstOf rows).map (·.1)) &&
        rows.all fun x => x.1.size == nEndT S.v.y && x.2.size == (firstOf rows).size) = true := by
      cases hX : ((termsCube S rows).fits &&
          (rows.all fun x => x.2.map (·.1) == (firstOf rows).map (·.1)) &&
          rows.all fun x => x.1.size == nEndT S.v.y && x.2.size == (firstOf rows).size) with
      | true => rfl
      | false =>
        exact absurd (show (!((termsCube S rows).fits &&
          (rows.all fun x => x.2.map (·.1) == (firstOf rows).map (·.1)) &&
          rows.all fun x => x.1.size == nEndT S.v.y && x.2.size == (firstOf rows).size)) = true by
            rw [hX]
            rfl) hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc'
    exact ⟨rows, hr, hc'.1.1, hc'.1.2, hc'.2, rfl⟩

/-- valAff? returns x exactly if affFits is true and x is valAff's value. -/
theorem valAffQ_some (v : Env) (R : Reads) (slot : ℕ → E) (a : Aff) (x : E) :
    valAff? v R slot a = some x ↔ affFits v R a = true ∧ x = valAff v R slot a := by
  unfold valAff?
  by_cases c : affFits v R a = true
  · rw [if_pos c]
    exact ⟨fun h => ⟨c, (Option.some.inj h).symm⟩, fun h => by rw [h.2]⟩
  · rw [if_neg c]
    exact ⟨fun h => (by cases h), fun h => absurd h.1 c⟩

/-- **valAff? at a token point and at the corners.** -/
theorem valAffQ_tok {Q : K4Pub} {w : K4In} {fo : Forest.Heard} {zlow z : Array E}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {Rz : Reads} {Rt : ℕ → Reads}
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) (hk : TokAsks Q)
    (hlow : zlow.size = Q.P.y.ls) (hz : z.size = Q.P.y.h.lt)
    (hRz : readsAt Q w fo (tokPts zlow z) = some Rz)
    (hRt : ∀ t, t < 2 ^ Q.P.y.h.lt →
      readsAt Q w fo (tokPts zlow (cornerAt Q.P.y.h.lt t)) = some (Rt t))
    {v : Env} {slot : ℕ → E} {a : Aff} {x : E} (h : valAff? v Rz slot a = some x) :
    (∀ t, t < 2 ^ Q.P.y.h.lt → valAff? v (Rt t) slot a = some (valAff v (Rt t) slot a)) ∧
      Reading.gl.val x = ∑ t ∈ range (2 ^ Q.P.y.h.lt),
        Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
          Reading.gl.val (valAff v (Rt t) slot a) := by
  obtain ⟨hfit, rfl⟩ := (valAffQ_some v Rz slot a x).mp h
  obtain ⟨h1, h2⟩ := valAff_tok (slot := slot) hl hk hlow hz hRz hRt hfit
  exact ⟨fun t ht => (valAffQ_some _ _ _ _ _).mpr ⟨h1 t ht, rfl⟩, h2⟩

/-- **From one corner to the point**: where valAff? returns at one corner, the reads are there at
every token point z of lt coordinates, valAff? returns on them, and its value is the combination of
the corners' under z's equality weights. CONDITIONAL on hl, hk, hlow, hz, hRt (THE READS AT EVERY
CORNER), ht0 and h: one corner's return gives the fit, not the reads. -/
theorem valAffQ_up {Q : K4Pub} {w : K4In} {fo : Forest.Heard} {zlow z : Array E}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {Rt : ℕ → Reads}
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) (hk : TokAsks Q)
    (hlow : zlow.size = Q.P.y.ls) (hz : z.size = Q.P.y.h.lt)
    (hRt : ∀ t, t < 2 ^ Q.P.y.h.lt →
      readsAt Q w fo (tokPts zlow (cornerAt Q.P.y.h.lt t)) = some (Rt t))
    {v : Env} {slot : ℕ → E} {a : Aff} {t0 : ℕ} (ht0 : t0 < 2 ^ Q.P.y.h.lt) {x0 : E}
    (h : valAff? v (Rt t0) slot a = some x0) :
    ∃ Rz, readsAt Q w fo (tokPts zlow z) = some Rz ∧
      valAff? v Rz slot a = some (valAff v Rz slot a) ∧
      Reading.gl.val (valAff v Rz slot a) = ∑ t ∈ range (2 ^ Q.P.y.h.lt),
        Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
          Reading.gl.val (valAff v (Rt t) slot a) := by
  obtain ⟨Rz, hRz⟩ := readsAt_some (hRt t0 ht0) (tokPts zlow z)
  have hf0 := ((valAffQ_some _ _ _ _ _).mp h).1
  have hfz : affFits v Rz a = true :=
    affFits_tok hl hk (by rw [cornerAt_size, hz]) (hRt t0 ht0) hRz hf0
  exact ⟨Rz, hRz, (valAffQ_some _ _ _ _ _).mpr ⟨hfz, rfl⟩,
    (valAff_tok (slot := slot) hl hk hlow hz hRz hRt hfz).2⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.tokenRows_trips
#print axioms OnBytes.Road.K4.C.tokenRows_size
#print axioms OnBytes.Road.K4.C.jobTermsOn_whole
#print axioms OnBytes.Road.K4.C.valAffQ_some
#print axioms OnBytes.Road.K4.C.valAffQ_tok
#print axioms OnBytes.Road.K4.C.valAffQ_up
