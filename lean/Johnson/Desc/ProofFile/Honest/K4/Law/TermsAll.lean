-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsAll.lean: CONDITIONAL.

What is here. THE SECOND TOKEN SUMCHECK's JOB MEETS THE THREE PREMISES THAT THE CUBE's TIE
(CubeSum.lean) ASKS OF A JOB, FROM PUBLIC PREMISES AND THE JOB's BEING MADE: the joining of
KindsOf.lean (the hypothesis `TripsAt` at a token point) with TermsJob.lean (the three from
`TripsAt`), the returns at the point being had from the tokens' rows (Law/SkelTerms.lean,
Law/AtEnds.lean). Statements and proofs.

  `TermsPub`   the public premises under one name
  `made_of_rows`   the reads and the products are made at every point of lt coordinates
  `terms_tripsAt`   `TripsAt` at the point that the challenges make
  `terms_three`   **the three**

Limits. At the reading `Reading.gl`. Premises: the job is made; the verifier's list of tables is
laid; every family of that list is of a sort that `TokAsk` names; the structure that the forms read
has the plan's layout; the lookup's low coordinates are ls in number; there are 2 ^ lt tokens, and
at most so many by the structure that the rotation factor reads; the table of gated products has a
whole number of rows of T entries; THE PUBLIC TEST `triPlainB` (TripsWhole.lean), which no text of
the verifier or of the honest parts asks; as many challenges as a token's number has bits. Where one
of them is false nothing is said. TermsMember.lean has a test with code for the public premises,
which passes at the small plan by evaluation. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.KindsOf
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsJob
import Johnson.Desc.ProofFile.Honest.K4.Law.AtEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading eqTab)
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks)
open OnBytes.Flat (OptRel)
open OnBytes.Road.K4.C (TokAsks jobTermsOn_whole tokenRows_trips)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes.Desc.First.K4.RtPub

/-- **The public premises on what the two jobs share.** This defines a hypothesis; the definition
claims nothing. -/
structure TermsPub (S : Sides) : Prop where
  laid : ∃ r, layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r
  asks : TokAsks S.Q
  y : S.v.y = S.Q.P.y
  low : S.zlow.size = S.v.y.ls
  T : S.v.y.T = 2 ^ S.v.y.h.lt
  Tc : S.ce.v.y.T ≤ 2 ^ S.v.y.h.lt
  rowsOfT : S.hh.size % S.v.y.T = 0
  tri : triPlainB S = true

/-- **Where the tokens' rows are made and there is a token, the reads and the products are made at
every point of lt coordinates, at all values in the place of the shown factors.** -/
theorem made_of_rows {S : Sides} {rows : TokRows} (h : tokenRows S = some rows)
    (hT : 0 < S.v.y.T) (z : Array E) (hz : z.size = S.v.y.h.lt) :
    ∃ Rz, S.readsTok z = some Rz ∧ ∀ e : Array E, ∃ l, S.trips Rz (eqTab z)
      (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE) e = some l := by
  obtain ⟨R, sh, tr, hR, _, h3, _⟩ := tokenRows_trips h hT
  have K := sidesSkel_refl S
  obtain ⟨Rz, e1, k1⟩ := OptRel.of_right
    (readsTok_has K (z := z) (z₀ := bitsOf S.v.y.h.lt 0) (hz.trans (bitsOf_size _ _).symm)) hR
  refine ⟨Rz, e1, fun e => ?_⟩
  obtain ⟨l, e2, _⟩ := OptRel.of_right
    (trips_rel K k1 (eqTab z) _
      (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE) _ e sh) h3
  exact ⟨l, e2⟩

/-- `TripsAt` at the point that the challenges make. -/
theorem terms_tripsAt {S : Sides} (P : TermsPub S) {rows : TokRows}
    (h : tokenRows S = some rows) (rs : List E) (hr : rs.length = S.v.y.h.lt) :
    ∃ idx, TripsAt S rows rs.toArray idx := by
  have hz : rs.toArray.size = S.v.y.h.lt := by simpa using hr
  have pos : 0 < S.v.y.T := by
    rw [P.T]
    exact Nat.two_pow_pos _
  obtain ⟨Rz, hRz, hm⟩ := made_of_rows h pos rs.toArray hz
  obtain ⟨r, hl⟩ := P.laid
  exact tripsAt_at S h hl P.asks P.y P.low P.T P.Tc P.rowsOfT P.tri rs.toArray hz Rz hRz hm

/-- **THE THREE**: along the masked line the job's summand is a polynomial of degree at most that
of the job; it reads its values through the reading; on the true end values it is the cube's
summand. -/
theorem terms_three {S : Sides} {J : Job} (P : TermsPub S) (hJ : jobTermsOn S = some J)
    (rs : List E) (hr : rs.length = S.v.y.h.lt) :
    (∀ m, PolyOn J.dY fun y => J.atEnds rs (maskedEnds (J.ends rs) m y)) ∧
      ReadsAlike (J.atEnds rs) ∧
      Reading.gl.val (J.atEnds rs (J.ends rs)) = Reading.gl.val (J.cube.summandAt rs) := by
  obtain ⟨rows, h1, _⟩ := jobTermsOn_whole hJ
  obtain ⟨idx, T⟩ := terms_tripsAt P h1 rs hr
  have T' : ∀ rows', tokenRows S = some rows' → TripsAt S rows' rs.toArray idx := by
    intro rows' h'
    obtain rfl : rows = rows' := Option.some.inj (h1.symm.trans h')
    exact T
  exact ⟨fun m => terms_poly hJ rs m hr T', terms_alike hJ rs hr T', terms_end hJ rs hr T'⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.made_of_rows
#print axioms ProofFile.Honest.K4.terms_tripsAt
#print axioms ProofFile.Honest.K4.terms_three
