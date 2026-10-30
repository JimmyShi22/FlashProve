--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/RowsHold.lean: the open constraints that the linear claim's shared rounds
lay at the kind's own three places hold of an honest prover's words.

The shared rounds test no equation: they lay linear constraints on two groups of messages, which two
proximity tests test later. Here: at each of "(rec_gamma)", "LOC" and "SPLIT", if that place
accepts, if all open constraints on a group held in front of it, and if the words hold the honest
values, then all open constraints on the group hold behind it. The tests also take in the sample
rows of o_u, o_omega and o_sp, which are laid in the same rounds by the two sendings: these are not
here. What a constraint says of words is an equation, by the laws recMeansW, locMeansW and
foldMeansW (Johnson/Desc/K14/Law/MeansRec.lean, MeansLoc.lean, Means.lean), each of which is an "if
and only if". The equations at the honest values: Johnson/Desc/K14/Honest/Values.lean, and
locAt_of_rows (Johnson/Desc/K14/Law/NearRows.lean).

  wOf, wOf_eq     the rows' weights as the program's table has them, read into the field; they are
                  the equality vector's entries at gamma where gamma has v coordinates. IsFold is
                  stated at wOf; a caller whose folded row is made with the equality vector's
                  entries goes over by wOf_eq
  rec_say, rec_hold   at "(rec_gamma)": row by row; and the group's whole list
  loc_say, loc_hold   at "LOC": likewise
  split_hold      at "SPLIT", where the shape splits

What is assumed, as premises. The place's function returns a state (in rec_say and loc_say: the rows
are the ones that it makes, and its tests are passed). The committed table's shape is in order (hi).
The messages have their tables (PlacedU, Placed). The table of weights has as many entries as the
committed table has rows (hsz). The words at o_u hold the fold of the committed table's rows
(IsFold), and those at o_omega what that fold gives at psi_lo (hO). Each row's OOD answers in the
key are that row's own (RowAnswer). Each opened column holds each row's own symbol (genK). That
premise puts these symbols into the base field's image, as a committed table's are; of the table
tabOfRows, at the library's field and for rows lifted from the base field, it is a theorem
(Johnson/Desc/K14/Law/TabOfRows.lean). At "SPLIT": the shape splits (hS: with one code (fold) goes
whole to the one group: not treated), and the element that is sent reads as the honest scalar's
value (hmu: see Johnson/Desc/K14/Honest/SplitSays.lean: of the two new constraints the one on
G_omega is that premise in other words). T, the statement at which the tables' sizes are read, is a
free variable: whoever calls these theorems at a state owes what Johnson/Desc/Means/Says.lean asks
of a law over Says: that the row has passed the tests at the statement in force.
What is not claimed. That a place's function returns a state. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.Values
import Johnson.Desc.K14.Honest.SplitSays
import Johnson.Desc.K14.Law.Joint
import Johnson.Desc.K14.Law.MeansDot
import Johnson.Desc.K14.Law.Weights
import Johnson.Desc.K14.Law.NearRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (ok takeMaskP)
open Desc.K14.Law

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- The weights of the committed table's rows, as the program's table has them, read into the field;
0 beyond the table's end. -/
def wOf (S : LinShape) (l : Lin) (r : Nat) : K := ρ.val ((weights S l).getD r zeroE)

/-- They are the equality vector's entries at gamma. -/
theorem wOf_eq (S : LinShape) (l : Lin) (hg : (gamma S l).length = S.fold.index.v) :
    ∀ r < S.fold.index.rows, wOf ρ S l r = eqK ((gamma S l).map ρ.val) r := by
  intro r hr
  have hr' : r < 2 ^ (gamma S l).length := by
    rw [hg]
    exact hr
  exact weights_val ρ S l r hr'

/-- (rec_gamma)'s constraints, as they are made at the carried state l, hold of the honest words. -/
theorem rec_say (p : Par) (l : Lin) (T : Statement) (m : Words K) (Rw : Nat → Nat → K)
    (rows : List Row) (hrows : recRows p l = some rows) (hok : ok (laysRecL p l) = true)
    (hi : p.S.fold.index.ok = true) (hP : PlacedU T p.S.fold l.oU)
    (hu : IsFold p.S.fold (wOf ρ p.S l) Rw (uOf l m))
    (hR : ∀ x ∈ l.key.seeds.zipIdx, ∀ r < p.S.fold.index.rows,
      RowAnswer p.S.fold.index (x.1.z.map ρ.val) (ρ.val x.1.beta) (fun t => ρ.val (thetaE t)) x.2
        (Rw r) (ρ.val (l.key.record.getD (r * p.S.fold.index.answers + x.2) zeroE))) :
    ∀ row ∈ rows, Means.Says ρ T row m := by
  intro row hrow
  obtain ⟨x, hx, hg⟩ := mem_mapM_back _ _ _ hrows row hrow
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
  have hfit : l.key.fits p.S.fold.index = true := hok.1
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  have hx' : l.key.seeds[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  have hlt : x.2 < p.S.fold.index.answers := by
    rw [← hfit.1.2]
    exact (List.getElem?_eq_some_iff.1 hx').1
  have hz : x.1.z.length = p.S.fold.index.cubeBits := hfit.2 _ (List.mem_of_getElem? hx')
  have hi' := hi
  simp only [IndexShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hi'
  have hp0 : p.S.fold.index.pads < p.S.fold.index.code.ell := by tauto
  exact (recMeansW ρ T p.S.fold x.1 x.2 _ _ _ row hi hlt hz hg hP m).2
    (recEq_of_isFold p.S.fold (x.1.z.map ρ.val) (ρ.val x.1.beta) (fun t => ρ.val (thetaE t)) x.2
      (wOf ρ p.S l) (fun k => ρ.val (l.key.record.getD k zeroE)) (uOf l m) Rw
      hu (Nat.le_of_lt hp0) hlt (hR x hx))

/-- **"(rec_gamma)"**: the constraints on G_u hold behind it, if they held in front of it. -/
theorem rec_hold (p : Par) (d d' : St) (rs : List Fmt.RoundView) (T : Statement) (m : Words K)
    (Rw : Nat → Nat → K) (h : laysRec p d rs = some d')
    (hi : p.S.fold.index.ok = true) (hP : PlacedU T p.S.fold d.loc.oU)
    (hu : IsFold p.S.fold (wOf ρ p.S d.loc) Rw (uOf d.loc m))
    (hR : ∀ x ∈ d.loc.key.seeds.zipIdx, ∀ r < p.S.fold.index.rows,
      RowAnswer p.S.fold.index (x.1.z.map ρ.val) (ρ.val x.1.beta) (fun t => ρ.val (thetaE t)) x.2
        (Rw r) (ρ.val (d.loc.key.record.getD (r * p.S.fold.index.answers + x.2) zeroE)))
    (hold : Means.AllSay ρ T (rowsOn d d.loc.gU) m) :
    Means.AllSay ρ T (rowsOn d' d.loc.gU) m := by
  obtain ⟨hok, _, rows, hrows, hU, _⟩ := laysRecW p d d' rs h
  intro row hrow
  rw [hU, List.mem_append] at hrow
  rcases hrow with hrow | hrow
  · exact hold row hrow
  · exact rec_say ρ p d.loc T m Rw rows hrows hok hi hP hu hR row hrow

/-- (loc_x)'s constraints, as they are made at the state d, hold of the honest words: by
locAt_of_rows (Johnson/Desc/K14/Law/NearRows.lean). -/
theorem loc_say (p : Par) (d : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (T : Statement) (m : Words K) (Rw : Nat → Nat → K) (rows : List Row)
    (hrows : locRows p d.loc r cols = some rows) (hi : p.S.fold.index.ok = true)
    (hP : PlacedU T p.S.fold d.loc.oU)
    (hu : IsFold p.S.fold (wOf ρ p.S d.loc) Rw (uOf d.loc m))
    (hsz : (weights p.S d.loc).size = p.S.fold.index.rows)
    (hC : ∀ x ∈ locations p r, ∀ col, cols.lookup x = some col → ∀ q < p.S.fold.index.rows,
      ρ.val (ofF (col.toArray.getD q 0)) = genK ρ p.S.fold x (Rw q)) :
    ∀ row ∈ rows, Means.Says ρ T row m := by
  intro row hrow
  obtain ⟨x, hx, hg⟩ := mem_mapM_back _ _ _ hrows row hrow
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hg
  obtain ⟨col, hcol, hg⟩ := hg
  have hat : LocAt ρ p d m (fun _ => col) x := by
    refine locAt_of_rows ρ p d m (fun _ => col) x Rw ?_ ?_ ?_
    · intro q hq
      rw [hsz] at hq
      exact hC x hx col hcol q hq
    · intro j hj
      rw [hsz]
      exact hu.onMsg j hj
    · intro j hj
      rw [hsz]
      exact hu.onTail j hj
  exact (locMeansW ρ T p.S.fold x _ _ _ row hi hg hP m).2 hat

/-- **"LOC"**: the constraints on G_u hold behind it, if they held in front of it. -/
theorem loc_hold (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (T : Statement) (m : Words K) (Rw : Nat → Nat → K)
    (h : loc p d [r] [cols] = some d') (hi : p.S.fold.index.ok = true)
    (hP : PlacedU T p.S.fold d.loc.oU)
    (hu : IsFold p.S.fold (wOf ρ p.S d.loc) Rw (uOf d.loc m))
    (hsz : (weights p.S d.loc).size = p.S.fold.index.rows)
    (hC : ∀ x ∈ locations p r, ∀ col, cols.lookup x = some col → ∀ q < p.S.fold.index.rows,
      ρ.val (ofF (col.toArray.getD q 0)) = genK ρ p.S.fold x (Rw q))
    (hold : Means.AllSay ρ T (rowsOn d d.loc.gU) m) :
    Means.AllSay ρ T (rowsOn d' d.loc.gU) m := by
  obtain ⟨_, rows, hrows, _, hU, _⟩ := laysLocW p d d' r cols h
  intro row hrow
  rw [hU, List.mem_append] at hrow
  rcases hrow with hrow | hrow
  · exact hold row hrow
  · exact loc_say ρ p d r cols T m Rw rows hrows hi hP hu hsz hC row hrow

/-- **"SPLIT"**, where the shape splits (hS): if all open constraints on the two groups held in
front of it, and the element that is sent reads as the honest scalar's value (hmu), all open
constraints on the two groups hold behind it. -/
theorem split_hold (p : Par) (d d' : St) (r : Fmt.RoundView) (T : Statement) (m : Words K)
    (hS : p.S.sharedSplitNeeded = true) (h : split p d [r] = some d')
    (hP : Placed T p.S d.loc (linLayOmega d.st.codes p.S))
    (hO : ∀ j < p.S.matrixRows, omegaOf d.loc (linLayOmega d.st.codes p.S) m j =
      ∑ t ∈ Finset.range (2 ^ p.S.kLo),
        eqK ((d.loc.psiSh.take p.S.kLo).map ρ.val) t * uOf d.loc m (t + 2 ^ p.S.kLo * j))
    (hmu : ∀ row x G kappa d₁, fold p.S d.loc (linLayOmega d.st.codes p.S) = some row →
      r.vals = [.e x] → d.st.groups[d.loc.gOmega]? = some G →
      takeMaskP d d.loc.oSp = some (kappa, d₁) →
      ρ.val (E.ofTriple x) = muVal ρ T row G.members d.loc.oSp kappa m)
    (holdO : Means.AllSay ρ T (rowsOn d d.loc.gOmega) m)
    (holdU : Means.AllSay ρ T (rowsOn d d.loc.gU) m) :
    Means.AllSay ρ T (rowsOn d' d.loc.gOmega) m ∧ Means.AllSay ρ T (rowsOn d' d.loc.gU) m := by
  obtain ⟨row, x, G, kappa, d₁, d₂, hf, hx, hG, hok, hk, h2, h3⟩ := split_inv p d d' r hS h
  have hne : d.loc.gOmega ≠ d.loc.gU := by
    simp only [ok, splitL, List.all_cons, Bool.and_eq_true, bne_iff_ne] at hok
    exact hok.1
  have rO : rowsOn d' d.loc.gOmega = rowsOn d d.loc.gOmega ++
      [onOmega row G.members d.loc.oSp kappa (E.ofTriple x)] := by
    rw [rowsOn_addRowP_other d₂ d' _ _ _ h3 hne.symm, rowsOn_addRowP_same d₁ d₂ _ _ h2,
      rowsOn_takeMaskP d d₁ _ _ _ hk]
  have rU : rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++
      [onU row G.members d.loc.oSp kappa (E.ofTriple x)] := by
    rw [rowsOn_addRowP_same d₂ d' _ _ h3, rowsOn_addRowP_other d₁ d₂ _ _ _ h2 hne,
      rowsOn_takeMaskP d d₁ _ _ _ hk]
  have hrow : Means.Says ρ T row m :=
    (foldMeansW ρ T p.S d.loc _ row hf hP m).2 (foldEq_of_col p.S _ _ _ _ hO)
  obtain ⟨sa, sb⟩ := says_split ρ T row G.members d.loc.oSp kappa (E.ofTriple x) m
    (hmu row x G kappa d₁ hf hx hG hk) hrow
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rw [rO, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact holdO a ha
    · exact sa
  · rw [rU, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact holdU b hb
    · exact sb

end Desc.K14.Honest

#print axioms Desc.K14.Honest.wOf_eq
#print axioms Desc.K14.Honest.rec_say
#print axioms Desc.K14.Honest.rec_hold
#print axioms Desc.K14.Honest.loc_say
#print axioms Desc.K14.Honest.loc_hold
#print axioms Desc.K14.Honest.split_hold
