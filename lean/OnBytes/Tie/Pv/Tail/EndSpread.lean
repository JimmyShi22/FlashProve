-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndSpread.lean: the claims that objectsF (OnBytes/Model/Tail.lean) adds for its
ties and reads are the batch, under the powers of the batching element, of a list of single
equations that is made from the smallness test's state before objectsF runs.

Statements and proofs.
Main names:
  `carry4`: a function of the state that reads none of the fields that four steps set has the same
    value before and after.
  `topOf`: the number of indices.
  `objectsF_spread`: if objectsF returns: the exponents of `rowsTail ρ tl funs pc` rise strictly and
    lie from pc on and below pc + `topOf`; and behind the lookup's claims the total grows by the
    batch of that list at the batching element.
Limits: the premises of `objectsF_ends` (OnBytes/Tie/Pv/Tail/EndAll.lean) stand: `RawRows` and
`Fits`. The list reads no field that objectsF sets. That the state
before objectsF holds nothing that was drawn after the batching element is not a statement here: it
is the order of the verifier's routines. The number pc is read off the state behind objectsF
(planClaimsF): that the lookup's claims leave it as it was before is not stated here.
-/
import OnBytes.Tie.Pv.Tail.EndRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

open Finset

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- A function of the smallness test's state that does not read the fields that four steps set. -/
theorem carry4 {α : Sort _} (f : HTailF2 → α) {t0 t1 t2 t3 t4 x1 x2 x3 x4 : HTailF2}
    (e1 : t1 = x1) (r1 : f x1 = f t0) (e2 : t2 = x2) (r2 : f x2 = f t1) (e3 : t3 = x3)
    (r3 : f x3 = f t2) (e4 : t4 = x4) (r4 : f x4 = f t3) : f t4 = f t0 :=
  ((congrArg f e4).trans r4).trans (((congrArg f e3).trans r3).trans
    (((congrArg f e2).trans r2).trans ((congrArg f e1).trans r1)))

/-- the number of indices -/
def topOf (tl : HTailF2) (funs : Array HFun) : Nat :=
  firstOf tl tl.NM + (readsList tl funs).length * tl.stepF

/-- The ties and reads that objectsF adds are the batch, under the powers of the batching element,
of a list of single equations that is made from the state before objectsF runs. -/
theorem objectsF_spread (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (hfit : Fits tl)
    (A : Nat → Nat → Nat → K) (hV : RawRows W tl G funs (ρ.val G.theta) A) :
    Rising (rowsTail ρ tl funs G.planClaimsF) ∧
    (∀ r ∈ rowsTail ρ tl funs G.planClaimsF,
      G.planClaimsF ≤ r.1 ∧ r.1 < G.planClaimsF + topOf tl funs) ∧
    ∃ g Fa ca tla Fb cb tlb Fc cc,
      tl.heard = some g ∧ Forest.objects g F c = .ok (((), Fa), ca) ∧
      tl.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      (Fc.LS.size = Fc.ns → c' = cc ∧ Kept Fc G ∧
        G.nClaim = Fc.nClaim + tl.NM + (readsList tl funs).length ∧
        G.total ρ W = Fc.total ρ W +
          batchOf (ρ.val G.theta) A (rowsTail ρ tl funs G.planClaimsF)) := by
  obtain ⟨_, Fa0, ca0, tla0, Fb0, cb0, tlb0, Fc0, cc0, tl1, F10, c10, _, _, hJ0, hB0, hWt0, hlaid,
    etl, _, _, _⟩ := objectsF_total ρ W tl tl' funs F G c c' h
  have ea := linJoin9_spec tl tla0 Fa0 Fb0 ca0 cb0 hJ0
  have eb := linBits9_spec tla0 tlb0 Fb0 Fc0 cb0 cc0 hB0
  obtain ⟨_, _, hP1, e1⟩ := weightsF_spec tlb0 tl1 Fc0 F10 cc0 c10 hWt0
  have sRows : ∀ pc, rowsTail ρ tl' funs pc = rowsTail ρ tl funs pc := fun pc =>
    carry4 (fun t => rowsTail ρ t funs pc) ea rfl eb rfl e1 rfl etl rfl
  have sNM : tl'.NM = tl.NM := carry4 (fun t => t.NM) ea rfl eb rfl e1 rfl etl rfl
  have sShp : tl'.shp = tl.shp := carry4 (fun t => t.shp) ea rfl eb rfl e1 rfl etl rfl
  have sMats : tl'.mats = tl.mats := carry4 (fun t => t.mats) ea rfl eb rfl e1 rfl etl rfl
  have sReads : readsList tl' funs = readsList tl funs :=
    carry4 (fun t => readsList t funs) ea rfl eb rfl e1 rfl etl rfl
  have sReads1 : readsList tl' funs = readsList tl1 funs :=
    (congrArg (fun t => readsList t funs) etl).trans rfl
  have hV' : RawRows W tl' G funs (ρ.val G.theta) A :=
    ⟨(carry4 (fun t => ∀ c, W.entry t.ix.ZZ t.zzRowTies c =
          ∑ u ∈ range t.tau, ρ.val G.theta ^ u * A t.ix.ZZ u c)
        ea rfl eb rfl e1 rfl etl rfl).mpr hV.ties,
      (carry4 (fun t => ∀ c, W.entry t.ix.ZZ t.zzRowReads c =
          ∑ u ∈ range t.tau, ρ.val G.theta ^ u * A t.ix.ZZ u c)
        ea rfl eb rfl e1 rfl etl rfl).mpr hV.reads,
      (carry4 (fun t => ∀ mu, mu < t.NM → ∀ p, W.entry (t.gtTree.getD mu 0) 0 p =
          ∑ i' ∈ range (t.shp.getD mu {}).mS,
            ρ.val G.theta ^ (t.stepF * i') * A (t.gtTree.getD mu 0) i' p)
        ea rfl eb rfl e1 rfl etl rfl).mpr hV.syms,
      (carry4 (fun t => ∀ x ∈ readsList t funs, ∀ d, d < (t.mats.getD x.1.mat {}).k →
          W.entry (uOf t x.1) (posOf t x.1 x.2 d / colsU G (uOf t x.1))
            (posOf t x.1 x.2 d % colsU G (uOf t x.1)) = A (uOf t x.1) 0 (posOf t x.1 x.2 d))
        ea rfl eb rfl e1 rfl etl rfl).mpr hV.tabs⟩
  have hfit' : Fits tl' := hfit.of_same sNM sShp sMats
  have hsh' : ∀ mu, mu < tl'.NM →
      (tl'.shp.getD mu {}).mS = ((tl'.mats.getD mu {}).m + 2) / 3 := by
    rw [etl]
    exact fun mu hmu => (hP1.shape mu hmu).2.2.2.2
  have hmS : ∀ mu, mu < tl.NM →
      (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m := by
    intro mu hmu
    have e := hsh' mu (by rw [sNM]; exact hmu)
    rw [sShp, sMats] at e
    rw [e, (hfit mu hmu).1]
    rfl
  obtain ⟨g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, _, F1, c1, hg, hFo, hJ, hB, _, eF, ec, himp⟩ :=
    objectsF_ends ρ W tl tl' funs F G c c' h hfit' A hV'
  subst eF
  subst ec
  refine ⟨rising_rowsTail ρ tl funs _ hmS, bounds_rowsTail ρ tl funs _ hmS,
    g, Fa, ca, tla, Fb, cb, tlb, F1, c1, hg, hFo, hJ, hB, fun hs => ?_⟩
  obtain ⟨e1', hk, hn, htot⟩ := himp hs
  refine ⟨e1', hk, ?_, ?_⟩
  · rw [hn, sNM, hlaid, ← sReads1, sReads]
  · rw [htot, add_assoc, ← batch_rowsTail, sRows]

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.objectsF_spread
