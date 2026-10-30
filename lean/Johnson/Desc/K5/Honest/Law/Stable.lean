-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Stable.lean: the honest prover's side of an attention segment's own
rounds: a value or a summand that is made when some challenges are still to come is the same when
it is made later, of more challenges. Statements with their proofs. No frame of a prover is
imported.

Why. The lone values and the summands (Johnson/Desc/K5/Honest/Alone.lean, Products.lean,
Index.lean) are functions of the challenges so far, in which a challenge that has not been heard
reads as 0. A value that is sent at one part of the row and is the start of a later part's sumcheck
is so typed at two lists of challenges; and the verifier's claims read all values at the points made
of all challenges. So each function has to read no challenge behind the part at which it is first
called. That is what is shown here, function by function, as an equation of the two results.

c, c': two lists of challenges with the same key points (hz), which are one in the rounds of the
parts in front of part number q (h: Agree, Johnson/Desc/K5/Honest/Law/HeardIs.lean).

  maxOf_agree, divIn_agree, divIn_none   the points that the summands share, early and late
  stable_sVM, stable_sVD   the value product's two summands: from behind the batching element in
                 front of them on: so the second is the same in front of the first's rounds and
                 behind them
  stable_m6      the maxima: from behind the point on
  stable_sSF     the score at the index: from behind the batching element in front of it on
  stable_sSD     the key at the index: the like
  stable_sHB     "the index's cells are bits": the like
  stable_sSE     denominator times output: at all challenges
  agree_take     the first n and the first n' of one list of challenges are one in the first n
                 rounds, where n is at most n'

Limits. Every statement is conditional on hz and h, but `divIn_none` (hz, not h), `stable_sSF` and
`stable_sHB` (h, not hz) and `agree_take` (neither: n is at most n'). The equations are of the
program's elements, word for word. Nothing holds a value against the verifier's claims. No property
is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PointsIs
import Johnson.Desc.K5.Honest.Products
import Johnson.Desc.K5.Honest.Index

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc.First.Att.P (Pts DivP MaxP wDivision wBelow wOn wAtIndex wCells pointM
  pointD)

/-! ## 1 The points that the summands share -/

section
variable (P : Pub5) {c c' : Chal} {q : Nat} (hz : c.zk = c'.zk)
  (h : Agree (firstOf P.x q) c c')
include hz h

/-- The named points on the maximum and its index, early and late. -/
theorem maxOf_agree :
    (iZero P.x < q → (maxOf P c).tg = (maxOf P c').tg ∧ (maxOf P c).ti = (maxOf P c').ti) ∧
      (iSF P.x < q → (maxOf P c).scF.r = (maxOf P c').scF.r) := by
  unfold maxOf
  cases hp : ptsOf P c with
  | none =>
    rw [ptsOf_none P hz hp]
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
  | some p =>
    obtain ⟨p', hp', K⟩ := ptsOf_agree P hz h hp
    rw [hp']
    exact ⟨fun hq => ⟨K.tg hq, K.ti hq⟩, fun hq => K.scF hq⟩

/-- What the division's and the value product's summands share, early and late. -/
theorem divIn_agree {D : DivIn} (hD : divIn P c = some D) :
    ∃ D', divIn P c' = some D' ∧ D.pw = D'.pw ∧ D.zW = D'.zW ∧ D.ec = D'.ec ∧
      divKey D.d = divKey D'.d ∧ (iGam P.x < q → D.d.gam = D'.d.gam) := by
  unfold divIn at hD ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hD ⊢
  obtain ⟨p, hp, wl, hw, rfl⟩ := hD
  obtain ⟨p', hp', K⟩ := ptsOf_agree P hz h hp
  have hk := K.key.d
  have hzc : p.d.zcW = p'.d.zcW := by
    simp only [divKey, Prod.mk.injEq] at hk
    exact hk.2.2.2.2.2.2.2.1
  refine ⟨_, ⟨p', hp', wl, hw, rfl⟩, ?_, ?_, ?_, hk, K.gam⟩
  · show _ = VerifiableInference.Desc.First.Att.P.weights wl (c'.zk.getD wl.call #[])
    rw [← hz]
  · show _ = VerifiableInference.Desc.First.Att.P.inner wl (c'.zk.getD wl.call #[])
    rw [← hz]
  · show VerifiableInference.Desc.First.Att.P.eqTab p.d.zcW = _
    rw [hzc]

end

theorem divIn_none (P : Pub5) {c c' : Chal} (hz : c.zk = c'.zk) (hD : divIn P c = none) :
    divIn P c' = none := by
  cases h' : divIn P c' with
  | none => rfl
  | some D' =>
    obtain ⟨D, e, _⟩ :=
      divIn_agree P (q := 0) hz.symm (fun i hi => absurd hi (Nat.not_lt_zero i)) h'
    rw [hD] at e
    cases e

/-! ## 2 The summands and the maxima -/

section
variable (P : Pub5) (w : K5In) {c c' : Chal} {q : Nat} (hz : c.zk = c'.zk)
  (h : Agree (firstOf P.x q) c c')
include hz h

/-- **Denominator times output** reads no challenge of the place's own rounds. -/
theorem stable_sSE : sSE P w c = sSE P w c' := by
  unfold sSE
  cases hD : divIn P c with
  | none => rw [divIn_none P hz hD]
  | some D =>
    obtain ⟨D', hD', e1, e2, e3, e4, _⟩ := divIn_agree P hz h hD
    simp only [divKey, Prod.mk.injEq] at e4
    rw [hD']
    simp only [wDivision]
    rw [e1, e2, e3, e4.1]

/-- **The value product below the diagonal.** CONDITIONAL: the batching element in front of it has
been heard in both. -/
theorem stable_sVM (hq : iGam P.x < q) : sVM P w c = sVM P w c' := by
  unfold sVM
  cases hD : divIn P c with
  | none => rw [divIn_none P hz hD]
  | some D =>
    obtain ⟨D', hD', e1, e2, e3, e4, e5⟩ := divIn_agree P hz h hD
    simp only [divKey, Prod.mk.injEq] at e4
    rw [hD']
    simp only [wBelow, belowAt, pointM, DivP.zilo]
    rw [e1, e2, e3, e4.1, e4.2.2.2.2.2.2.1, e5 hq]

/-- **The value product on the diagonal.** CONDITIONAL: the batching element in front of the value
product's two sumchecks has been heard in both. The challenges of the sumcheck below the diagonal,
which stands between, are not read. -/
theorem stable_sVD (hq : iGam P.x < q) : sVD P w c = sVD P w c' := by
  unfold sVD
  cases hD : divIn P c with
  | none => rw [divIn_none P hz hD]
  | some D =>
    obtain ⟨D', hD', e1, e2, e3, e4, e5⟩ := divIn_agree P hz h hD
    simp only [divKey, Prod.mk.injEq] at e4
    rw [hD']
    simp only [wOn, pointD, DivP.zilo]
    rw [e1, e2, e3, e4.1, e4.2.2.2.2.2.2.1, e5 hq]

/-- **The maxima.** CONDITIONAL: the point has been heard in both. -/
theorem stable_m6 (hq : iZero P.x < q) : m6 P w c = m6 P w c' := by
  obtain ⟨e1, e2⟩ := (maxOf_agree P hz h).1 hq
  unfold m6
  simp only
  rw [e1, e2]

omit hz in
/-- **The score at the index.** CONDITIONAL: the batching element in front of it has been heard in
both, and so the point. The result does not depend on the key points: hz is not asked. -/
theorem stable_sSF (hq : iM6 P.x < q) : sSF P w c = sSF P w c' := by
  have S := heardAt_agree P h
  have e1 := S.om hq
  have e2 := S.point (Nat.lt_trans (Nat.lt_succ_self _) hq)
  unfold sSF
  simp only [atF, MaxP.ri, MaxP.rg, MaxP.rc, wAtIndex]
  rw [e1, e2]

/-- **The key at the index.** CONDITIONAL: the batching element in front of it has been heard in
both, and so the challenges of the score at the index. -/
theorem stable_sSD (hq : iOm4 P.x < q) : sSD P w c = sSD P w c' := by
  have S := heardAt_agree P h
  have e1 := S.om' hq
  have e2 := (maxOf_agree P hz h).2 (Nat.lt_trans (Nat.lt_succ_self _) hq)
  unfold sSD
  simp only [atD, MaxP.ri, MaxP.rg, MaxP.rc, MaxP.pj, MaxP.pg, MaxP.pi]
  rw [e1, e2]

omit hz in
/-- **The index's cells are bits.** CONDITIONAL: the batching element in front of it has been heard
in both, and so the point. The result does not depend on the key points: hz is not asked. -/
theorem stable_sHB (hq : iOm5 P.x < q) : sHB P w c = sHB P w c' := by
  have S := heardAt_agree P h
  have e1 := S.om'' hq
  have e2 := S.point (show iZero P.x < q by unfold iZero; unfold iOm5 at hq; omega)
  unfold sHB
  simp only [atH, MaxP.ri2, MaxP.rg2, MaxP.rk, wCells]
  rw [e1, e2]

end

/-! ## 3 Two stretches of one list -/

/-- The first n and the first n' of one list of challenges. CONDITIONAL: n is at most n'. -/
theorem agree_take (zk zk' : Array (Array E)) (ds : List Fmt.Drawn) {n n' : Nat} (hn : n ≤ n') :
    Agree n ⟨zk, ds.take n⟩ ⟨zk', ds.take n'⟩ := fun i hi => by
  show (ds.take n)[i]? = (ds.take n')[i]?
  rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt (Nat.lt_of_lt_of_le hi hn)]

end H2K5.Honest

#print axioms H2K5.Honest.maxOf_agree
#print axioms H2K5.Honest.divIn_agree
#print axioms H2K5.Honest.divIn_none
#print axioms H2K5.Honest.stable_sSE
#print axioms H2K5.Honest.stable_sVM
#print axioms H2K5.Honest.stable_sVD
#print axioms H2K5.Honest.stable_m6
#print axioms H2K5.Honest.stable_sSF
#print axioms H2K5.Honest.stable_sSD
#print axioms H2K5.Honest.stable_sHB
#print axioms H2K5.Honest.agree_take
