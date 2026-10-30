-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearCanon.lean: the typed data that the chain of a layers' sub-proof's own
rounds itself names on what the routines heard; and to what the letters' claims and the fit of the
weights come down there.

The chain's run has at each sumcheck the output at the letters' claim; the records' readings are
shown of the output at the reading of the record's target and at an added state (`OutIs`,
OnBytes/Tie/Pv/Lay/HearTieL.lean). The two are one where the letters' claims hold of the data
(`TailH.Claims`, OnBytes/Tie/Pv/Lay/OwnTieL.lean). Here the added states are chosen as the claims
name them, stage by stage, and the end values as those heard, read. What is left of the claims are
seven equations of targets; two of them hold at the records.

Main names:
  `valsOf ρ sh l`, `map_valsOf`: the end values heard, read, each under its name's place in a list
    sh of names without repetition and of the same length.
  `StIs`, `TgIs`, `claims_of`: the letters' claims in two halves: the states, the targets.
  `Shs T`: a list of names for each sumcheck. `c1` to `c7`, `w1` to `w6`, `canon`, `tailC`: the
    data of the stages, one after the other, from a first statement x.
  `tailC_st`, `tailC_of`, `tailC_claims`: their states are the claims'; they meet `TailOf`; so the
    claims hold as soon as the seven targets agree.
  `TokSaid.target`, `TokTg`, `own_recs2`: the target in a token sumcheck's record reads as the
    scalar that rode in its first message.
  `Tg5`, `layV_claims`, `layVF_claims`: at the records of Cb/Pv/Lay/OwnAll.lean the claims hold as
    soon as the five other targets agree.
  `stgFits_eq`, `stgFits_plain`: `StgFits` (OnBytes/Tie/Pv/Lay/HearTieAll.lean) from the form of
    the variables: all in the equality form at the readings of z, under the pick of the constant
    coefficient; or all plain, under the pick of the linear one.

Limits: `Tg5` is a premise: that the targets which the records name at the sums of squares, the
batched sumcheck, the two later product layers and the merge are the readings of the public parts
of the routines' start forms is shown of no value here. In `stgFits_eq` the weights are written as
a list over the variables; that the routines' lists of weights are such lists is shown in
OnBytes/Tie/Pv/Lay/SumTop.lean and LevelTie.lean. The lists of names are letters.
-/
import OnBytes.Tie.Pv.Lay.HearTieAll
import OnBytes.Tie.Pv.Lay.SumTop
import Cb.Pv.Lay.OwnAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-! ### End values by a list of their names -/

open Classical in
/-- The end values heard, read, each under its name's place in the list sh. -/
noncomputable def valsOf {A : Type} (sh : List A) (l : List E) : A → K :=
  fun a => ρ.val (l.getD (sh.idxOf a) zeroE)

omit [Fintype K] in
theorem map_valsOf {A : Type} (sh : List A) (hn : sh.Nodup) (l : List E)
    (h : sh.length = l.length) : sh.map (valsOf ρ sh l) = l.map ρ.val := by
  classical
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  have hi : i < sh.length := by simpa using h1
  have hl : i < l.length := by rw [← h]; exact hi
  rw [List.getElem_map, List.getElem_map]
  unfold valsOf
  rw [List.Nodup.idxOf_getElem hn i hi, List.getD_eq_getElem l zeroE hl]

/-! ### The letters' claims, in two halves -/

/-- The states in the typed data are those that the letters' claims name. -/
structure StIs {M X : Type} {T : LayTail K M X} (Dt : TailH ρ T) (x : X) : Prop where
  s1 : (T.s1.cl (Dt.y1 x) Dt.d1.rd).2 = Dt.d1.st
  s2 : (T.s2.cl (Dt.y2 x) Dt.d2.rd).2 = Dt.d2.st
  s3 : (T.s3.cl (Dt.z2 x) Dt.d3.rd).2 = Dt.d3.st
  s4 : (T.s4.cl (Dt.y4 x) Dt.d4.rd).2 = Dt.d4.st
  s5 : (T.s5.cl (Dt.z4 x) Dt.d5.rd).2 = Dt.d5.st
  s6 : (T.s6.cl (Dt.y6 x) Dt.d6.rd).2 = Dt.d6.st
  s7 : (T.s7.cl (Dt.y7 x) Dt.d7.rd).2 = Dt.d7.st

/-- The targets that the letters' claims name are the readings of the targets in the data. -/
structure TgIs {M X : Type} {T : LayTail K M X} (Dt : TailH ρ T) (x : X) : Prop where
  t1 : (T.s1.cl (Dt.y1 x) Dt.d1.rd).1 = ρ.val Dt.d1.t
  t2 : (T.s2.cl (Dt.y2 x) Dt.d2.rd).1 = ρ.val Dt.d2.t
  t3 : (T.s3.cl (Dt.z2 x) Dt.d3.rd).1 = ρ.val Dt.d3.t
  t4 : (T.s4.cl (Dt.y4 x) Dt.d4.rd).1 = ρ.val Dt.d4.t
  t5 : (T.s5.cl (Dt.z4 x) Dt.d5.rd).1 = ρ.val Dt.d5.t
  t6 : (T.s6.cl (Dt.y6 x) Dt.d6.rd).1 = ρ.val Dt.d6.t
  t7 : (T.s7.cl (Dt.y7 x) Dt.d7.rd).1 = ρ.val Dt.d7.t

theorem claims_of {M X : Type} {T : LayTail K M X} (Dt : TailH ρ T) (x : X) (s : StIs ρ Dt x)
    (t : TgIs ρ Dt x) : Dt.Claims x :=
  ⟨Prod.ext t.t1 s.s1, Prod.ext t.t2 s.s2, Prod.ext t.t3 s.s3, Prod.ext t.t4 s.s4,
    Prod.ext t.t5 s.s5, Prod.ext t.t6 s.s6, Prod.ext t.t7 s.s7⟩

/-! ### The additions that the chain itself names -/

/-- A list of the names of each sumcheck's end values. -/
structure Shs {M X : Type} (T : LayTail K M X) where
  n1 : List T.s1.L.S.A
  n2 : List T.s2.L.S.A
  n3 : List T.s3.L.S.A
  n4 : List T.s4.L.S.A
  n5 : List T.s5.L.S.A
  n6 : List T.s6.L.S.A
  n7 : List T.s7.L.S.A

section Canon
variable (D : OwnH) (nz : Nz7 ρ D) (H0 : Heard) (O : Own) (hd2 : Level) (p1 p3 p4 p5 p6 : Psc)
  {M X : Type} {T : LayTail K M X} (N : Shs T) (x : X)

/-- The data of the stages, one after the other: each state is the one that the letters' claim
names at the statement which the stages before have made; the end values are those heard, read. -/
noncomputable def c1 : StgH ρ T.s1 :=
  ⟨[], D.H1, nz.b1, valsOf ρ N.n1 D.H1.v,
    (T.s1.cl (((x, rd ρ T.nL D.vW), ρ.val D.xL), rd ρ T.gN (D.dI.elems.map E.ofTriple))
      (rd ρ T.s1.n [])).2, p1.target⟩

noncomputable def w1 : T.s1.Nx :=
  (c1 ρ D nz p1 N x).nx (((x, rd ρ T.nL D.vW), ρ.val D.xL), rd ρ T.gN (D.dI.elems.map E.ofTriple))

noncomputable def c2 : StgH ρ T.s2 :=
  ⟨[D.cl2], D.H2, nz.b2, valsOf ρ N.n2 D.H2.v,
    (T.s2.cl (((w1 ρ D nz p1 N x, ρ.val H0.wpl.tau), rd ρ T.nP D.vP), ρ.val D.xP)
      (rd ρ T.s2.n [D.cl2])).2, H0.tV.p.target⟩

noncomputable def w2 : T.s2.Nx :=
  (c2 ρ D nz H0 p1 N x).nx (((w1 ρ D nz p1 N x, ρ.val H0.wpl.tau), rd ρ T.nP D.vP), ρ.val D.xP)

noncomputable def c3 : StgH ρ T.s3 :=
  ⟨[D.cl3], D.H3, nz.b3, valsOf ρ N.n3 D.H3.v,
    (T.s3.cl (w2 ρ D nz H0 p1 N x) (rd ρ T.s3.n [D.cl3])).2, p3.target⟩

noncomputable def w3 : T.s3.Nx := (c3 ρ D nz H0 p1 p3 N x).nx (w2 ρ D nz H0 p1 N x)

noncomputable def c4 : StgH ρ T.s4 :=
  ⟨[], D.H4, nz.b4, valsOf ρ N.n4 D.H4.v,
    (T.s4.cl (w3 ρ D nz H0 p1 p3 N x, ρ.val D.x4) (rd ρ T.s4.n [])).2, p4.target⟩

noncomputable def w4 : T.s4.Nx :=
  (c4 ρ D nz H0 p1 p3 p4 N x).nx (w3 ρ D nz H0 p1 p3 N x, ρ.val D.x4)

noncomputable def c5 : StgH ρ T.s5 :=
  ⟨[], D.H5, nz.b5, valsOf ρ N.n5 D.H5.v,
    (T.s5.cl (w4 ρ D nz H0 p1 p3 p4 N x) (rd ρ T.s5.n [])).2, p5.target⟩

noncomputable def w5 : T.s5.Nx := (c5 ρ D nz H0 p1 p3 p4 p5 N x).nx (w4 ρ D nz H0 p1 p3 p4 N x)

noncomputable def c6 : StgH ρ T.s6 :=
  ⟨[], D.H6, nz.b6, valsOf ρ N.n6 D.H6.v,
    (T.s6.cl ((w5 ρ D nz H0 p1 p3 p4 p5 N x, ρ.val O.hd.tau),
      rd ρ T.gR (D.dM.elems.map E.ofTriple)) (rd ρ T.s6.n [])).2, p6.target⟩

noncomputable def w6 : T.s6.Nx :=
  (c6 ρ D nz H0 O p1 p3 p4 p5 p6 N x).nx ((w5 ρ D nz H0 p1 p3 p4 p5 N x, ρ.val O.hd.tau),
    rd ρ T.gR (D.dM.elems.map E.ofTriple))

noncomputable def c7 : StgH ρ T.s7 :=
  ⟨[], D.H7, nz.b7, valsOf ρ N.n7 D.H7.v,
    (T.s7.cl (((w6 ρ D nz H0 O p1 p3 p4 p5 p6 N x, ρ.val hd2.tau), rd ρ T.nW D.vE), ρ.val D.xW)
      (rd ρ T.s7.n [])).2, O.wo.p.target⟩

/-- The additions. -/
noncomputable def canon : TailAdd T where
  v1 := valsOf ρ N.n1 D.H1.v
  st1 := (c1 ρ D nz p1 N x).st
  v2 := valsOf ρ N.n2 D.H2.v
  st2 := (c2 ρ D nz H0 p1 N x).st
  v3 := valsOf ρ N.n3 D.H3.v
  st3 := (c3 ρ D nz H0 p1 p3 N x).st
  v4 := valsOf ρ N.n4 D.H4.v
  st4 := (c4 ρ D nz H0 p1 p3 p4 N x).st
  v5 := valsOf ρ N.n5 D.H5.v
  st5 := (c5 ρ D nz H0 p1 p3 p4 p5 N x).st
  v6 := valsOf ρ N.n6 D.H6.v
  st6 := (c6 ρ D nz H0 O p1 p3 p4 p5 p6 N x).st
  v7 := valsOf ρ N.n7 D.H7.v
  st7 := (c7 ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).st

/-- The typed data with these additions. -/
noncomputable def tailC : TailH ρ T :=
  D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 (canon ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x)

/-- Their states are those that the letters' claims name. -/
theorem tailC_st : StIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tailC_of : TailOf ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) D H0 O hd2 p1 p3 p4 p5 p6 :=
  tail_of ρ D nz H0 O hd2 p1 p3 p4 p5 p6 _

/-- So the letters' claims hold of them as soon as the seven targets agree. -/
theorem tailC_claims (t : TgIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) x) :
    (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).Claims x :=
  claims_of ρ _ x (tailC_st ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) t

end Canon

/-! ### The two token sumchecks' targets -/

omit [Fintype K] in
/-- The target in a token sumcheck's record reads as the scalar that rode in its first message. -/
theorem TokSaid.target {P : Array E} {lt shown dY : Nat} {F G : Fork} {t : Tsc} {x : E} {H : PscH}
    (s : TokSaid P lt shown dY F G t x H) : ρ.val t.p.target = ρ.val x := by
  rw [s.psc.target, ρ.add, ρ.mul, ρ.zero, ρ.one, zero_add, one_mul]

/-- The two token sumchecks' targets read as the scalars that rode. -/
structure TokTg (D : OwnH) (H0 : Heard) (p3 : Psc) : Prop where
  t2 : ρ.val H0.tV.p.target = ρ.val D.cl2
  t3 : ρ.val p3.target = ρ.val D.cl3

omit [Fintype K] in
/-- `own_recs` (OnBytes/Tie/Pv/Lay/HearTieAll.lean) with these two. -/
theorem own_recs2 {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {O : Own} {F G : Fork}
    {D : OwnH} {H0 : Heard} {tT : Tsc} {hd2 : Level} {claims : Array WsClaim}
    (s : OwnSaidL P hp g fo O F G D H0 tT hd2 claims) :
    ∃ p1 p3 p4 p5 p6 : Psc, Recs7 P hp g O D H0 tT hd2 p1 p3 p4 p5 p6 ∧ TokTg ρ D H0 p3 := by
  obtain ⟨F4, F7, F8, F1, F1', F2, F3, F3', F5, F6, t3, C, p4, c1, c5, _, a2, _, _, a5, a6, a7, a8,
    _, _, a11, _, _, _, a14, _, _, a17⟩ := s.recs
  obtain ⟨p1, b1, b2⟩ := a2.recAt
  obtain ⟨tT', Fm, e1, g5, g6⟩ := a14.said
  have et : tT' = tT := Option.some.inj (e1.symm.trans s.hasT)
  rw [et] at g6
  obtain ⟨p5, b5, d5⟩ := g5.recAt
  obtain ⟨p6, b6, d6⟩ := g6.recAt
  exact ⟨p1, t3.p, p4, p5, p6, ⟨b1, b2, a5.recAt, a6.recAt, by rw [a7], by rw [a8], a11.recAt,
    a11.row, b5, d5, b6, d6, a17.recAt⟩, a5.target ρ, a6.target ρ⟩

/-! ### At the records -/

/-- The five other targets. -/
structure Tg5 {M X : Type} {T : LayTail K M X} (Dt : TailH ρ T) (x : X) : Prop where
  t1 : (T.s1.cl (Dt.y1 x) Dt.d1.rd).1 = ρ.val Dt.d1.t
  t4 : (T.s4.cl (Dt.y4 x) Dt.d4.rd).1 = ρ.val Dt.d4.t
  t5 : (T.s5.cl (Dt.z4 x) Dt.d5.rd).1 = ρ.val Dt.d5.t
  t6 : (T.s6.cl (Dt.y6 x) Dt.d6.rd).1 = ρ.val Dt.d6.t
  t7 : (T.s7.cl (Dt.y7 x) Dt.d7.rd).1 = ρ.val Dt.d7.t

/-- At the records of Cb/Pv/Lay/OwnAll.lean a token sumcheck's claim names the scalar that rode as
its target: so the letters' claims hold of the chain's own data as soon as the five other targets
agree. -/
theorem layV_claims {M X : Type} (V : LayV K M X) (D : OwnH) (nz : Nz7 ρ D) (H0 : Heard) (O : Own)
    (hd2 : Level) (p1 p3 p4 p5 p6 : Psc) (N : Shs V.toTail) (x : X) (tt : TokTg ρ D H0 p3)
    (t : Tg5 ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) x) :
    (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).Claims x :=
  tailC_claims ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x
    ⟨t.t1, tt.t2.symm, tt.t3.symm, t.t4, t.t5, t.t6, t.t7⟩

theorem layVF_claims {M X : Type} (V : LayVF K M X) (D : OwnH) (nz : Nz7 ρ D) (H0 : Heard)
    (O : Own) (hd2 : Level) (p1 p3 p4 p5 p6 : Psc) (N : Shs V.toTail) (x : X)
    (tt : TokTg ρ D H0 p3) (t : Tg5 ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) x) :
    (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).Claims x :=
  tailC_claims ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x
    ⟨t.t1, tt.t2.symm, tt.t3.symm, t.t4, t.t5, t.t6, t.t7⟩

/-! ### The fit of the weights, from the variables' forms -/

/-- All variables in the equality form, at the readings of z, under the pick of the constant
coefficient. -/
theorem stgFits_eq {M X : Type} (S : Stg K M X) (st : S.L.St) (z : Fin S.L.S.k → E)
    (hF : S.F = F₀ S.L.T.par) (hn : ∀ i, S.L.M.n i = 2)
    (hw : ∀ i, S.L.S.w st i = some (ρ.val (z i))) :
    StgFits ρ S st (List.ofFn fun i => Weight.equality (z i) 3) S.L.S.k S.L.M.DY := by
  refine ⟨rfl, rfl, hn, ?_⟩
  have h := sum_fits_eq ρ S.L st z hw
  rw [show (fun i => Weight.equality (z i) (S.L.M.n i + 1)) = fun i => Weight.equality (z i) 3 from
    funext fun i => by rw [hn i]] at h
  rw [hF]
  exact h

/-- All variables plain, under the pick of the linear coefficient. -/
theorem stgFits_plain {M X : Type} (S : Stg K M X) (st : S.L.St)
    (hF : S.F = fun st => pick (S.L.T.par.vars st)) (hn : ∀ i, S.L.M.n i = 2)
    (hw : ∀ i, S.L.S.w st i = none) :
    StgFits ρ S st (List.replicate S.L.S.k (Weight.plain 3)) S.L.S.k S.L.M.DY := by
  refine ⟨rfl, rfl, hn, ?_⟩
  rw [hF]
  exact plain2_fits ρ S.L st hn hw

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.own_recs2
#print axioms OnBytes.Tie.Pv.Lay.layV_claims
#print axioms OnBytes.Tie.Pv.Lay.layVF_claims
#print axioms OnBytes.Tie.Pv.Lay.stgFits_eq
#print axioms OnBytes.Tie.Pv.Lay.stgFits_plain
#print axioms OnBytes.Tie.Pv.Lay.map_valsOf
#print axioms OnBytes.Tie.Pv.Lay.claims_of
#print axioms OnBytes.Tie.Pv.Lay.tailC_st
#print axioms OnBytes.Tie.Pv.Lay.tailC_claims
#print axioms OnBytes.Tie.Pv.Lay.TokSaid.target
