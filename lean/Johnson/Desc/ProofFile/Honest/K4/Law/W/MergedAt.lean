-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MergedAt.lean: CONDITIONAL.

Not shown here. OpensAt (Johnson/Road/K4/C/MergedOf.lean: the honest side's open tables read as the
library's vectors of the verifier's weight claims, panel by panel): a hypothesis; no statement here
leads to it; no member of it is evaluated in Lean. The left half (OpenedLeft), StackAt, the
library's LedG and DrawnIs, that the structure which the forms read is the verifier's (hv), that the
verifier's list of weight claims returns (hcl), that the weights' layout is one that wsLayOf returns
for a model with routed experts, with the widths d and fe of the layer sub-proof's shape:
hypotheses. That all of these hold together: no example is known. By a walk of import lines the
closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs),
through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under
Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness
or on any other property. No property is claimed.

The field merged of `OpenedOwn` (Johnson/Road/K4/W/OpenedOwn.lean), to the letter: the slot under
each weight claim's value is worth the sum that the claim speaks of in the matrix of the weights in
the honest side's input. From `merged_of_opens` (Johnson/Road/K4/C/MergedOf.lean): the end value's
place in the list by `ends_at`; the slot by the left half at that place; that the two lists of
claims are one by `sides_ce` and StackAt's ties; that there are as many claims as the plan says by
the library's `hearStack_public` and `claims_of_panels`.

  `sides_ce`   the environment of the claims that Sides.of lays.
  `ends_at`   an entry of the stretch of a list from n on.
  `claims_len`   the verifier's list has as many weight claims as the plan says.
  `own_merged`   OpenedOwn's field merged.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightStack
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SizesOfLed
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMergeStart
import Johnson.Road.K4.C.MergedOf
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE)
open OnBytes.Model (Reading World Fork Level Tsc Forest.Heard WsClaim WsShape wsLayOf)
open OnBytes.Model.Layer (Own ClaimEnv callsTS)
open OnBytes.K.Kc (Tape)
open OnBytes.Road (valsOf claimVal claims_of_panels toArray_getD)
open OnBytes.Road.K4 (LedG)
open OnBytes.Road.K4.C (OpensAt merged_of_opens stack_open sides_fields extract_at)
open OnBytes.Desc.First.K4 (hearStack_public)
open OnBytes.Desc.First.K4.Honest

/-- **The environment of the claims that Sides.of lays**: the verifier's, with placeholders for the
challenges. -/
theorem sides_ce {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}
    (h : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) :
    S.ce = { v := S.v, wsLay := Q.P.wsLay, rope := Q.P.rope,
             rs := Array.replicate Q.hp.lamS zeroE, rt := #[] } := by
  unfold OnBytes.Desc.First.K4.Honest.Sides.of at h
  obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨TS, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Z, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨cls, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨x, lfc⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨opens, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨gl, gr⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ends, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  rfl

/-- An entry of the stretch of a list from n on is the list's entry n places further. -/
theorem ends_at (l : List E) (n a : ℕ) :
    valsOf Reading.gl (l.toArray.extract n l.toArray.size) a =
      Reading.gl.val (l.getD (n + a) zeroE) := by
  unfold valsOf
  rw [extract_at, Nat.min_self, toArray_getD]
  by_cases c : n + a < l.toArray.size
  · rw [if_pos c]
  · rw [if_neg c, List.getD_eq_default _ _ (by simpa using c)]

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} {w : K4In} {h ds : List Fmt.Drawn}
  {seen : Seen} {SD : StackData} {e : List E} {Wd : World Cb.Gl.E}

/-- **The verifier's list has as many weight claims as the plan says.** CONDITIONAL: on the
hearing's return and the two returns named. -/
theorem claims_len
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    {TS : List ℕ} {cl : List WsClaim} (hTS : callsTS Q.P = some TS) {c : ClaimEnv}
    (hv : c.v = o.v) (hcl : c.weightClaims TS = some cl) :
    cl.length = Q.hp.NCL - (if (Q.g == 0) = true then 1 else 0) := by
  obtain ⟨_, _, TS', pans, _, _, _, _, _, _, _, _, _, _, _, hT', hp, _, hn, _⟩ :=
    hearStack_public L.c4
  obtain rfl : TS' = TS := Option.some.inj (hT'.symm.trans hTS)
  rw [← (claims_of_panels _ c hv.symm TS' hp hcl).1]
  simpa using hn

/-- **THE FIELD merged OF OpenedOwn.** CONDITIONAL: on every hypothesis named. -/
theorem own_merged
    (Lg : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3'
      G4 G5 u5)
    (hD : DrawnIs t ds) (hl4 : k4StartAt Q 4 ≤ ds.length)
    (L : OpenedLeft Wd Q o w h ds seen) (A : StackAt Q w h ds seen o SD e)
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q (pts4 Q w h ds) = some o.v) {TS : List ℕ}
    {cl : List WsClaim} (hTS : callsTS Q.P = some TS)
    (hcl : ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
              rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) (hd : s.d = Q.P.y.h.d)
    (hfe : s.fe = Q.P.y.h.fe) (hO : OpensAt SD Q.P.wsLay (wmOf w.w) cl) :
    ∀ a x, cl[a]? = some x →
      Wd.slot (o.K.sV + a) = claimVal Reading.gl Q.P.wsLay (wmOf w.w) x := by
  intro a x hx
  have hS := (stack_open A.data).1
  obtain ⟨_, _, _, hvS, _, hTS', _⟩ := sides_fields hS
  have eV : SD.S.v = o.v := Option.some.inj (hvS.symm.trans hv)
  have eT : SD.S.TS = TS := Option.some.inj (hTS'.symm.trans hTS)
  have hE := A.ends
  rw [A.rs] at hE
  have ert : (pts4 Q w h ds).rt = (o.H.tT.map (·.r)).getD #[] := by
    rw [A.rt _ Lg.kTT, Lg.kTT]
    rfl
  have hcl' : ({ SD.S.ce with rs := o.K.rs, rt := (pts4 Q w h ds).rt } :
      ClaimEnv).weightClaims SD.S.TS = some cl := by
    rw [sides_ce hS, eV, eT, ert]
    exact hcl
  have r := merged_of_opens A.data (rs_size Lg hD hl4) hE hcl' hl
    (by rw [eV, A.y]; exact hd) (by rw [eV, A.y]; exact hfe) (wmOf w.w) hO a x hx
  rw [ends_at] at r
  have ha : a < Q.hp.NCL - (if (Q.g == 0) = true then 1 else 0) := by
    rw [← claims_len Lg hTS rfl hcl]
    exact (List.getElem?_eq_some_iff.mp hx).1
  have es : o.K.sV + a = o.K.sA0 + (2 + SD.nVirt + a) := by
    have env : SD.nVirt = 1 + SD.S.v.y.LamM := rfl
    rw [L.sV, L.sB0, env, eV, A.y]
    omega
  have hn : 2 + SD.nVirt + a < nStack Q.P Q.hp Q.g := by
    have env : SD.nVirt = 1 + SD.S.v.y.LamM := rfl
    rw [env, eV, A.y]
    unfold nStack
    omega
  rw [es, L.stack _ hn, ← r]
  exact congrArg Reading.gl.val (stack_word A _)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.sides_ce
#print axioms ProofFile.Honest.K4.W.ends_at
#print axioms ProofFile.Honest.K4.W.claims_len
#print axioms ProofFile.Honest.K4.W.own_merged
