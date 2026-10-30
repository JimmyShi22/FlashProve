-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/HeadLens.lean: the lengths of the points of the output head's sub-proof, from the
verifier's own routine that hears its messages.

Johnson/Road/HeadMet.lean gathers in the record PointsH the lengths of eight points from which the
verifier makes the weights of its tables of reads. This file shows the record of what the routine
hear (OnBytes/Model/HeadHeard.lean) returns in a run on a view, for a layout that the verifier
returns.

How. Three of the points are the challenges of token sumchecks: the loop of such a sumcheck appends
one challenge for each coordinate that it is given, and it is given lt of them (a public test). That
holds in every run. The other five are parts of the lookup's point and the point P_V:
Johnson/Road/HeadPoint.lean and Johnson/Road/HeadView.lean have their lengths, in a run on a view.

Main theorems: subMust_bind; tscLoop_size, tscRounds_size, tscIn_size, channelRounds_size;
hearProducts_size, hearStream_size, hearLogits_size; sums_of_hear (the three sumchecks' challenges
are lt each, and the channels' challenges as many as the plan says); pointsH_of_run.

What is not claimed. That hear succeeds is a hypothesis. Nothing on how a point was drawn or on what
a sumcheck shows. The program does not import this file.
-/
import Johnson.Road.HeadView
import Johnson.Road.HeadMet

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Reading Fork SubM)

/-- A public condition of a sub-proof's routine, and what follows it. -/
theorem subMust_bind {β : Type} {b : Bool} {f : Unit → SubM β} {F G : Fork} {C D : Ctx} {y : β}
    (h : Ok (SubM.must b >>= f) F C y G D) : b = true ∧ Ok (f ()) F C y G D := by
  obtain ⟨u, F1, C1, h1, h2⟩ := bind_ok h
  obtain ⟨e1, eF⟩ := (ok_lift (Blk.must b) F F1 C C1 u).1 h1
  obtain ⟨e2, eC⟩ := (Blk.yields_must b C C1).1 ((Blk.yields_iff _ _ _ _).2 e1)
  rw [eF, eC] at h2
  exact ⟨e2, h2⟩

/-- The loop of a token sumcheck appends one challenge for each coordinate. -/
theorem tscLoop_size : ∀ (zs : List E) (r : Array E) (p : Model.Psc) (F G : Fork) (C D : Ctx)
    (a : Array E × Model.Psc), Ok (Model.tscLoop zs r p) F C a G D →
    a.1.size = r.size + zs.length
  | [], r, p, F, G, C, D, a, h => by
    unfold Model.tscLoop at h
    obtain ⟨e, -, -⟩ := pure_ok h
    rw [e]
    rfl
  | z :: zs, r, p, F, G, C, D, a, h => by
    unfold Model.tscLoop at h
    obtain ⟨⟨x, p'⟩, F1, C1, -, h2⟩ := bind_ok h
    rw [tscLoop_size zs (r.push x) p' F1 G C1 D a h2, Array.size_push, List.length_cons]
    omega

/-- The rounds of a token sumcheck leave lt challenges. -/
theorem tscRounds_size {P : Array E} {lt : ℕ} {F G : Fork} {C D : Ctx} {o : Model.Tsc}
    (h : Ok (Model.tscRounds P lt) F C o G D) : o.r.size = lt := by
  unfold Model.tscRounds at h
  obtain ⟨e, h⟩ := subMust_bind h
  obtain ⟨sCl, _, _, -, h⟩ := bind_ok h
  obtain ⟨p, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨r, p'⟩, _, _, k, h⟩ := bind_ok h
  obtain ⟨eo, -, -⟩ := pure_ok h
  have hle : lt ≤ P.size := of_decide_eq_true e
  have ks := tscLoop_size _ _ _ _ _ _ _ _ k
  rw [eo]
  show r.size = lt
  have k2 : r.size = (#[] : Array E).size + (P.toList.take lt).length := ks
  rw [k2, List.length_take, Array.length_toList]
  have e0 : (#[] : Array E).size = 0 := rfl
  omega

/-- The whole token sumcheck leaves lt challenges. -/
theorem tscIn_size {P : Array E} {lt s d : ℕ} {F G : Fork} {C D : Ctx} {o : Model.Tsc}
    (h : Ok (Model.tscIn P lt s d) F C o G D) : o.r.size = lt := by
  unfold Model.tscIn at h
  obtain ⟨o', _, _, k, h⟩ := bind_ok h
  obtain ⟨⟨sEnd, p⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨eo, -, -⟩ := pure_ok h
  rw [eo]
  exact (tscRounds_size k : o'.r.size = lt)

/-- The rounds over the channels append one challenge each. -/
theorem channelRounds_size : ∀ (n : ℕ) (r : Array E) (p : Model.Psc) (F G : Fork) (C D : Ctx)
    (a : Array E × Model.Psc), Ok (Model.Head.channelRounds n r p) F C a G D →
    a.1.size = r.size + n
  | 0, r, p, F, G, C, D, a, h => by
    unfold Model.Head.channelRounds at h
    obtain ⟨e, -, -⟩ := pure_ok h
    rw [e]
    rfl
  | n + 1, r, p, F, G, C, D, a, h => by
    unfold Model.Head.channelRounds at h
    obtain ⟨⟨x, p'⟩, F1, C1, -, h2⟩ := bind_ok h
    rw [channelRounds_size n (r.push x) p' F1 G C1 D a h2, Array.size_push]
    omega

/-- The sumcheck of the row products has lt challenges. -/
theorem hearProducts_size {h : Model.Head.Shape} {PV : Array E} {F G : Fork} {C D : Ctx}
    {a : ℕ × Array E × Model.Tsc} (hx : Ok (Model.Head.hearProducts h PV) F C a G D) :
    a.2.2.r.size = h.lt := by
  unfold Model.Head.hearProducts at hx
  obtain ⟨_, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨_, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨tV, _, _, k, hx⟩ := bind_ok hx
  obtain ⟨_, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨⟨row, p⟩, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨ea, -, -⟩ := pure_ok hx
  rw [ea]
  exact (tscIn_size k : tV.r.size = h.lt)

/-- The sumcheck of the stream times the reciprocal has lt challenges. -/
theorem hearStream_size {h : Model.Head.Shape} {zt : Array E} {F G : Fork} {C D : Ctx}
    {a : Model.Tsc} (hx : Ok (Model.Head.hearStream h zt) F C a G D) : a.r.size = h.lt := by
  unfold Model.Head.hearStream at hx
  obtain ⟨tN, _, _, k, hx⟩ := bind_ok hx
  obtain ⟨_, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨_, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨⟨row, p⟩, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨ea, -, -⟩ := pure_ok hx
  rw [ea]
  exact (tscIn_size k : tN.r.size = h.lt)

/-- The sumcheck of the activations times the head's weights has lt challenges over the positions
and lam over the channels. -/
theorem hearLogits_size {h : Model.Head.Shape} {lam : ℕ} {zt : Array E} {F G : Fork} {C D : Ctx}
    {a : Model.Tsc × Array E} (hx : Ok (Model.Head.hearLogits h lam zt) F C a G D) :
    a.1.r.size = h.lt ∧ a.2.size = lam := by
  unfold Model.Head.hearLogits at hx
  obtain ⟨tH, _, _, k, hx⟩ := bind_ok hx
  obtain ⟨⟨r, p⟩, _, _, k2, hx⟩ := bind_ok hx
  obtain ⟨⟨sEnd, p'⟩, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨_, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨_, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨⟨row, p''⟩, _, _, -, hx⟩ := bind_ok hx
  obtain ⟨ea, -, -⟩ := pure_ok hx
  rw [ea]
  refine ⟨(tscRounds_size k : tH.r.size = h.lt), ?_⟩
  show r.reverse.size = lam
  have k3 : r.size = (#[] : Array E).size + lam := channelRounds_size _ _ _ _ _ _ _ _ k2
  have e0 : (#[] : Array E).size = 0 := rfl
  rw [Array.size_reverse, k3]
  omega

/-- **The challenges of the three token sumchecks are lt each, and those over the channels as many
as the plan says**: in every run in which hear succeeds. -/
theorem sums_of_hear {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    x.tV.r.size = h.lt ∧ x.tN.r.size = h.lt ∧ x.tH.r.size = h.lt ∧ x.rs.size = hp.lamS := by
  obtain ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, -, -, -, -, -, -, k7, -, -, k8, k9, -,
    rfl⟩ := hear_steps hx
  exact ⟨hearProducts_size k7, hearStream_size k8, (hearLogits_size k9).1,
    (hearLogits_size k9).2⟩

/-- **The record PointsH**, of what hear returns in a run on a view for a layout that the verifier
returns. -/
theorem pointsH_of_run {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    {hp : Model.Head.HPlanH2} {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard}
    {F0 G : Fork} {C D : Ctx} (hy : Model.Head.layout h tauFC = .ok L) (hd : C.ch.dry = false)
    (hx : Ok (Model.Head.hear h L hp cov plain) F0 C x G D) {R : Model.Head.Run} (e1 : R.h = h)
    (e2 : R.L = L) (e3 : R.x = x) : PointsH R := by
  have X := View.heardFits_of_view hd hx
  have S := sums_of_hear hx
  have P := View.PV_size hd hx
  subst e1 e2 e3
  exact {
    Zl := Zl_parts hy X
    zFC := fun q hq => (point_of_call hy X Reading.gl (callNo_lt hq)).2.2.1
    zROW := fun q hq => (point_of_call hy X Reading.gl (callNo_lt hq)).2.2.1
    zH := (point_of_call hy X Reading.gl (callNo_lt X.qH)).2.2.1
    tH := S.2.2.1
    PV := P
    tV := S.1
    tN := S.2.1 }

#print axioms sums_of_hear
#print axioms pointsH_of_run

end OnBytes.Road.Hd
