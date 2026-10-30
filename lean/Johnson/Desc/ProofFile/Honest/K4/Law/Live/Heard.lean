-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/Heard.lean: CONDITIONAL. THE FOUR ROUTINES BY WHICH THE
FUNCTION THAT READS THE LAYERS' OWN ROUNDS (sub-protocol K4) READS A MASKED SUMCHECK, WHERE THEY
RETURN FROM A TAPE THAT MEETS `TapeLive`: THE SUMCHECK's STATE IS LIVE, AND THE NUMBERS OF ITS
SLOTS.

What is here. A LAW ON THE VERIFIER's TEXT: the honest prover is not in it. Four statements, each
from a return of a routine at a ledger F and a tape t that meets `TapeLive` (Law/Live/PscLive.lean).
p is the sumcheck's state as it stands when its own claim is made. Each proof reads the library's
lemma that takes the routine apart "with what the tape was" (OnBytes/Desc/First/P1/FlTape.lean,
TscLaw.lean, FlSpec.lean; OnBytes/Desc/First/K4/StackTape.lean; Johnson/Top/H0/MergeLaw/Hear.lean,
Flat.lean).

  `level_live`: a layer of a product tree (`Fl.levelIn`), F with arrays of the right sizes: p is
      `PscLive`; its start form is the form handed in, which names slots that are filled in F alone;
      its first slot is F's next free number; its window's length; THE LAYER's OWN CLAIM IS p's
      `rowForm`; the slots of its two end values, as F's next free number plus numbers of the plan;
      the ledger left has arrays of the right sizes, and its next free number is stated; the tape
      left meets `TapeLive`.
  `tsc_live`: a token sumcheck (`Fl.tscIn`): the same list, BUT: its start form is the slot of
      its claimed sum, which is F's next free number, a slot that the routine itself takes: so
      nothing is said of slots filled in F; its first slot is one behind that; in the two end
      values' stead: the slot sEnd of the first of its n end values, with the ledger's next free
      number n further on; and its own claim is not made by this routine.
  `stack_live`: the batched sumcheck (`hearStack`): the same list as the layer's, with its own
      claim p's `rowForm`, its four slot fields, the return of `joinStart` that makes its start
      form, and that the batching element x, with whose powers (1, x) that form is built, reads as
      neither 0 nor 1.
  `merge_live`: the merge (`flatForkEnd`), at any ledger F: p is `PscLive`; its start form,
      which names slots that are filled in F alone; that its batching element reads as not 0; its
      first slot; its window's length; the slot of its end value. NOTHING IS SAID OF THE LEDGER OR
      OF THE TAPE THAT IT LEAVES.
  `pscLive_of_tape`, `atZero_isEq`: the state is live, from the library's two lists, the tape,
      and that eps and the further variable's challenge read as not 0; the weight of the further
      variable is an equality weight.

Kin. From a return of the description's own hearing of a masked sumcheck (`MaskedSum.hear`,
`MaskedSum.whole`), not of the verifier program's four routines: `record_coef`, `whole_coef`
(Honest/K3/Good/Coef.lean): where each challenge reads as not 0, the row has a coefficient that is
not 0 on each of the sumcheck's own slots. At the output head's sums: `live_own`, `live_lead`
(Honest/K6/GoodLaw/Coef.lean): these slots, and the slot of the claimed sum, are live. Of a merge's
state the library states the like facts as a condition on the head's state (`MergeLive`,
Johnson/Desc/K11/Live/RunStatement.lean) and draws `liveAt` from it (`walk_at`, `mergeRunLive`,
`mergeRunLiveStart`, Johnson/Desc/K11/Live/Run.lean); `merge_live` shows them of the layers' merge
from a return and a tape. `tsc_win` (Johnson/Road/K4/Slots/HearSpares.lean) has `tsc_live`'s window
within the slots taken, without a tape's clause. Where the batched sumcheck's stretch is shown to
return, `StackLeft` (Johnson/Desc/First/K4/Returns/Stack.lean) states the four slot fields of
`stack_live` (sA0, sH1, sB0, sV) by the same numbers.

Not shown here. THAT ANY TAPE MEETS `TapeLive`. That a routine returns. One direction: from a
return. Nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.PscLive
import OnBytes.Desc.First.P1.TscLaw
import OnBytes.Desc.First.K4.StackTape
import Johnson.Top.H0.MergeLaw.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Heard HeardStack)
open OnBytes.Psc (Weight)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (engFl hearStack joinStart)
open OnBytes.Desc.First.K4.Slots (run_same)
open OnBytes.Desc.First.P1 (msOf Rnd levelWs tscWs plainWs levelIn_tape tscIn_tape
  filledA_of_publicPart)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat mergeHear_inv)

/-- The state is live: from the library's two lists and the tape. ws: the weights of the rounds rs;
y: the round in the further variable. -/
theorem pscLive_of_tape {p : Psc} {t : Tape} (T : TapeLive t) {ws : List Weight}
    {rs : List FlatRound} {y : Rnd} (he : Reading.gl.val p.eps ≠ 0)
    (hv : p.vars.toList = ws ++ [y.1]) (hws : ∀ w ∈ ws, IsEqOrPlain w) (hwy : IsEqOrPlain y.1)
    (hr : p.r.toList = (msOf ws rs ++ [y]).map (·.2.2)) (hrs : ∀ x ∈ rs, x ∈ t)
    (h1 : ∀ x ∈ rs, x.drawn.length = 1) (hb : Reading.gl.val y.2.2 ≠ 0) : PscLive p := by
  refine pscLive_of he (fun w hw => ?_) fun g hg => ?_
  · rw [hv] at hw
    rcases List.mem_append.1 hw with hw | hw
    · exact hws w hw
    · rw [List.mem_singleton.1 hw]
      exact hwy
  · rw [hr] at hg
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hg
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨x, hx, e⟩ := msOf_drawn ws rs h1 m hm
      exact (T x (hrs x hx) _ e).1
    · rw [List.mem_singleton.1 hm]
      exact hb

theorem atZero_isEq (d : ℕ) : IsEqOrPlain (Weight.atZero d) := Or.inl ⟨zeroE, d, rfl⟩

/-- CONDITIONAL. **A layer of a product tree.** -/
theorem level_live {mu : ℕ} {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork} {t u : Tape}
    {L : Level} (hF : Sized F) (h : Fl.levelIn mu rho C order F t = some (L, G, u))
    (T : TapeLive t) :
    ∃ (p : Psc) (S0 : E), PscLive p ∧ p.start = C ∧ p.first = F.next ∧
      p.walk.1.length = 1 + 2 * mu + 2 ∧ L.row = p.rowForm S0 {} ∧
      L.sL = F.next + 1 + 2 * mu + 2 ∧ L.sR = L.sL + 1 ∧ Fo.FilledA F C ∧
      Sized G ∧ G.next = F.next + 1 + 2 * mu + 2 + 2 ∧ TapeLive u := by
  obtain ⟨hlen, T0, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, ht,
    hrs, hall, -, -, hms, hy, -, hpub, hmap, -, -, -, hvars, hr, -, -, heps, hstart, hfirst, hrow,
    -, hsL, hsR, -, hrun, -, -, hrun2⟩ := levelIn_tape h
  subst hms hy
  have hwl : (levelWs mu rho order).length = mu := by
    unfold levelWs
    rw [List.length_map, hlen]
  have h3 : ∀ w ∈ levelWs mu rho order, w.d = 3 := fun w hw => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw
    rfl
  have hE : ∀ w ∈ levelWs mu rho order, IsEqOrPlain w := fun w hw => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw
    exact Or.inl ⟨_, 3, rfl⟩
  have hml : (msOf (levelWs mu rho order) rs).length = mu := by
    have := congrArg List.length hmap
    rw [List.length_map, hwl] at this
    exact this
  have L1 : PscLive p := by
    refine pscLive_of_tape T (rs := rs) (y := (Weight.atZero 3, sentY, beta)) ?_ hvars hE
      (atZero_isEq 3) hr (fun x hx => ?_) (fun x hx => (hall x hx).2.2) ?_
    · rw [heps]
      exact T.at_ (by rw [ht]; exact List.mem_cons_self)
    · rw [ht]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
    · exact T.at_ (by
        rw [ht]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have hw : p.walk.1.length = 1 + 2 * mu + 2 := by
    have := win_len p (levelWs mu rho order) 2 h3 hvars (by
      rw [hr, List.length_map, List.length_append, hml, hwl]
      rfl)
    rw [hwl] at this
    exact this
  obtain ⟨s1, n1, -⟩ :=
    run_same (show Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) from hF) hrun
  obtain ⟨s2, n2, -⟩ := run_same s1 hrun2
  exact ⟨p, _, L1, hstart, hfirst, hw, hrow, hsL, hsR, filledA_of_publicPart hpub, s2,
    n2.trans n1, T.sub fun r hr => by
      rw [ht]
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))⟩

/-- CONDITIONAL. **A token sumcheck.** -/
theorem tsc_live {P : Array E} {lt n dY : ℕ} {F G : Fork} {t u : Tape} {o : Tsc} (hF : Sized F)
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) (T : TapeLive t) :
    PscLive o.p ∧ o.sCl = F.next ∧ o.p.start = Aff.slot F.next ∧ o.p.first = F.next + 1 ∧
      o.p.walk.1.length = 1 + 2 * lt + dY ∧ o.sEnd = F.next + 1 + 1 + 2 * lt + dY ∧
      Sized G ∧ G.next = F.next + 1 + 1 + 2 * lt + dY + n ∧ TapeLive u := by
  obtain ⟨hlt, T0, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0, ht, hrs, hall,
    hms, hy, -, hsCl, -, hrun0, -, hmap, -, -, -, hvars, hr, -, -, heps, hstart, hfirst, -, hsEnd,
    -, hrun⟩ := tscIn_tape h
  subst hms hy
  have htl : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    omega
  have hwl : (tscWs (P.toList.take lt)).length = lt := by
    unfold tscWs
    rw [List.length_map, htl]
  have h3 : ∀ w ∈ tscWs (P.toList.take lt), w.d = 3 := fun w hw => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw
    rfl
  have hE : ∀ w ∈ tscWs (P.toList.take lt), IsEqOrPlain w := fun w hw => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw
    exact Or.inl ⟨_, 3, rfl⟩
  have hml : (msOf (tscWs (P.toList.take lt)) rs).length = lt := by
    have := congrArg List.length hmap
    rw [List.length_map, hwl] at this
    exact this
  have L1 : PscLive o.p := by
    refine pscLive_of_tape T (rs := rs) (y := (Weight.atZero (dY + 1), sentY, beta)) ?_ hvars hE
      (atZero_isEq _) hr (fun x hx => ?_) (fun x hx => (hall x hx).2.2) ?_
    · rw [heps]
      exact T.at_ (by rw [ht]; exact List.mem_cons_self)
    · rw [ht]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
    · exact T.at_ (by
        rw [ht]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have hw : o.p.walk.1.length = 1 + 2 * lt + dY := by
    have := win_len o.p (tscWs (P.toList.take lt)) dY h3 hvars (by
      rw [hr, List.length_map, List.length_append, hml, hwl]
      rfl)
    rw [hwl] at this
    exact this
  obtain ⟨s0, n0, -⟩ := run_same (show Sized ({ F with next := F.next + 1 } : Fork) from hF) hrun0
  have n0' : G0.next = F.next + 1 := n0
  obtain ⟨s1, n1, -⟩ := run_same (show Sized ({ G0 with
    next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) from s0) hrun
  have n1' : G.next = G0.next + 1 + 2 * (P.toList.take lt).length + dY + n := n1
  refine ⟨L1, hsCl, hstart, by rw [hfirst, n0'], hw, ?_, s1, ?_, T.sub fun r hr => ?_⟩
  · rw [hsEnd, n0', htl]
  · rw [n1', n0', htl]
  · rw [ht]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hr)))

/-- CONDITIONAL. **The batched sumcheck.** x: the batching element; the start form C is built with
its powers (1, x). -/
theorem stack_live {P : Layer.Pub} {v : Layer.Env} {H : Heard} {lamS NCLp : ℕ} {F G : Fork}
    {t u : Tape}
    {K : HeardStack} (hF : Sized F)
    (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) (T : TapeLive t) :
    ∃ (p : Psc) (S0 x : E) (C : Aff), PscLive p ∧ p.start = C ∧ p.first = F.next ∧
      p.walk.1.length = 1 + 2 * lamS + 2 ∧ K.rowS = p.rowForm S0 {} ∧
      joinStart engFl v H (powers x 2) F (t.drop 1) = some (C, F, t.drop 1) ∧
      Reading.gl.val x ≠ 0 ∧ Reading.gl.val x ≠ 1 ∧
      K.sA0 = F.next + 1 + 2 * lamS + 2 ∧ K.sH1 = K.sA0 + 1 ∧
      K.sB0 = K.sH1 + (1 + P.y.LamM) ∧ K.sV = K.sB0 + 1 ∧ Fo.FilledA F C ∧ Sized G ∧
      G.next = F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) ∧ TapeLive u := by
  obtain ⟨x, mu0, eps, beta, T0, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, ht, hrs, hall,
    hjoin, hpub, hms, hy, hp, hmap, -, -, -, hA0, hH1, hB0, hV, -, hrun, hrow, hrun2⟩ :=
    OnBytes.Desc.First.K4.hearStack_tape h
  subst hms hy
  obtain ⟨ev, er, ee, es, ef⟩ : p.vars.toList = plainWs lamS ++ [Weight.atZero 3] ∧
      p.r.toList = (msOf (plainWs lamS) rs ++ [(Weight.atZero 3, sentY, beta)]).map (·.2.2) ∧
      p.eps = eps ∧ p.start = C ∧ p.first = F.next := by
    obtain ⟨a1, a2, -, a4, -, a6, a7⟩ := OnBytes.Desc.First.P1.endP_spec
      { target := T0, first := F.next, eps := eps, claim := addE mu0 (mulE eps T0), start := C,
        started := true } (msOf (plainWs lamS) rs) (Weight.atZero 3, sentY, beta)
    rw [← hp] at a1 a2 a4 a6 a7
    refine ⟨?_, ?_, a6, a4, a7⟩
    · rw [a1, List.map_append, hmap]
      rfl
    · rw [a2]
      rfl
  have hwl : (plainWs lamS).length = lamS := by
    unfold plainWs
    rw [List.length_replicate]
  have h3 : ∀ w ∈ plainWs lamS, w.d = 3 := fun w hw => by
    rw [List.eq_of_mem_replicate hw]
    rfl
  have hE : ∀ w ∈ plainWs lamS, IsEqOrPlain w := fun w hw =>
    Or.inr ⟨3, List.eq_of_mem_replicate hw⟩
  have hml : (msOf (plainWs lamS) rs).length = lamS := by
    have := congrArg List.length hmap
    rw [List.length_map, hwl] at this
    exact this
  have L1 : PscLive p := by
    refine pscLive_of_tape T (rs := rs) (y := (Weight.atZero 3, sentY, beta)) ?_ ev hE
      (atZero_isEq 3) er (fun z hz => ?_) (fun z hz => (hall z hz).2.2) ?_
    · rw [ee]
      exact T.at_ (by
        rw [ht]
        exact List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [ht]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hz))
    · exact T.at_ (by
        rw [ht]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append_right _ List.mem_cons_self)))
  have hw : p.walk.1.length = 1 + 2 * lamS + 2 := by
    have := win_len p (plainWs lamS) 2 h3 ev (by
      rw [er, List.length_map, List.length_append, hml, hwl]
      rfl)
    rw [hwl] at this
    exact this
  have hx : (⟨some RoundName.batSigma.name, 0, 2, [], [x]⟩ : FlatRound) ∈ t := by
    rw [ht]
    exact List.mem_cons_self
  obtain ⟨s1, n1, -⟩ := run_same (show Sized ({ F with
    next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork) from hF) hrun
  obtain ⟨s2, n2, -⟩ := run_same s1 hrun2
  exact ⟨p, _, x, C, L1, es, ef, hw, hrow, hjoin, T.at_ hx, T.ne_one_bat hx, hA0, hH1, hB0, hV,
    filledA_of_publicPart hpub, s2, n2.trans n1, T.sub fun r hr => by
      rw [ht]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))⟩

/-- CONDITIONAL. **The merge.** x: its batching element. -/
theorem merge_live {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) (T : TapeLive t) :
    ∃ x : E, PscLive wo.p ∧ wo.p.start = wsForkStart sv (powers x sv.size) ∧
      Reading.gl.val x ≠ 0 ∧ wo.p.first = F.next ∧ wo.p.walk.1.length = 1 + 2 * lay.lk + 1 ∧
      wo.sFv = F.next + 1 + 2 * lay.lk + 1 ∧
      Fo.FilledA F (wsForkStart sv (powers x sv.size)) := by
  obtain ⟨x, mu, eps, c, beta, v, T0, r1, rY, rV, qs, hq, -, ht, hpub, heps, -, -, -, -, hr, hsF,
    -, -, -, hvars, hfirst, hstart, -⟩ := mergeHear_inv (hear_of_flat h)
  have h3 : ∀ w ∈ List.replicate lay.lk (Weight.plain 3), w.d = 3 := fun w hw => by
    rw [List.eq_of_mem_replicate hw]
    rfl
  have L1 : PscLive wo.p := by
    refine pscLive_of ?_ (fun w hw => ?_) fun g hg => ?_
    · rw [heps]
      exact T.at_ (by
        rw [ht]
        exact List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [hvars] at hw
      rcases List.mem_append.1 hw with hw | hw
      · exact Or.inr ⟨3, List.eq_of_mem_replicate hw⟩
      · rw [List.mem_singleton.1 hw]
        exact atZero_isEq 2
    · rw [hr] at hg
      rcases List.mem_append.1 hg with hg | hg
      · obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hg
        refine T.at_ (nm := some RoundName.pscRound.name) (z := 0) (w := q.1) (s := q.2.1) ?_
        rw [ht]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_map.2 ⟨q, hq', rfl⟩)))
      · rw [List.mem_singleton.1 hg]
        exact T.at_ (by
          rw [ht]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ List.mem_cons_self)))
  have hw : wo.p.walk.1.length = 1 + 2 * lay.lk + 1 := by
    have := win_len wo.p (List.replicate lay.lk (Weight.plain 3)) 1 h3 hvars (by
      rw [hr, List.length_append, List.length_map, hq, List.length_replicate]
      rfl)
    rw [List.length_replicate] at this
    exact this
  exact ⟨x, L1, hstart, T.at_ (by rw [ht]; exact List.mem_cons_self), hfirst, hw, hsF,
    filledA_of_publicPart hpub⟩

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.pscLive_of_tape
#print axioms ProofFile.Honest.K4.Live.atZero_isEq
#print axioms ProofFile.Honest.K4.Live.level_live
#print axioms ProofFile.Honest.K4.Live.tsc_live
#print axioms ProofFile.Honest.K4.Live.stack_live
#print axioms ProofFile.Honest.K4.Live.merge_live
