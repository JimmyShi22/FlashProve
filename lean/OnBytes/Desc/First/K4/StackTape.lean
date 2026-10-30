-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/StackTape.lean: the batched sumcheck of the layers' own rounds, `hearStack`
(OnBytes/Desc/First/K4/Hear.lean), over the plain engine `engFl` (K4/Plain.lean), TAKEN APART WHERE
IT RETURNS, with what the tape was. Statements and proofs.

  `shownRun_spec`: a run of shown values leaves ledger and tape as they are; what it returns is the
    run of what the ledger shows.
  `joinStart_quiet`: the start form is made without a step on the ledger or the tape.
  `hearStack_tape`: the tape begins with the round that draws x (of whose powers 1, x the start
    form is made), the sumcheck's beginning (mu0 sent, eps drawn), lamS rounds of degree 2 that are
    summed plainly, the round of the further variable (beta drawn) and the round of the end values.
    The record p behind these rounds is named; the row is p's form at the product of the two end
    elements; the four slots' numbers are said; the challenges are laid in the reverse of the
    rounds' order.

One direction: from a return. No law of a sumcheck is applied here. What the start form, the panels
and the two end elements mean is not said.
-/
import OnBytes.Desc.First.K4.Plain
import OnBytes.Desc.First.FlGrows
import OnBytes.Desc.First.P1.PlainTape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (bind_some pure_some need_some ask_some batch_spec pscBegin_tape
  plainRounds_tape pscEnds_tape pscRow_spec msOf plainWs endP endP_spec runP stepP Rnd Held
  claimAfter)

theorem drop_one' {α : Type} (a : α) (l : List α) : (a :: l).drop 1 = l := rfl

/-! ### Steps that read the ledger alone -/

theorem mapM_shown_list (first : Nat) : ∀ (l : List Nat) {F G : Fork} {t u : Tape} {a : List E},
    (l.mapM fun i => Fl.shown (first + i)) F t = some (a, G, u) →
    F = G ∧ t = u ∧ (l.mapM fun i => F.shown (first + i)) = some a
  | [], F, G, t, u, a, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp h
    exact ⟨rfl, rfl, rfl⟩
  | i :: l, F, G, t, u, a, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, G1, u1, h1, k1⟩ := bind_some.mp h
    obtain ⟨hb, rfl, rfl⟩ := ask_some.mp h1
    obtain ⟨bs, G2, u2, h2, k2⟩ := bind_some.mp k1
    obtain ⟨rfl, rfl, hbs⟩ := mapM_shown_list first l h2
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k2
    have hb' : F.shown (first + i) = some b := hb
    refine ⟨rfl, rfl, ?_⟩
    simp [List.mapM_cons, hb', hbs]

/-- A run of shown values leaves ledger and tape as they are. -/
theorem shownRun_spec {first n : Nat} {F G : Fork} {t u : Tape} {a : Array E}
    (h : shownRun engFl first n F t = some (a, G, u)) :
    F = G ∧ t = u ∧ ((Array.range n).mapM fun i => F.shown (first + i)) = some a := by
  have h' : ((Array.range n).mapM fun i => Fl.shown (first + i)) F t = some (a, G, u) := h
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind] at h'
  obtain ⟨l, G1, u1, h1, k1⟩ := bind_some.mp h'
  obtain ⟨rfl, rfl, hl⟩ := mapM_shown_list first _ h1
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k1
  refine ⟨rfl, rfl, ?_⟩
  rw [Array.mapM_eq_mapM_toList, hl]
  rfl

/-- The start form is made without a step on the ledger or the tape. -/
theorem joinStart_quiet {v : Env} {H : Heard} {om : Array E} {F G : Fork} {t u : Tape} {C : Aff}
    (h : joinStart engFl v H om F t = some (C, G, u)) : F = G ∧ t = u := by
  unfold joinStart at h
  obtain ⟨_, A1, a1, c1, k1⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c1
  obtain ⟨_, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c2
  obtain ⟨_, A3, a3, c3, k3⟩ := bind_some.mp k2
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c3
  obtain ⟨_, A4, a4, c4, k4⟩ := bind_some.mp k3
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c4
  obtain ⟨_, A5, a5, c5, k5⟩ := bind_some.mp k4
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c5
  obtain ⟨_, A6, a6, c6, k6⟩ := bind_some.mp k5
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c6
  obtain ⟨_, rfl, rfl⟩ := pure_some.mp k6
  exact ⟨rfl, rfl⟩

/-! ### The batched sumcheck -/

/-- **Where the batched sumcheck returns, with the tape.** -/
theorem hearStack_tape {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    ∃ (x mu0 eps beta T : E) (rs : List FlatRound) (sentY : List E) (vals : Array E)
      (w1 wY wV : Nat) (C : Aff) (G1 : Fork) (ms : List Rnd) (y : Rnd) (p : Psc),
      t = ⟨some RoundName.batSigma.name, 0, 2, [], [x]⟩ ::
        ⟨some RoundName.pscEpsilon.name, 0, w1, [mu0], [eps]⟩ ::
        (rs ++ ⟨some RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
          ⟨some RoundName.pscValues.name, 0, wV, vals.toList, []⟩ :: u) ∧
      rs.length = lamS ∧
      (∀ r ∈ rs, r.name = some RoundName.pscRound.name ∧ r.nz = 0 ∧ r.drawn.length = 1) ∧
      joinStart engFl v H (powers x 2) F (t.drop 1) = some (C, F, t.drop 1) ∧
      F.publicPart C = some T ∧
      ms = msOf (plainWs lamS) rs ∧ y = (OnBytes.Psc.Weight.atZero 3, sentY, beta) ∧
      p = endP { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T),
                 start := C, started := true } ms y ∧
      ms.map (·.1) = plainWs lamS ∧
      (∀ m ∈ ms ++ [y], Held m.1) ∧ (∀ m ∈ ms ++ [y], m.2.1.length + 1 = m.1.d) ∧
      K.rs.toList = (ms.map (·.2.2)).reverse ∧
      K.sA0 = F.next + 1 + 2 * lamS + 2 ∧ K.sH1 = K.sA0 + 1 ∧
      K.sB0 = K.sH1 + (1 + P.y.LamM) ∧ K.sV = K.sB0 + 1 ∧
      vals.size = 2 + (1 + P.y.LamM) + NCLp ∧
      ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork).hideRun
        K.sA0 vals beta = some G1 ∧
      K.rowS = p.rowForm (mulE K.fin.As K.fin.Bs) {} ∧
      G1.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G := by
  unfold hearStack at h
  obtain ⟨om, F1, t1, h1, k1⟩ := bind_some.mp h
  obtain ⟨_, rfl, x, e1, rfl⟩ := batch_spec h1
  obtain ⟨tT, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c2
  obtain ⟨shownT, A3, a3, c3, k3⟩ := bind_some.mp k2
  obtain ⟨rfl, rfl, _⟩ := shownRun_spec c3
  obtain ⟨TS, A4, a4, c4, k4⟩ := bind_some.mp k3
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c4
  obtain ⟨pans, A5, a5, c5, k5⟩ := bind_some.mp k4
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c5
  obtain ⟨_, A6, a6, c6, k6⟩ := bind_some.mp k5
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c6
  obtain ⟨C, A7, a7, c7, k7⟩ := bind_some.mp k6
  obtain ⟨rfl, rfl⟩ := joinStart_quiet c7
  obtain ⟨p0, F8, t8, c8, k8⟩ := bind_some.mp k7
  obtain ⟨T, mu0, eps, w1, hT, rfl, rfl, e8⟩ := pscBegin_tape c8
  obtain ⟨st, F9, t9, c9, k9⟩ := bind_some.mp k8
  obtain ⟨rs, e9, hrs, hnames, a1, a2', a3', hstp, hstr, _, rfl⟩ :=
    plainRounds_tape (fun _ _ _ _ => rfl) c9
  obtain ⟨lam', rs', p'⟩ := st
  have hstp' : p' = runP _ (msOf (plainWs lamS) rs) := hstp
  subst hstp'
  obtain ⟨_, A10, a10, c10, k10⟩ := bind_some.mp k9
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c10
  obtain ⟨z, F11, t11, c11, k11⟩ := bind_some.mp k10
  obtain ⟨sA0, p2⟩ := z
  obtain ⟨hY, sentY, beta, vals, wY, wV, b1, b2, rfl, rfl, hG1, e11⟩ := pscEnds_tape c11
  obtain ⟨x1, A12, a12, c12, k12⟩ := bind_some.mp k11
  obtain ⟨rfl, rfl, _⟩ := shownRun_spec c12
  obtain ⟨x2, A13, a13, c13, k13⟩ := bind_some.mp k12
  obtain ⟨rfl, rfl, _⟩ := shownRun_spec c13
  obtain ⟨x3, A14, a14, c14, k14⟩ := bind_some.mp k13
  have c14' : Fl.shown _ _ _ = some (x3, A14, a14) := c14
  obtain ⟨_, rfl, rfl⟩ := ask_some.mp c14'
  obtain ⟨x4, A15, a15, c15, k15⟩ := bind_some.mp k14
  have c15' : Fl.shown _ _ _ = some (x4, A15, a15) := c15
  obtain ⟨_, rfl, rfl⟩ := ask_some.mp c15'
  obtain ⟨fin, A16, a16, c16, k16⟩ := bind_some.mp k15
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c16
  obtain ⟨z2, F17, t17, c17, k17⟩ := bind_some.mp k16
  obtain ⟨rowS, p3⟩ := z2
  have c17' : Fl.pscRow _ (mulE fin.As fin.Bs) {} F11 t11 = some ((rowS, p3), F17, t17) := c17
  obtain ⟨rfl, rfl, hG⟩ := pscRow_spec c17'
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k17
  have d1 : t.drop 1 = t1 := by rw [e1, drop_one']
  refine ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, F11, msOf (plainWs lamS) rs,
    (OnBytes.Psc.Weight.atZero (2 + 1), sentY, beta), _, ?_, hrs, hnames, ?_, hT, rfl, rfl, rfl,
    a1, ?_, ?_, hstr, rfl, rfl, rfl, rfl, b2, hG1, rfl, hG⟩
  · rw [e1, e8, e9, e11]
  · rw [d1]
    exact c7
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact a2' m hm
    · rw [List.mem_singleton] at hm
      rw [hm]
      exact hY
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact a3' m hm
    · rw [List.mem_singleton] at hm
      rw [hm]
      show sentY.length + 1 = 3
      omega

end OnBytes.Desc.First.K4
