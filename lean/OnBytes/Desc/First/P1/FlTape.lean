-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/FlTape.lean: the plain functions by which the layers' own rounds (K4) hear a
masked sumcheck (OnBytes/K/Kc/Flat.lean), taken apart where they return, WITH WHAT THE TAPE WAS.
Statements and proofs.

Why. FlSpec.lean says which record a function leaves, "for some" sent and drawn elements. It does
not say that these elements are the tape's. Here every statement of FlSpec.lean is walked again, and
the tape is written out round by round: each round's name, its number of elements drawn other than
0, what it sent and what was drawn. The letters of the record are the letters of the tape.

  `closeOne_some`, `emptyOn_some`: what the round was that is closed.
  `pscBegin_tape`, `pscRound_tape`, `roundIn_eq2_tape`, `pscEnds_tape`: the facts of the statement
    of the like name in FlSpec.lean, and the tape.
  `msOf`: the rounds of a sumcheck read off a tape: weight number i with what round number i sent
    and with the first element that it drew.
  `levelRounds_tape`, `levelIn_tape`: a layer of a product tree.

What is not shown. One direction: from a return. Nothing is said where a function refuses, and
nothing on when it returns. The number of batched rows of a round (the third word) is not tested by
these functions, so it stands under "there is". Nothing on soundness.
-/
import OnBytes.Desc.First.P1.FlSpec
import OnBytes.Desc.First.P1.BatchPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc

/-! ### The rounds that are closed -/

/-- A round in which one element is drawn is closed: what it was. -/
theorem closeOne_some {name : String} {nz : Nat} {t u : Tape} {x : E}
    (h : closeOne name nz t = some (x, u)) :
    ∃ w : Nat, t = ⟨some name, nz, w, [], [x]⟩ :: u := by
  unfold closeOne at h
  split at h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨c1, c2⟩ := hc
      injection h with e0
      injection e0 with e1 e2
      subst c1 c2 e1 e2
      exact ⟨_, rfl⟩
    · cases h
  · cases h

/-- A round in which nothing is drawn is closed: what it was. -/
theorem emptyOn_some {name : String} {t u : Tape} {a : Unit}
    (h : Fl.emptyOn name t = some (a, u)) :
    ∃ w : Nat, t = ⟨some name, 0, w, [], []⟩ :: u := by
  unfold Fl.emptyOn at h
  cases hc : closeN name 0 0 t with
  | none =>
    rw [hc] at h
    exact absurd h (by simp)
  | some y =>
    obtain ⟨d, u'⟩ := y
    rw [hc, Option.map_some] at h
    injection h with e0
    injection e0 with _ e2
    have e2' : u' = u := e2
    subst e2'
    obtain ⟨hl, w, ht⟩ := closeN_some hc
    cases d with
    | nil => exact ⟨w, ht⟩
    | cons b l => exact absurd hl (by simp)

/-! ### The sumcheck's functions -/

/-- The beginning: one round, in which the sum mu of the hiding polynomial is sent and eps is
drawn. -/
theorem pscBegin_tape {C : Aff} {F G : Fork} {t u : Tape} {p : Psc}
    (h : Fl.pscBegin C F t = some (p, G, u)) :
    ∃ (T mu eps : E) (w : Nat), F.publicPart C = some T ∧
      p = { target := T, first := F.next, eps := eps, claim := addE mu (mulE eps T), start := C,
            started := true } ∧
      G = { F with next := F.next + 1 } ∧
      t = ⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: u := by
  unfold Fl.pscBegin at h
  obtain ⟨T, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨hT, rfl, rfl⟩ := ask_some.mp h1
  obtain ⟨p0, G2, u2, h2, k2⟩ := bind_some.mp k1
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k2
  unfold Fl.pscBeginAt at h2
  obtain ⟨first, G3, u3, h3, k3⟩ := bind_some.mp h2
  obtain ⟨rfl, rfl, rfl⟩ := takeSlots_some.mp h3
  obtain ⟨mu, G4, u4, h4, k4⟩ := bind_some.mp k3
  obtain ⟨r4, rfl⟩ := onTape_some.mp h4
  obtain ⟨eps, G5, u5, h5, k5⟩ := bind_some.mp k4
  obtain ⟨r5, rfl⟩ := onTape_some.mp h5
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k5
  obtain ⟨w, hw⟩ := closeOne_some r5
  have e := (recv_some r4).1.trans (congrArg (putBack [mu]) hw)
  exact ⟨T, mu, eps, w, hT, rfl, rfl, e⟩

/-- One round that is closed under a name: what was sent and the challenge are the tape's. -/
theorem pscRound_tape {p p' : Psc} {w : OnBytes.Psc.Weight} {name : String} {nz : Nat}
    {F G : Fork} {t u : Tape} {r : E}
    (h : Fl.pscRound p w (closeOne name nz) F t = some ((r, p'), G, u)) :
    Held w ∧ ∃ (sent : List E) (k : Nat), sent.length + 1 = w.d ∧ p' = stepP p (w, sent, r) ∧
      G = { F with next := F.next + (w.d - 1) } ∧
      t = ⟨some name, nz, k, sent, [r]⟩ :: u := by
  unfold Fl.pscRound at h
  obtain ⟨_, G1, u1, h1, k6⟩ := bind_some.mp h
  obtain ⟨hb, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨sent, G2, u2, h2, k7⟩ := bind_some.mp k6
  obtain ⟨r2, rfl⟩ := onTape_some.mp h2
  obtain ⟨_, G3, u3, h3, k8⟩ := bind_some.mp k7
  obtain ⟨hs, rfl, rfl⟩ := must_some.mp h3
  obtain ⟨r', G4, u4, h4, k9⟩ := bind_some.mp k8
  obtain ⟨r4, rfl⟩ := onTape_some.mp h4
  obtain ⟨_, G5, u5, h5, k10⟩ := bind_some.mp k9
  obtain ⟨_, rfl, rfl⟩ := takeSlots_some.mp h5
  obtain ⟨he, rfl, rfl⟩ := pure_some.mp k10
  injection he with e1 e2
  subst e1
  rw [Bool.and_eq_true] at hb
  obtain ⟨k, hk⟩ := closeOne_some r4
  have e := (recvN_some r2).2.1.trans (congrArg (putBack sent.toList) hk)
  rw [putBack_cons, List.append_nil] at e
  refine ⟨hb, sent.toList, k, ?_, e2.symm, rfl, e⟩
  simpa using hs

theorem roundIn_eq2_tape {p p' : Psc} {z : E} {F G : Fork} {t u : Tape} {r : E}
    (h : Fl.roundIn .eq2 p z 0 F t = some ((r, p'), G, u)) :
    Held (OnBytes.Psc.Weight.equality z 3) ∧ ∃ (sent : List E) (k : Nat), sent.length = 2 ∧
      p' = stepP p (OnBytes.Psc.Weight.equality z 3, sent, r) ∧
      G = { F with next := F.next + 2 } ∧
      t = ⟨some Model.RoundName.pscRound.name, 0, k, sent, [r]⟩ :: u := by
  unfold Fl.roundIn at h
  obtain ⟨_, G1, u1, h1, k11⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨w, G2, u2, h2, k12⟩ := bind_some.mp k11
  obtain ⟨hw, rfl, rfl⟩ := need_some.mp h2
  have hw' : OnBytes.Psc.Weight.equality z 3 = w := Option.some.inj hw
  subst hw'
  obtain ⟨hh, sent, k, hl, hp, hG, ht⟩ := pscRound_tape k12
  have hl3 : sent.length + 1 = 3 := hl
  exact ⟨hh, sent, k, by omega, hp, hG, ht⟩

/-- The round in the further variable, then the round of the n end values, in which nothing is
drawn. -/
theorem pscEnds_tape {p p' : Psc} {dY n e : Nat} {F G : Fork} {t u : Tape}
    (h : Fl.pscEnds p dY n F t = some ((e, p'), G, u)) :
    Held (OnBytes.Psc.Weight.atZero (dY + 1)) ∧
      ∃ (sent : List E) (beta : E) (v : Array E) (k k' : Nat),
      sent.length = dY ∧ v.size = n ∧
      p' = { stepP p (OnBytes.Psc.Weight.atZero (dY + 1), sent, beta) with ended := true } ∧
      e = F.next + dY ∧
      ({ F with next := F.next + dY + n } : Fork).hideRun e v beta = some G ∧
      t = ⟨some Model.RoundName.pscY.name, 1, k, sent, [beta]⟩ ::
        ⟨some Model.RoundName.pscValues.name, 0, k', v.toList, []⟩ :: u := by
  unfold Fl.pscEnds at h
  obtain ⟨_, G1, u1, h1, k13⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨x, G2, u2, h2, k14⟩ := bind_some.mp k13
  obtain ⟨beta, q⟩ := x
  obtain ⟨hh, sent, k, hl, rfl, rfl, ht1⟩ := pscRound_tape h2
  obtain ⟨v, G3, u3, h3, k15⟩ := bind_some.mp k14
  obtain ⟨r3, rfl⟩ := onTape_some.mp h3
  obtain ⟨_, G4, u4, h4, k16⟩ := bind_some.mp k15
  obtain ⟨hv, rfl, rfl⟩ := must_some.mp h4
  obtain ⟨_, G5, u5, h5, k17⟩ := bind_some.mp k16
  obtain ⟨r5, rfl⟩ := onTape_some.mp h5
  obtain ⟨e', G6, u6, h6, k18⟩ := bind_some.mp k17
  obtain ⟨rfl, rfl, rfl⟩ := takeSlots_some.mp h6
  obtain ⟨_, G7, u7, h7, k19⟩ := bind_some.mp k18
  obtain ⟨hG, rfl⟩ := change_some.mp h7
  obtain ⟨he, rfl, rfl⟩ := pure_some.mp k19
  injection he with e1 e2
  have hlY : sent.length + 1 = dY + 1 := hl
  have hd1 : dY + 1 - 1 = dY := by omega
  obtain ⟨k', hk'⟩ := emptyOn_some r5
  have e3 := (recvN_some r3).2.1.trans (congrArg (putBack v.toList) hk')
  rw [putBack_cons, List.append_nil] at e3
  rw [e3] at ht1
  refine ⟨hh, sent, beta, v, k, k', by omega, by simpa using hv, e2.symm, ?_, ?_, ht1⟩
  · rw [← e1]
    show F.next + (dY + 1 - 1) = F.next + dY
    rw [hd1]
  · rw [← e1]
    have hG' : ({ F with next := F.next + (dY + 1 - 1) + n } : Fork).hideRun
        (F.next + (dY + 1 - 1)) v beta = some _ := hG
    rw [hd1] at hG'
    exact hG'

/-! ### The rounds of a sumcheck, read off a tape -/

/-- Weight number i with what round number i sent and with the first element that it drew (0 if it
drew none). As many rounds as there are weights, or as the tape has, whichever is fewer. -/
def msOf (ws : List OnBytes.Psc.Weight) (rs : List FlatRound) : List Rnd :=
  List.zipWith (fun w r => (w, r.sent, r.drawn.headD zeroE)) ws rs

theorem msOf_cons (w : OnBytes.Psc.Weight) (ws : List OnBytes.Psc.Weight) (r : FlatRound)
    (rs : List FlatRound) :
    msOf (w :: ws) (r :: rs) = (w, r.sent, r.drawn.headD zeroE) :: msOf ws rs := rfl

theorem msOf_nil (rs : List FlatRound) : msOf [] rs = [] := by
  simp [msOf]

theorem msOf_level_cons (mu : Nat) (rho : Array E) (v : Nat) (order : List Nat)
    (nm : Option String) (z k : Nat) (sent : List E) (c : E) (rs : List FlatRound) :
    msOf (levelWs mu rho (v :: order)) (⟨nm, z, k, sent, [c]⟩ :: rs) =
      (OnBytes.Psc.Weight.equality (rho.getD (mu - 1 - v) zeroE) 3, sent, c) ::
        msOf (levelWs mu rho order) rs := rfl

/-- Rounds behind the last weight's round are not read. -/
theorem msOf_append_same : ∀ (ws : List OnBytes.Psc.Weight) (rs more : List FlatRound),
    ws.length = rs.length → msOf ws (rs ++ more) = msOf ws rs
  | [], rs, more, _ => by rw [msOf_nil, msOf_nil]
  | _ :: _, [], _, h => by simp at h
  | w :: ws, r :: rs, more, h => by
    have h' : ws.length = rs.length := by simpa using h
    rw [List.cons_append, msOf_cons, msOf_cons, msOf_append_same ws rs more h']

/-- One weight more reads one round more. -/
theorem msOf_append_one : ∀ (ws : List OnBytes.Psc.Weight) (w' : OnBytes.Psc.Weight)
    (rs : List FlatRound) (r' : FlatRound) (more : List FlatRound), ws.length = rs.length →
    msOf (ws ++ [w']) (rs ++ r' :: more) = msOf ws rs ++ [(w', r'.sent, r'.drawn.headD zeroE)]
  | [], _, [], _, _, _ => by simp [msOf]
  | [], _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, [], _, _, h => by simp at h
  | w :: ws, w', r :: rs, r', more, h => by
    have h' : ws.length = rs.length := by simpa using h
    simp only [List.cons_append, msOf_cons]
    rw [msOf_append_one ws w' rs r' more h']

theorem msOf_append_lit (ws : List OnBytes.Psc.Weight) (w' : OnBytes.Psc.Weight)
    (rs : List FlatRound) (nm : Option String) (z k : Nat) (sent : List E) (c : E)
    (more : List FlatRound) (h : ws.length = rs.length) :
    msOf (ws ++ [w']) (rs ++ ⟨nm, z, k, sent, [c]⟩ :: more) = msOf ws rs ++ [(w', sent, c)] :=
  msOf_append_one ws w' rs ⟨nm, z, k, sent, [c]⟩ more h

/-! ### A layer of a product tree -/

/-- The rounds of a layer: as many rounds of the tape as the order has variables, each under the
name of a sumcheck's round, with one drawn element. The rounds of `levelRounds_spec` are these. The
program's test on the order's variables is kept. -/
theorem levelRounds_tape {mu : Nat} {rho : Array E} : ∀ {order : List Nat} {r r' : Array E}
    {p p' : Psc} {F G : Fork} {t u : Tape},
    Fl.levelRounds mu rho order r p F t = some ((r', p'), G, u) →
    ∃ rs : List FlatRound, t = rs ++ u ∧ rs.length = order.length ∧
      (∀ x ∈ rs, x.name = some Model.RoundName.pscRound.name ∧ x.nz = 0 ∧ x.drawn.length = 1) ∧
      (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) ∧
      (msOf (levelWs mu rho order) rs).map (·.1) = levelWs mu rho order ∧
      (∀ m ∈ msOf (levelWs mu rho order) rs, Held m.1) ∧
      (∀ m ∈ msOf (levelWs mu rho order) rs, m.2.1.length + 1 = m.1.d) ∧
      p' = runP p (msOf (levelWs mu rho order) rs) ∧
      r' = levelR mu order ((msOf (levelWs mu rho order) rs).map (·.2.2)) r ∧
      G = { F with next := F.next + 2 * order.length }
  | [], r, r', p, p', F, G, t, u, h => by
    unfold Fl.levelRounds at h
    obtain ⟨he, rfl, rfl⟩ := pure_some.mp h
    injection he with e1 e2
    have e0 : msOf (levelWs mu rho []) [] = [] := rfl
    refine ⟨[], rfl, rfl, by simp, by simp, ?_⟩
    rw [e0]
    exact ⟨rfl, by simp, by simp, e2.symm, e1.symm, rfl⟩
  | v :: order, r, r', p, p', F, G, t, u, h => by
    unfold Fl.levelRounds at h
    obtain ⟨_, G1, u1, h1, k22⟩ := bind_some.mp h
    obtain ⟨hb, rfl, rfl⟩ := must_some.mp h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨x, G2, u2, h2, k23⟩ := bind_some.mp k22
    obtain ⟨c, q⟩ := x
    obtain ⟨hh, sent, k, hl, rfl, rfl, ht⟩ := roundIn_eq2_tape h2
    obtain ⟨rs, b0, b1, b2, b3, a1, a2, a3, a4, a5, a6⟩ := levelRounds_tape k23
    have et := ht.trans (congrArg
      (List.cons (⟨some Model.RoundName.pscRound.name, 0, k, sent, [c]⟩ : FlatRound)) b0)
    refine ⟨⟨some Model.RoundName.pscRound.name, 0, k, sent, [c]⟩ :: rs, et, ?_, ?_, ?_, ?_⟩
    · rw [List.length_cons, List.length_cons, b1]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨rfl, rfl, rfl⟩
      · exact b2 x hx
    · intro v' hv'
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact hb
      · exact b3 v' hv'
    rw [msOf_level_cons]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.map_cons, a1]
      rfl
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hh
      · exact a2 m hm
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · show sent.length + 1 = 3
        omega
      · exact a3 m hm
    · rw [runP_cons]
      exact a4
    · rw [List.map_cons, levelR_cons]
      exact a5
    · rw [a6]
      show ({ F with next := F.next + 2 + 2 * order.length } : Fork) = _
      have : F.next + 2 + 2 * order.length = F.next + 2 * (v :: order).length := by
        rw [List.length_cons]
        omega
      rw [this]

/-- **Where a layer returns, with the tape.** The tape begins with mu + 4 rounds: the beginning (mu0
sent, eps drawn), the mu rounds rs of the variables, the round of the further variable (beta drawn,
by the rule that never gives 0), the round of the two end values v (nothing drawn), and the round in
which the point tau on the line is drawn. The rounds ms and y, of which all facts of
`levelIn_spec` are said, are these, and the record p is the one behind them. -/
theorem levelIn_tape {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    order.length = mu ∧ ∃ (T mu0 eps : E) (rs : List FlatRound) (sentY : List E) (beta tau : E)
      (w0 wY wV wT : Nat) (ms : List Rnd) (y : Rnd) (shL shR : E) (v : Array E)
      (G1 : Fork) (p : Psc),
      t = ⟨some Model.RoundName.pscEpsilon.name, 0, w0, [mu0], [eps]⟩ ::
        (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
          ⟨some Model.RoundName.pscValues.name, 0, wV, v.toList, []⟩ ::
          ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u) ∧
      rs.length = mu ∧
      (∀ x ∈ rs, x.name = some Model.RoundName.pscRound.name ∧ x.nz = 0 ∧ x.drawn.length = 1) ∧
      (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) ∧
      L.tau = tau ∧
      ms = msOf (levelWs mu rho order) rs ∧ y = (OnBytes.Psc.Weight.atZero 3, sentY, beta) ∧
      p = endP { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T),
                 start := C, started := true } ms y ∧
      F.publicPart C = some T ∧
      ms.map (·.1) = levelWs mu rho order ∧ y.1 = OnBytes.Psc.Weight.atZero 3 ∧
      (∀ m ∈ ms ++ [y], Held m.1) ∧ (∀ m ∈ ms ++ [y], m.2.1.length + 1 = m.1.d) ∧
      p.vars.toList = levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3] ∧
      p.r.toList = (ms ++ [y]).map (·.2.2) ∧
      p.claim = claimAfter (ms ++ [y]) (addE mu0 (mulE eps T)) ∧
      p.target = T ∧ p.eps = eps ∧ p.start = C ∧ p.first = F.next ∧
      L.row = p.rowForm (mulE shL shR) {} ∧ L.r = levelR mu order (ms.map (·.2.2))
        (Array.replicate mu zeroE) ∧
      L.sL = F.next + 1 + 2 * mu + 2 ∧ L.sR = L.sL + 1 ∧ v.size = 2 ∧
      ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork).hideRun L.sL v y.2.2 = some G1 ∧
      G1.shown L.sL = some shL ∧ G1.shown (L.sL + 1) = some shR ∧
      G1.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G := by
  unfold Fl.levelIn at h
  obtain ⟨_, G0, u0, h0, k24⟩ := bind_some.mp h
  obtain ⟨ho, rfl, rfl⟩ := must_some.mp h0
  have hom : order.length = mu := by simpa using ho
  obtain ⟨p0, G1, u1, h1, k25⟩ := bind_some.mp k24
  obtain ⟨T, mu0, eps, w0, hT, rfl, rfl, ht0⟩ := pscBegin_tape h1
  obtain ⟨x, G2, u2, h2, k26⟩ := bind_some.mp k25
  obtain ⟨r, p1⟩ := x
  obtain ⟨rs, c0, c1, c2, c3, a1, a2, a3, rfl, rfl, rfl⟩ := levelRounds_tape h2
  obtain ⟨x, G3, u3, h3, k27⟩ := bind_some.mp k26
  obtain ⟨sL, p2⟩ := x
  obtain ⟨hY, sentY, beta, v, wY, wV, b1, b2, rfl, rfl, hG3, ht3⟩ := pscEnds_tape h3
  obtain ⟨tau, G4, u4, h4, k28⟩ := bind_some.mp k27
  obtain ⟨r4, rfl⟩ := onTape_some.mp h4
  obtain ⟨wT, hk⟩ := closeOne_some r4
  obtain ⟨shL, G5, u5, h5, k29⟩ := bind_some.mp k28
  obtain ⟨hL, rfl, rfl⟩ := ask_some.mp h5
  obtain ⟨shR, G6, u6, h6, k30⟩ := bind_some.mp k29
  obtain ⟨hR, rfl, rfl⟩ := ask_some.mp h6
  obtain ⟨x, G7, u7, h7, k31⟩ := bind_some.mp k30
  obtain ⟨row, p3⟩ := x
  obtain ⟨rfl, rfl, hG7⟩ := pscRow_spec h7
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k31
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := endP_spec
    { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true } (msOf (levelWs mu rho order) rs)
    (OnBytes.Psc.Weight.atZero (2 + 1), sentY, beta)
  refine ⟨hom, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT,
    msOf (levelWs mu rho order) rs, (OnBytes.Psc.Weight.atZero (2 + 1), sentY, beta), shL, shR, v,
    G3, _, ?_, c1.trans hom, c2, c3, rfl, rfl, rfl, rfl, hT, a1, rfl, ?_, ?_, ?_, e2, e3, e5, e6,
    e4, e7, rfl, rfl, ?_, rfl, b2, ?_, hL, hR, hG7⟩
  · rw [ht0, c0, ht3, hk]
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact a2 m hm
    · rw [List.mem_singleton] at hm
      rw [hm]
      exact hY
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact a3 m hm
    · rw [List.mem_singleton] at hm
      rw [hm]
      show sentY.length + 1 = 3
      omega
  · rw [e1, List.map_append, a1]
    rfl
  · show F.next + 1 + 2 * order.length + 2 = F.next + 1 + 2 * mu + 2
    rw [hom]
  · rw [← hom]
    exact hG3

end OnBytes.Desc.First.P1
