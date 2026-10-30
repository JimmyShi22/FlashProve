-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/FlSpec.lean: the plain functions on a ledger and a tape by which the layers'
own
rounds (K4) hear a masked sumcheck (OnBytes/K/Kc/Flat.lean: `Fl.pscBegin`, `pscRound`, `roundIn`,
`pscEnds`, `pscRow`, `levelRounds`, `levelIn`), TAKEN APART WHERE THEY RETURN: which record they
leave,
of which rounds, under which slots, and what they do to the ledger. Statements and proofs.

  `bind_some` and its kin: a function of this kind returns exactly if its steps do, one after the
  other.
  `stepP`, `runP`: the record behind a round; behind rounds. `runP_claim` ...: its fields.
  `pscBegin_spec`, `pscRound_spec`, `roundIn_eq2_spec`, `pscEnds_spec`, `pscRow_spec`.
  `levelRounds_spec`, `levelIn_spec`: a layer of a product tree.

One direction: from a return. Nothing is said where a function refuses. No routine of the program
`verify-on-bytes` is named: these are functions Fork → Tape → Option.
-/
import OnBytes.Desc.First.P1.PscSound
import OnBytes.K.Kc.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc

variable {α β : Type}

/-! ### The steps

Every equation has what a step returns on its RIGHT side, so that a substitution removes the
returned
letter and keeps the letter that was handed in. -/

theorem some_triple {a b : α} {F G : Fork} {t u : Tape} :
    (some (a, F, t) : Option (α × Fork × Tape)) = some (b, G, u) ↔ a = b ∧ F = G ∧ t = u := by
  constructor
  · intro h
    injection h with h
    injection h with h1 h2
    injection h2 with h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem bind_some {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape} {r : β × Fork × Tape} :
    (x >>= f) F t = some r ↔ ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some r := by
  show Fl.andThen x f F t = some r ↔ _
  unfold Fl.andThen
  cases h : x F t with
  | none => simp
  | some y =>
    obtain ⟨a, G, u⟩ := y
    constructor
    · intro h'
      exact ⟨a, G, u, rfl, h'⟩
    · rintro ⟨a', G', u', e, h'⟩
      obtain ⟨rfl, rfl, rfl⟩ := some_triple.mp e
      exact h'

theorem pure_some {a b : α} {F G : Fork} {t u : Tape} :
    (pure a : Fl α) F t = some (b, G, u) ↔ a = b ∧ F = G ∧ t = u := some_triple

theorem must_some {b : Bool} {a : Unit} {F G : Fork} {t u : Tape} :
    Fl.must b F t = some (a, G, u) ↔ b = true ∧ F = G ∧ t = u := by
  unfold Fl.must
  cases b with
  | false => simp
  | true =>
    rw [if_pos rfl, some_triple]
    simp

theorem need_some {x : Option α} {a : α} {F G : Fork} {t u : Tape} :
    Fl.need x F t = some (a, G, u) ↔ x = some a ∧ F = G ∧ t = u := by
  unfold Fl.need
  cases x with
  | none => simp
  | some y =>
    rw [Option.map_some, some_triple]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h⟩
    · rintro ⟨h1, h⟩
      exact ⟨Option.some.inj h1, h⟩

theorem ask_some {f : Fork → Option α} {a : α} {F G : Fork} {t u : Tape} :
    Fl.ask f F t = some (a, G, u) ↔ f F = some a ∧ F = G ∧ t = u := by
  unfold Fl.ask
  cases f F with
  | none => simp
  | some y =>
    rw [Option.map_some, some_triple]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h⟩
    · rintro ⟨h1, h⟩
      exact ⟨Option.some.inj h1, h⟩

theorem change_some {f : Fork → Option Fork} {a : Unit} {F G : Fork} {t u : Tape} :
    Fl.change f F t = some (a, G, u) ↔ f F = some G ∧ t = u := by
  unfold Fl.change
  cases f F with
  | none => simp
  | some y =>
    rw [Option.map_some, some_triple]
    constructor
    · rintro ⟨_, rfl, h⟩
      exact ⟨rfl, h⟩
    · rintro ⟨h1, h⟩
      exact ⟨rfl, Option.some.inj h1, h⟩

theorem onTape_some {g : Tape → Option (α × Tape)} {a : α} {F G : Fork} {t u : Tape} :
    Fl.onTape g F t = some (a, G, u) ↔ g t = some (a, u) ∧ F = G := by
  unfold Fl.onTape
  cases g t with
  | none => simp
  | some y =>
    obtain ⟨y1, y2⟩ := y
    rw [Option.map_some, some_triple]
    constructor
    · rintro ⟨rfl, h, rfl⟩
      exact ⟨rfl, h⟩
    · rintro ⟨h1, h⟩
      injection h1 with h1
      injection h1 with h1 h2
      exact ⟨h1, h, h2⟩

theorem takeSlots_some {n a : Nat} {F G : Fork} {t u : Tape} :
    Fl.takeSlots n F t = some (a, G, u) ↔
      F.next = a ∧ { F with next := F.next + n } = G ∧ t = u := some_triple

/-! ### The record behind rounds -/

/-- The record behind one round. -/
def stepP (p : Psc) (m : Rnd) : Psc :=
  { p with
    claim := OnBytes.Psc.polyAt (m.1.complete m.2.1 p.claim) m.2.2
    vars := p.vars.push m.1
    r := p.r.push m.2.2 }

/-- The record behind rounds. -/
def runP : Psc → List Rnd → Psc
  | p, [] => p
  | p, m :: ms => runP (stepP p m) ms

theorem runP_cons (p : Psc) (m : Rnd) (ms : List Rnd) : runP p (m :: ms) = runP (stepP p m) ms :=
  rfl

theorem runP_append (p : Psc) : ∀ (a b : List Rnd), runP p (a ++ b) = runP (runP p a) b := by
  intro a
  induction a generalizing p with
  | nil => intro b; rfl
  | cons m a ih => intro b; exact ih (stepP p m) b

theorem runP_claim : ∀ (ms : List Rnd) (p : Psc), (runP p ms).claim = claimAfter ms p.claim
  | [], _ => rfl
  | m :: ms, p => runP_claim ms (stepP p m)

theorem runP_vars : ∀ (ms : List Rnd) (p : Psc),
    (runP p ms).vars.toList = p.vars.toList ++ ms.map (·.1)
  | [], p => by simp [runP]
  | m :: ms, p => by
    rw [runP, runP_vars ms]
    simp [stepP]

theorem runP_r : ∀ (ms : List Rnd) (p : Psc),
    (runP p ms).r.toList = p.r.toList ++ ms.map (·.2.2)
  | [], p => by simp [runP]
  | m :: ms, p => by
    rw [runP, runP_r ms]
    simp [stepP]

/-- What rounds leave as it was. -/
theorem runP_same : ∀ (ms : List Rnd) (p : Psc),
    (runP p ms).start = p.start ∧ (runP p ms).target = p.target ∧ (runP p ms).eps = p.eps ∧
      (runP p ms).first = p.first
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | m :: ms, p => runP_same ms (stepP p m)

/-- The record behind the variables' rounds ms and the further variable's round y. -/
def endP (p : Psc) (ms : List Rnd) (y : Rnd) : Psc := { stepP (runP p ms) y with ended := true }

theorem endP_spec (p : Psc) (ms : List Rnd) (y : Rnd) :
    (endP p ms y).vars.toList = p.vars.toList ++ (ms ++ [y]).map (·.1) ∧
      (endP p ms y).r.toList = p.r.toList ++ (ms ++ [y]).map (·.2.2) ∧
      (endP p ms y).claim = claimAfter (ms ++ [y]) p.claim ∧
      (endP p ms y).start = p.start ∧ (endP p ms y).target = p.target ∧
      (endP p ms y).eps = p.eps ∧ (endP p ms y).first = p.first := by
  have hrun : stepP (runP p ms) y = runP p (ms ++ [y]) := by
    rw [runP_append]
    rfl
  obtain ⟨s1, s2, s3, s4⟩ := runP_same (ms ++ [y]) p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (stepP (runP p ms) y).vars.toList = _
    rw [hrun, runP_vars]
  · show (stepP (runP p ms) y).r.toList = _
    rw [hrun, runP_r]
  · show (stepP (runP p ms) y).claim = _
    rw [hrun, runP_claim]
  · show (stepP (runP p ms) y).start = _
    rw [hrun, s1]
  · show (stepP (runP p ms) y).target = _
    rw [hrun, s2]
  · show (stepP (runP p ms) y).eps = _
    rw [hrun, s3]
  · show (stepP (runP p ms) y).first = _
    rw [hrun, s4]

/-! ### The sumcheck's functions -/

theorem pscBegin_spec {C : Aff} {F G : Fork} {t u : Tape} {p : Psc}
    (h : Fl.pscBegin C F t = some (p, G, u)) :
    ∃ T mu eps, F.publicPart C = some T ∧
      p = { target := T, first := F.next, eps := eps, claim := addE mu (mulE eps T), start := C,
            started := true } ∧
      G = { F with next := F.next + 1 } := by
  unfold Fl.pscBegin at h
  obtain ⟨T, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨hT, rfl, rfl⟩ := ask_some.mp h1
  obtain ⟨p0, G2, u2, h2, k2⟩ := bind_some.mp k1
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k2
  unfold Fl.pscBeginAt at h2
  obtain ⟨first, G3, u3, h3, k3⟩ := bind_some.mp h2
  obtain ⟨rfl, rfl, rfl⟩ := takeSlots_some.mp h3
  obtain ⟨mu, G4, u4, h4, k4⟩ := bind_some.mp k3
  obtain ⟨_, rfl⟩ := onTape_some.mp h4
  obtain ⟨eps, G5, u5, h5, k5⟩ := bind_some.mp k4
  obtain ⟨_, rfl⟩ := onTape_some.mp h5
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k5
  exact ⟨T, mu, eps, hT, rfl, rfl⟩

theorem pscRound_spec {p p' : Psc} {w : OnBytes.Psc.Weight} {draw : Tape → Option (E × Tape)}
    {F G : Fork} {t u : Tape} {r : E} (h : Fl.pscRound p w draw F t = some ((r, p'), G, u)) :
    Held w ∧ ∃ sent : List E, sent.length + 1 = w.d ∧ p' = stepP p (w, sent, r) ∧
      G = { F with next := F.next + (w.d - 1) } := by
  unfold Fl.pscRound at h
  obtain ⟨_, G1, u1, h1, k6⟩ := bind_some.mp h
  obtain ⟨hb, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨sent, G2, u2, h2, k7⟩ := bind_some.mp k6
  obtain ⟨_, rfl⟩ := onTape_some.mp h2
  obtain ⟨_, G3, u3, h3, k8⟩ := bind_some.mp k7
  obtain ⟨hs, rfl, rfl⟩ := must_some.mp h3
  obtain ⟨r', G4, u4, h4, k9⟩ := bind_some.mp k8
  obtain ⟨_, rfl⟩ := onTape_some.mp h4
  obtain ⟨_, G5, u5, h5, k10⟩ := bind_some.mp k9
  obtain ⟨_, rfl, rfl⟩ := takeSlots_some.mp h5
  obtain ⟨he, rfl, rfl⟩ := pure_some.mp k10
  injection he with e1 e2
  subst e1
  rw [Bool.and_eq_true] at hb
  refine ⟨hb, sent.toList, ?_, e2.symm, rfl⟩
  simpa using hs

theorem roundIn_eq2_spec {p p' : Psc} {z : E} {F G : Fork} {t u : Tape} {r : E}
    (h : Fl.roundIn .eq2 p z 0 F t = some ((r, p'), G, u)) :
    Held (OnBytes.Psc.Weight.equality z 3) ∧ ∃ sent : List E, sent.length = 2 ∧
      p' = stepP p (OnBytes.Psc.Weight.equality z 3, sent, r) ∧
      G = { F with next := F.next + 2 } := by
  unfold Fl.roundIn at h
  obtain ⟨_, G1, u1, h1, k11⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨w, G2, u2, h2, k12⟩ := bind_some.mp k11
  obtain ⟨hw, rfl, rfl⟩ := need_some.mp h2
  have hw' : OnBytes.Psc.Weight.equality z 3 = w := Option.some.inj hw
  subst hw'
  obtain ⟨hh, sent, hl, hp, hG⟩ := pscRound_spec k12
  have hl3 : sent.length + 1 = 3 := hl
  exact ⟨hh, sent, by omega, hp, hG⟩

theorem pscEnds_spec {p p' : Psc} {dY n e : Nat} {F G : Fork} {t u : Tape}
    (h : Fl.pscEnds p dY n F t = some ((e, p'), G, u)) :
    Held (OnBytes.Psc.Weight.atZero (dY + 1)) ∧ ∃ (sent : List E) (beta : E) (v : Array E),
      sent.length = dY ∧ v.size = n ∧
      p' = { stepP p (OnBytes.Psc.Weight.atZero (dY + 1), sent, beta) with ended := true } ∧
      e = F.next + dY ∧
      ({ F with next := F.next + dY + n } : Fork).hideRun e v beta = some G := by
  unfold Fl.pscEnds at h
  obtain ⟨_, G1, u1, h1, k13⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨x, G2, u2, h2, k14⟩ := bind_some.mp k13
  obtain ⟨beta, q⟩ := x
  obtain ⟨hh, sent, hl, rfl, rfl⟩ := pscRound_spec h2
  obtain ⟨v, G3, u3, h3, k15⟩ := bind_some.mp k14
  obtain ⟨_, rfl⟩ := onTape_some.mp h3
  obtain ⟨_, G4, u4, h4, k16⟩ := bind_some.mp k15
  obtain ⟨hv, rfl, rfl⟩ := must_some.mp h4
  obtain ⟨_, G5, u5, h5, k17⟩ := bind_some.mp k16
  obtain ⟨_, rfl⟩ := onTape_some.mp h5
  obtain ⟨e', G6, u6, h6, k18⟩ := bind_some.mp k17
  obtain ⟨rfl, rfl, rfl⟩ := takeSlots_some.mp h6
  obtain ⟨_, G7, u7, h7, k19⟩ := bind_some.mp k18
  obtain ⟨hG, rfl⟩ := change_some.mp h7
  obtain ⟨he, rfl, rfl⟩ := pure_some.mp k19
  injection he with e1 e2
  have hlY : sent.length + 1 = dY + 1 := hl
  have hd1 : dY + 1 - 1 = dY := by omega
  refine ⟨hh, sent, beta, v, by omega, by simpa using hv, e2.symm, ?_, ?_⟩
  · rw [← e1]
    show F.next + (dY + 1 - 1) = F.next + dY
    rw [hd1]
  · rw [← e1]
    have hG' : ({ F with next := F.next + (dY + 1 - 1) + n } : Fork).hideRun
        (F.next + (dY + 1 - 1)) v beta = some _ := hG
    rw [hd1] at hG'
    exact hG'

theorem pscRow_spec {p p' : Psc} {S0 : E} {kept f : Aff} {F G : Fork} {t u : Tape}
    (h : Fl.pscRow p S0 kept F t = some ((f, p'), G, u)) :
    f = p.rowForm S0 kept ∧ u = t ∧
      F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G := by
  unfold Fl.pscRow at h
  obtain ⟨_, G1, u1, h1, k20⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨_, G2, u2, h2, k21⟩ := bind_some.mp k20
  obtain ⟨hG, rfl⟩ := change_some.mp h2
  obtain ⟨he, rfl, rfl⟩ := pure_some.mp k21
  injection he with e1 e2
  exact ⟨e1.symm, rfl, hG⟩

/-! ### A layer of a product tree -/

/-- The weights of a layer's rounds, in the order of the rounds. -/
def levelWs (mu : Nat) (rho : Array E) (order : List Nat) : List OnBytes.Psc.Weight :=
  order.map fun v => OnBytes.Psc.Weight.equality (rho.getD (mu - 1 - v) zeroE) 3

/-- The challenges laid at their variables' places. -/
def levelR (mu : Nat) : List Nat → List E → Array E → Array E
  | v :: order, x :: xs, r => levelR mu order xs (r.set! (mu - 1 - v) x)
  | _, _, r => r

theorem levelR_cons (mu v : Nat) (order : List Nat) (x : E) (xs : List E) (r : Array E) :
    levelR mu (v :: order) (x :: xs) r = levelR mu order xs (r.set! (mu - 1 - v) x) := rfl

theorem levelRounds_spec {mu : Nat} {rho : Array E} : ∀ {order : List Nat} {r r' : Array E}
    {p p' : Psc} {F G : Fork} {t u : Tape},
    Fl.levelRounds mu rho order r p F t = some ((r', p'), G, u) →
    ∃ ms : List Rnd, ms.map (·.1) = levelWs mu rho order ∧ (∀ m ∈ ms, Held m.1) ∧
      (∀ m ∈ ms, m.2.1.length + 1 = m.1.d) ∧ p' = runP p ms ∧
      r' = levelR mu order (ms.map (·.2.2)) r ∧ G = { F with next := F.next + 2 * order.length }
  | [], r, r', p, p', F, G, t, u, h => by
    unfold Fl.levelRounds at h
    obtain ⟨he, rfl, rfl⟩ := pure_some.mp h
    injection he with e1 e2
    exact ⟨[], rfl, by simp, by simp, e2.symm, e1.symm, rfl⟩
  | v :: order, r, r', p, p', F, G, t, u, h => by
    unfold Fl.levelRounds at h
    obtain ⟨_, G1, u1, h1, k22⟩ := bind_some.mp h
    obtain ⟨_, rfl, rfl⟩ := must_some.mp h1
    obtain ⟨x, G2, u2, h2, k23⟩ := bind_some.mp k22
    obtain ⟨c, q⟩ := x
    obtain ⟨hh, sent, hl, rfl, rfl⟩ := roundIn_eq2_spec h2
    obtain ⟨ms, a1, a2, a3, a4, a5, a6⟩ := levelRounds_spec k23
    refine ⟨(OnBytes.Psc.Weight.equality (rho.getD (mu - 1 - v) zeroE) 3, sent, c) :: ms,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- **Where a layer returns.** -/
theorem levelIn_spec {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    order.length = mu ∧ ∃ (T mu0 eps : E) (ms : List Rnd) (y : Rnd) (shL shR : E) (v : Array E)
      (G1 : Fork) (p : Psc),
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
  obtain ⟨T, mu0, eps, hT, rfl, rfl⟩ := pscBegin_spec h1
  obtain ⟨x, G2, u2, h2, k26⟩ := bind_some.mp k25
  obtain ⟨r, p1⟩ := x
  obtain ⟨ms, a1, a2, a3, rfl, rfl, rfl⟩ := levelRounds_spec h2
  obtain ⟨x, G3, u3, h3, k27⟩ := bind_some.mp k26
  obtain ⟨sL, p2⟩ := x
  obtain ⟨hY, sentY, beta, v, b1, b2, rfl, rfl, hG3⟩ := pscEnds_spec h3
  obtain ⟨tau, G4, u4, h4, k28⟩ := bind_some.mp k27
  obtain ⟨_, rfl⟩ := onTape_some.mp h4
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
      started := true } ms (OnBytes.Psc.Weight.atZero (2 + 1), sentY, beta)
  refine ⟨hom, T, mu0, eps, ms, (OnBytes.Psc.Weight.atZero (2 + 1), sentY, beta), shL, shR, v, G3,
    _, hT, a1, rfl, ?_, ?_, ?_, e2, e3, e5, e6, e4, e7, rfl, rfl, ?_, rfl, b2, ?_, hL, hR, hG7⟩
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
