-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/TscKit.lean: what the law of a token sumcheck (TscLaw.lean) uses: the plain
functions `Fl.claimsIn`, `Fl.tscLoop`, `Fl.tscIn` (OnBytes/K/Kc/Flat.lean) taken apart where they
return, and the weights of the rounds. Definitions, statements and proofs.

  `claimsIn_ledger`, `tscLoop_spec`, `tscIn_spec`: which record a function leaves and what it does
    to the ledger, "for some" sent and drawn elements. That these are the tape's is said in
    BatchPoint.lean (`claimsIn_spec`) and TscLaw.lean (`tscLoop_tape`, `tscIn_tape`).
  `tscWs`, `tscXs`, `twos_tsc`, `held_tsc`: the weights of a token sumcheck's rounds.
  `publicPart_slot`: the public part of a slot's form reads as what was shown.

It holds no law. One direction: from a return.
-/
import OnBytes.Desc.First.P1.LevelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc Polynomial
open OnBytes.PscRun (Sized Filled hideRun_ok)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### The functions, taken apart -/

theorem claimsIn_ledger {n j : Nat} {F G : Fork} {t u : Tape}
    (h : Fl.claimsIn n F t = some (j, G, u)) :
    j = F.next ∧ ∃ v : Array E, v.size = n ∧
      ({ F with next := F.next + n } : Fork).hideRun F.next v oneE = some G := by
  unfold Fl.claimsIn at h
  obtain ⟨v, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨_, rfl⟩ := onTape_some.mp h1
  obtain ⟨_, G2, u2, h2, k2⟩ := bind_some.mp k1
  obtain ⟨hv, rfl, rfl⟩ := must_some.mp h2
  obtain ⟨j', G3, u3, h3, k3⟩ := bind_some.mp k2
  obtain ⟨rfl, rfl, rfl⟩ := takeSlots_some.mp h3
  obtain ⟨_, G4, u4, h4, k4⟩ := bind_some.mp k3
  obtain ⟨hG, rfl⟩ := change_some.mp h4
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k4
  exact ⟨rfl, v, by simpa using hv, hG⟩

/-- The weights of a token sumcheck's rounds. -/
def tscWs (zs : List E) : List OnBytes.Psc.Weight := zs.map fun z => OnBytes.Psc.Weight.equality z 3

theorem tscLoop_spec : ∀ {zs : List E} {r r' : Array E} {p p' : Psc} {F G : Fork} {t u : Tape},
    Fl.tscLoop zs r p F t = some ((r', p'), G, u) →
    ∃ ms : List Rnd, ms.map (·.1) = tscWs zs ∧ (∀ m ∈ ms, Held m.1) ∧
      (∀ m ∈ ms, m.2.1.length + 1 = m.1.d) ∧ p' = runP p ms ∧
      r'.toList = r.toList ++ ms.map (·.2.2) ∧ G = { F with next := F.next + 2 * zs.length }
  | [], r, r', p, p', F, G, t, u, h => by
    unfold Fl.tscLoop at h
    obtain ⟨he, rfl, rfl⟩ := pure_some.mp h
    injection he with e1 e2
    exact ⟨[], rfl, by simp, by simp, e2.symm, by simp [e1], rfl⟩
  | z :: zs, r, r', p, p', F, G, t, u, h => by
    unfold Fl.tscLoop at h
    obtain ⟨x, G2, u2, h2, k1⟩ := bind_some.mp h
    obtain ⟨c, q⟩ := x
    obtain ⟨hh, sent, hl, rfl, rfl⟩ := roundIn_eq2_spec h2
    obtain ⟨ms, a1, a2, a3, a4, a5, a6⟩ := tscLoop_spec k1
    refine ⟨(OnBytes.Psc.Weight.equality z 3, sent, c) :: ms, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · rw [a5, List.map_cons]
      simp
    · rw [a6]
      show ({ F with next := F.next + 2 + 2 * zs.length } : Fork) = _
      have : F.next + 2 + 2 * zs.length = F.next + 2 * (z :: zs).length := by
        rw [List.length_cons]
        omega
      rw [this]

/-- **Where a token sumcheck returns.** -/
theorem tscIn_spec {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    lt ≤ P.size ∧ ∃ (T mu0 eps : E) (ms : List Rnd) (y : Rnd) (v1 v : Array E) (G0 : Fork),
      o.sCl = F.next ∧ v1.size = 1 ∧
      ({ F with next := F.next + 1 } : Fork).hideRun F.next v1 oneE = some G0 ∧
      G0.publicPart (Aff.slot F.next) = some T ∧
      ms.map (·.1) = tscWs (P.toList.take lt) ∧ y.1 = OnBytes.Psc.Weight.atZero (dY + 1) ∧
      (∀ m ∈ ms ++ [y], Held m.1) ∧ (∀ m ∈ ms ++ [y], m.2.1.length + 1 = m.1.d) ∧
      o.p.vars.toList = tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero (dY + 1)] ∧
      o.p.r.toList = (ms ++ [y]).map (·.2.2) ∧
      o.p.claim = claimAfter (ms ++ [y]) (addE mu0 (mulE eps T)) ∧
      o.p.target = T ∧ o.p.eps = eps ∧ o.p.start = Aff.slot F.next ∧ o.p.first = G0.next ∧
      o.r.toList = ms.map (·.2.2) ∧
      o.sEnd = G0.next + 1 + 2 * (P.toList.take lt).length + dY ∧ v.size = n ∧
      ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork).hideRun
        o.sEnd v y.2.2 = some G := by
  unfold Fl.tscIn at h
  obtain ⟨o1, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨x, G2, u2, h2, k2⟩ := bind_some.mp k1
  obtain ⟨sEnd, p2⟩ := x
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k2
  unfold Fl.tscRounds at h1
  obtain ⟨_, G3, u3, h3, k3⟩ := bind_some.mp h1
  obtain ⟨hlt, rfl, rfl⟩ := must_some.mp h3
  obtain ⟨sCl, G4, u4, h4, k4⟩ := bind_some.mp k3
  obtain ⟨rfl, v1, hv1, hG0⟩ := claimsIn_ledger h4
  obtain ⟨p0, G5, u5, h5, k5⟩ := bind_some.mp k4
  obtain ⟨T, mu0, eps, hT, rfl, rfl⟩ := pscBegin_spec h5
  obtain ⟨x, G6, u6, h6, k6⟩ := bind_some.mp k5
  obtain ⟨r, p1⟩ := x
  obtain ⟨ms, a1, a2, a3, rfl, a5, rfl⟩ := tscLoop_spec h6
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k6
  obtain ⟨hY, sentY, beta, v, b1, b2, rfl, rfl, hG⟩ := pscEnds_spec h2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := endP_spec
    { target := T, first := G4.next, eps := eps, claim := addE mu0 (mulE eps T),
      start := Aff.slot F.next, started := true } ms
    (OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta)
  refine ⟨by simpa using hlt, T, mu0, eps, ms, (OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta),
    v1, v, G4, rfl, hv1, hG0, hT, a1, rfl, ?_, ?_, ?_, e2, e3, e5, e6, e4, e7, ?_, rfl, b2, hG⟩
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
      show sentY.length + 1 = dY + 1
      omega
  · exact e1.trans (by
      rw [List.map_append, a1]
      rfl)
  · rw [a5]
    rfl

/-! ### The weights -/

/-- The two weights of each round. -/
def tscXs (zs : List E) : List (K × K) := zs.map fun z => (1 - ρ.val z, ρ.val z)

theorem twos_tsc : ∀ zs : List E, Twos 3 ((tscWs zs).map (wtOf ρ)) (tscXs ρ zs)
  | [] => trivial
  | z :: zs => ⟨two_equality ρ z 3 (by omega), le_refl 3, twos_tsc zs⟩

theorem held_tsc (zs : List E) : ∀ w ∈ tscWs zs, Held w := by
  intro w hw
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hw
  exact held_equality _ 3 (by omega)

/-- The public part of a slot's form reads as what was shown. -/
theorem publicPart_slot {G : Fork} {j : ℕ} {T : E} (h : G.publicPart (Aff.slot j) = some T) :
    ρ.val T = ρ.val (G.vp.getD j zeroE) ∧ Filled G j := by
  have h' : (G.shown j).map (fun y => addE zeroE (mulE oneE y)) = some T := by
    simpa [Fork.publicPart, Aff.slot] using h
  cases hq : G.shown j with
  | none => simp [hq] at h'
  | some y =>
    rw [hq, Option.map_some] at h'
    have hy := shown_some hq
    rw [← Option.some.inj h', ρ.add, ρ.mul, ρ.zero, ρ.one, hy.2.2]
    exact ⟨by ring, hy.2.1⟩

end OnBytes.Desc.First.P1
