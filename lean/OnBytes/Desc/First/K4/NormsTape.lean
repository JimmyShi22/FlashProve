-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/NormsTape.lean: the first stretch of the layers' own rounds, `hearNorms`
(OnBytes/Desc/First/K4/Hear.lean), over the plain engine `engFl` (K4/Plain.lean): WHERE ON THE TAPE
each of its calls stands, and on which ledger. Statements and proofs.

`hearNorms_calls` (NormsCalls.lean) gives the calls as equations on tapes and ledgers that stand
under "there are". Here each of these tapes is the tape t without its first k rounds, for a k that
is computed from public numbers, and six of the nine ledgers are named.

  `k0 g`: the number of rounds in front of the norms' sums: 3 in the first group, else 1.
  `hearNorms_tape`: round 0 draws the point PV. Round k0 sends the sums and draws gam. Round k0 + 1
    draws rhoI. From round k0 + 2 on, muV + 4 rounds: the squares' sumcheck, as a return of
    `Fl.levelIn`. Round k0 + muV + 6 sends the products and draws om. From round k0 + muV + 7 on:
    the products' sumcheck, as a return of `Fl.tscIn`. What is left of the tape is said too.

One direction: from a return. Nothing is said of what the calls mean.
-/
import OnBytes.Desc.First.K4.NormsCalls
import OnBytes.Desc.First.P1.TscLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
open OnBytes.Desc.First.P1 (point_spec claimsIn_spec batch_spec putBack putBack_cons levelIn_tape
  tscIn_tape drop_level drop_tsc drop_one_cons)

/-! ### Places on a list -/

theorem drop_drop' {α : Type} : ∀ (a b : Nat) (t : List α), (t.drop a).drop b = t.drop (a + b)
  | 0, b, t => by simp
  | a + 1, b, [] => by simp
  | a + 1, b, x :: t => by
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [List.drop_succ_cons, drop_drop' a b t, e, List.drop_succ_cons]

/-- Behind the first member of what is left behind a members stands what is left behind a + 1. -/
theorem drop_next {α : Type} {t v u : List α} {a : Nat} {x : α} (p : v = t.drop a)
    (h : v = x :: u) : u = t.drop (a + 1) := by
  have e : (t.drop a).drop 1 = t.drop (a + 1) := drop_drop' a 1 t
  rw [← e, ← p, h, drop_one_cons]

theorem drop_more {α : Type} {t v u : List α} {a k : Nat} (p : v = t.drop a)
    (h : u = v.drop k) : u = t.drop (a + k) := by
  rw [h, p, drop_drop']

/-- The same place, its number written otherwise. -/
theorem drop_at {α : Type} {t u : List α} {a b : Nat} (p : u = t.drop a) (h : a = b) :
    u = t.drop b := by
  rw [← h]
  exact p

/-! ### What two functions leave of the tape -/

theorem levelIn_rest {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    u = t.drop (mu + 4) := by
  obtain ⟨_, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, ht,
    hrs, _⟩ := levelIn_tape h
  rw [ht, ← hrs, drop_level]

theorem tscIn_rest {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    u = t.drop ((P.toList.take lt).length + 3) := by
  obtain ⟨_, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0, ht, hrs, _⟩ :=
    tscIn_tape h
  rw [ht, ← hrs, drop_tsc]

/-! ### The norms' stretch -/

/-- The number of rounds in front of the norms' sums. -/
def k0 (g : Nat) : Nat := if g == 0 then 3 else 1

/-- **Where on the tape the norms' stretch stands.** -/
theorem hearNorms_tape {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H : Heard} (h : hearNorms engFl P g fo F t = some (H, G, u)) :
    ∃ (F4 F7 F8 : Fork) (rhoI vW vP : Array E) (gam om : E) (w0 wI : Nat) (d0 dI : List E),
      t = ⟨some RoundName.zero.name, 0, w0, [], d0⟩ :: t.drop 1 ∧
      d0.length = P.y.h.lt ∧ H.PV = d0.toArray ∧
      t.drop (k0 g) = ⟨some RoundName.batSigma.name, 0, ledNS P.y.h.xl, vW.toList, [gam]⟩ ::
        t.drop (k0 g + 1) ∧
      vW.size = ledNS P.y.h.xl * P.y.NI ∧ H.sW = F.next ∧
      ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork).hideRun F.next vW oneE =
        some F4 ∧
      H.gp = powers gam (ledNS P.y.h.xl) ∧
      t.drop (k0 g + 1) = ⟨some RoundName.join.name, 0, wI, [], dI⟩ :: t.drop (k0 g + 2) ∧
      dI.length = P.rd.lNI ∧ rhoI = dI.toArray ∧
      Fl.levelIn P.rd.muV (normsStart P.y H.sW H.gp rhoI H.PV).2
          (normsStart P.y H.sW H.gp rhoI H.PV).1 (orderDefault P.rd.muV) F4
          (t.drop (k0 g + 2)) =
        some (H.wpl, F7, t.drop (k0 g + P.rd.muV + 6)) ∧
      t.drop (k0 g + P.rd.muV + 6) =
        ⟨some RoundName.batSigma.name, 0, ledNP P.y.h.xl * P.y.NI, vP.toList, [om]⟩ ::
          t.drop (k0 g + P.rd.muV + 7) ∧
      vP.size = ledNP P.y.h.xl * P.y.NI ∧ H.sPv = F7.next ∧
      ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork).hideRun F7.next vP oneE =
        some F8 ∧
      H.omV = powers om (ledNP P.y.h.xl * P.y.NI) ∧
      Fl.tscIn H.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8 (t.drop (k0 g + P.rd.muV + 7)) =
        some (H.tV, G, u) ∧
      u = t.drop (k0 g + P.rd.muV + 7 + ((H.PV.toList.take P.y.h.lt).length + 3)) := by
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, c1, c2, c3, _,
    c4, c5, rhoI, c6, c7, c8, c9, c10, _⟩ := hearNorms_calls h
  -- round 0
  have c1' : Fl.point .zero P.y.h.lt F t = some (H.PV, F1, t1) := c1
  obtain ⟨rfl, w0, d0, e0, l0, hPV⟩ := point_spec c1'
  have p0 : t = t.drop 0 := rfl
  have p1 : t1 = t.drop (0 + 1) := drop_next p0 e0
  -- the two points more of the first group
  have hfront : F = F3 ∧ t3 = t.drop (k0 g) := by
    unfold k0
    by_cases hg : (g == 0) = true
    · simp only [hg, if_true] at c2 c3 ⊢
      have c2' : Fl.point .zero (P.y.ls + P.y.h.lt) F t1 = some (H.ZE, F2, t2) := c2
      obtain ⟨rfl, _, _, e1, _, _⟩ := point_spec c2'
      have c3' : Fl.point .zero (P.y.lPd - P.y.ls) F t2 = some (H.tkh, F3, t3) := c3
      obtain ⟨rfl, _, _, e2, _, _⟩ := point_spec c3'
      exact ⟨rfl, drop_next (drop_next p1 e1) e2⟩
    · have hg' : (g == 0) = false := by simpa using hg
      simp only [hg', Bool.false_eq_true, if_false] at c2 c3 ⊢
      obtain ⟨_, rfl, rfl⟩ := P1.pure_some.mp c2
      obtain ⟨_, rfl, rfl⟩ := P1.pure_some.mp c3
      exact ⟨rfl, p1⟩
  obtain ⟨rfl, p3⟩ := hfront
  -- the sums and gam
  obtain ⟨hsW, vW, hvW, e3, _, hF4⟩ := claimsIn_spec c4
  obtain ⟨_, rfl, gam, e4, hgp⟩ := batch_spec c5
  rw [e4, putBack_cons, List.append_nil] at e3
  have p5 : t5 = t.drop (k0 g + 1) := drop_next p3 e3
  -- rhoI
  have c6' : Fl.point .join P.rd.lNI F4 t5 = some (rhoI, F6, t6) := c6
  obtain ⟨rfl, wI, dI, e5, lI, hrho⟩ := point_spec c6'
  have p6 : t6 = t.drop (k0 g + 2) := drop_next p5 e5
  -- the squares' sumcheck
  have p7 : t7 = t.drop (k0 g + P.rd.muV + 6) :=
    drop_at (drop_more p6 (levelIn_rest c7)) (by omega)
  -- the products and om
  obtain ⟨hsPv, vP, hvP, e7, _, hF8⟩ := claimsIn_spec c8
  obtain ⟨_, rfl, om, e8, hom⟩ := batch_spec c9
  rw [e8, putBack_cons, List.append_nil] at e7
  have p9 : t9 = t.drop (k0 g + P.rd.muV + 7) := drop_next p7 e7
  -- the products' sumcheck
  have pu := drop_more p9 (tscIn_rest c10)
  refine ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, ?_, l0, hPV, ?_, hvW, hsW, hF4, hgp,
    ?_, lI, hrho, ?_, ?_, hvP, hsPv, hF8, hom, ?_, pu⟩
  · rw [← p1]
    exact e0
  · rw [← p3, ← p5]
    exact e3
  · rw [← p5, ← p6]
    exact e5
  · rw [← p6, ← p7]
    exact c7
  · rw [← p7, ← p9]
    exact e7
  · rw [← p9]
    exact c10

end OnBytes.Desc.First.K4
