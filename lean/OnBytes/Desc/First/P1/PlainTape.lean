-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/PlainTape.lean: the rounds of a sumcheck without an equality factor, as the
layers' own rounds (K4) hear them: `Fl.roundIn .sum2` (OnBytes/K/Kc/Flat.lean) and `plainRounds`
(OnBytes/Desc/First/K4/Engine.lean), taken apart where they return, with what the tape was.
Statements and proofs.

  `roundIn_sum2_tape`: one round of degree 2 that is summed plainly: its weight is
    `Weight.plain 3`, whatever z and degree the caller hands in; two elements are sent.
  `plainWs n`: n such weights.
  `sum2Loop_tape`: a fold of such rounds that appends the challenges.
  `plainRounds_tape`: `plainRounds` over any engine of plain functions whose `roundIn` is
    `Fl.roundIn`. The engine `engFl` (OnBytes/Desc/First/K4/Plain.lean) is such a one by its
    definition; that file is not imported here.

What is not shown. One direction: from a return. Nothing on soundness: no law of a sumcheck is
applied here.
-/
import OnBytes.Desc.First.P1.FlTape
import OnBytes.Desc.First.K4.Engine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc

theorem roundIn_sum2_tape {p p' : Psc} {z : E} {d : Nat} {F G : Fork} {t u : Tape} {r : E}
    (h : Fl.roundIn .sum2 p z d F t = some ((r, p'), G, u)) :
    Held (OnBytes.Psc.Weight.plain 3) ∧ ∃ (sent : List E) (k : Nat), sent.length = 2 ∧
      p' = stepP p (OnBytes.Psc.Weight.plain 3, sent, r) ∧
      G = { F with next := F.next + 2 } ∧
      t = ⟨some Model.RoundName.pscRound.name, 0, k, sent, [r]⟩ :: u := by
  unfold Fl.roundIn at h
  obtain ⟨_, G1, u1, h1, k11⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := must_some.mp h1
  obtain ⟨w, G2, u2, h2, k12⟩ := bind_some.mp k11
  obtain ⟨hw, rfl, rfl⟩ := need_some.mp h2
  have hw' : OnBytes.Psc.Weight.plain 3 = w := Option.some.inj hw
  subst hw'
  obtain ⟨hh, sent, k, hl, hp, hG, ht⟩ := pscRound_tape k12
  have hl3 : sent.length + 1 = 3 := hl
  exact ⟨hh, sent, k, by omega, hp, hG, ht⟩

/-- The weights of n rounds of degree 2 that are summed plainly. -/
def plainWs (n : Nat) : List OnBytes.Psc.Weight := List.replicate n (OnBytes.Psc.Weight.plain 3)

theorem msOf_plain_cons (n : Nat) (nm : Option String) (z k : Nat) (sent : List E) (c : E)
    (rs : List FlatRound) :
    msOf (plainWs (n + 1)) (⟨nm, z, k, sent, [c]⟩ :: rs) =
      (OnBytes.Psc.Weight.plain 3, sent, c) :: msOf (plainWs n) rs := rfl

/-- A fold of n rounds. f: a step that hears one round and appends its challenge. -/
theorem sum2Loop_tape (f : Array E × Psc → E × Nat → Fl (Array E × Psc))
    (hf : ∀ (s s' : Array E × Psc) (z : E × Nat) (F G : Fork) (t u : Tape),
      f s z F t = some (s', G, u) →
      ∃ (c : E) (q : Psc), Fl.roundIn .sum2 s.2 z.1 z.2 F t = some ((c, q), G, u) ∧
        s' = (s.1.push c, q)) :
    ∀ (n : Nat) (zs : List (E × Nat)), zs.length = n →
    ∀ {s s' : Array E × Psc} {F G : Fork} {t u : Tape},
    zs.foldlM f s F t = some (s', G, u) →
    ∃ rs : List FlatRound, t = rs ++ u ∧ rs.length = n ∧
      (∀ x ∈ rs, x.name = some Model.RoundName.pscRound.name ∧ x.nz = 0 ∧ x.drawn.length = 1) ∧
      (msOf (plainWs n) rs).map (·.1) = plainWs n ∧ (∀ m ∈ msOf (plainWs n) rs, Held m.1) ∧
      (∀ m ∈ msOf (plainWs n) rs, m.2.1.length + 1 = m.1.d) ∧
      s'.2 = runP s.2 (msOf (plainWs n) rs) ∧
      s'.1.toList = s.1.toList ++ (msOf (plainWs n) rs).map (·.2.2) ∧
      G = { F with next := F.next + 2 * n }
  | 0, [], _, s, s', F, G, t, u, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp h
    have e0 : msOf (plainWs 0) [] = [] := rfl
    refine ⟨[], rfl, rfl, by simp, ?_⟩
    rw [e0]
    exact ⟨rfl, by simp, by simp, rfl, by simp, rfl⟩
  | 0, _ :: _, hz, _, _, _, _, _, _, _ => by simp at hz
  | _ + 1, [], hz, _, _, _, _, _, _, _ => by simp at hz
  | n + 1, z :: zs, hz, s, s', F, G, t, u, h => by
    have hz' : zs.length = n := by simpa using hz
    rw [List.foldlM_cons] at h
    obtain ⟨s1, G1, u1, h1, k1⟩ := bind_some.mp h
    obtain ⟨c, q, h2, rfl⟩ := hf s s1 z F G1 t u1 h1
    obtain ⟨hh, sent, k, hl, rfl, rfl, ht⟩ := roundIn_sum2_tape h2
    obtain ⟨rs, b0, b1, b2, a1, a2, a3, a4, a5, a6⟩ := sum2Loop_tape f hf n zs hz' k1
    have et := ht.trans (congrArg
      (List.cons (⟨some Model.RoundName.pscRound.name, 0, k, sent, [c]⟩ : FlatRound)) b0)
    refine ⟨⟨some Model.RoundName.pscRound.name, 0, k, sent, [c]⟩ :: rs, et, ?_, ?_, ?_⟩
    · rw [List.length_cons, b1]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨rfl, rfl, rfl⟩
      · exact b2 x hx
    rw [msOf_plain_cons]
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
    · rw [a5, List.map_cons]
      simp
    · rw [a6]
      show ({ F with next := F.next + 2 + 2 * n } : Fork) = _
      have : F.next + 2 + 2 * n = F.next + 2 * (n + 1) := by omega
      rw [this]

/-- **The rounds of a batched sumcheck, with the tape.** As many rounds of the tape as the state
counts, each under the name of a sumcheck's round, with two elements sent and one drawn. The
challenges are laid in the reverse of the rounds' order. -/
theorem plainRounds_tape {En : K4.Eng Fl}
    (hEn : ∀ (f : RoundForm) (p : Psc) (z : E) (d : Nat), En.roundIn f p z d = Fl.roundIn f p z d)
    {st st' : Stack} {F G : Fork} {t u : Tape}
    (h : K4.plainRounds En st F t = some (st', G, u)) :
    ∃ rs : List FlatRound, t = rs ++ u ∧ rs.length = st.lam ∧
      (∀ x ∈ rs, x.name = some Model.RoundName.pscRound.name ∧ x.nz = 0 ∧ x.drawn.length = 1) ∧
      (msOf (plainWs st.lam) rs).map (·.1) = plainWs st.lam ∧
      (∀ m ∈ msOf (plainWs st.lam) rs, Held m.1) ∧
      (∀ m ∈ msOf (plainWs st.lam) rs, m.2.1.length + 1 = m.1.d) ∧
      st'.p = runP st.p (msOf (plainWs st.lam) rs) ∧
      st'.rs.toList = ((msOf (plainWs st.lam) rs).map (·.2.2)).reverse ∧
      st'.lam = st.lam ∧
      G = { F with next := F.next + 2 * st.lam } := by
  unfold K4.plainRounds at h
  obtain ⟨x, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨r, p⟩ := x
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k1
  obtain ⟨rs, b0, b1, b2, a1, a2, a3, a4, a5, a6⟩ := sum2Loop_tape _ (by
    intro s s' z F' G' t' u' hs
    obtain ⟨y, G2, u2, h2, k2⟩ := bind_some.mp hs
    obtain ⟨c, q⟩ := y
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k2
    rw [hEn] at h2
    exact ⟨c, q, h2, rfl⟩) st.lam _ (by simp) h1
  refine ⟨rs, b0, b1, b2, a1, a2, a3, a4, ?_, rfl, a6⟩
  show r.reverse.toList = _
  have a5' : r.toList = (msOf (plainWs st.lam) rs).map (·.2.2) := by simpa using a5
  rw [Array.toList_reverse, a5']

end OnBytes.Desc.First.P1
