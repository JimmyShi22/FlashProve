-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/FoLevelRun.lean.
What a run of the byte-level routines for one level of a product tree does, if it returns.

The routines are levelRounds, levelIn, Level.handDown (OnBytes/Model/Psc.lean) and Forest.level
(OnBytes/Model/Look.lean). Each statement has the form: if the run from the states F, c returns,
then there are the messages and challenges of the rounds such that the channel's calls are these,
in this order; the slots taken are these; and the result is this term in them. The state of the
sumcheck is described by `Ran` (OnBytes/Tie/Pv/Psc/PscWhole.lean). Nothing is read into another ring
here.
* `lvZd mu rho order`: for each round the coordinate of the point that it reads, place
  mu - 1 - v of the array, with the number 3 of coefficients.
* `lvEv rs`, `levelEv`: the channel's calls of the rounds rs (message, challenge); of a level.
* `levelRounds_ran`: the rounds; the array of challenges is `Fo.stored`. Premise: `Ran` of the
  sumcheck's state before them.
* `levelIn_ran`: a whole level: the beginning, the rounds, the round in the further variable
  with the two end values, the line's draw, the claim.
* `level_ok`: the step of the walk down a tree.

-/
import OnBytes.Tie.Pv.Psc.PscWhole
import OnBytes.Model.Look
import OnBytes.Tie.Pv.Lookup.Forest.FoStore
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc

/-- For each round: the coordinate that it reads, and the number of coefficients. -/
def lvZd (mu : ℕ) (rho : Array E) (order : List ℕ) : List (E × ℕ) :=
  order.map fun v => (rho.getD (mu - 1 - v) zeroE, 3)

/-- The channel's calls of the rounds. -/
def lvEv (rs : List (Array E × E)) : List Ev :=
  rs.flatMap fun q => [.read 2 q.1, .ans .pscRound q.2]

/-- The rounds as OnBytes.Psc.claimAfter takes them. -/
def lvRs (rs : List (Array E × E)) : List (List E × E) := rs.map fun q => (q.1.toList, q.2)

private theorem took_took (F : Fork) (a b : ℕ) : took (took F a) b = took F (a + b) := by
  simp only [took, Nat.add_assoc]

theorem levelRounds_ran (mu : ℕ) (rho : Array E) : ∀ (order : List ℕ) (r : Array E) (p : Psc)
    (first : ℕ) (m0 eps : E) (zd : List (E × ℕ)) (rs0 : List (List E × E)),
    Ran p first m0 eps zd rs0 → ∀ (F G : Fork) (c c' : Ctx) (r' : Array E) (p' : Psc),
    levelRounds mu rho order r p F c = .ok (((r', p'), G), c') →
    ∃ rs : List (Array E × E), rs.length = order.length ∧
      (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) ∧ (∀ q ∈ rs, q.1.size = 2) ∧
      Evs (lvEv rs) c c' ∧ G = took F (2 * order.length) ∧
      r' = stored mu order (rs.map (·.2)) r ∧ p'.target = p.target ∧ p'.start = p.start ∧
      p'.started = p.started ∧ p'.rowMade = p.rowMade ∧
      Ran p' first m0 eps (zd ++ lvZd mu rho order) (rs0 ++ lvRs rs)
  | [], r, p, first, m0, eps, zd, rs0, hp, F, G, c, c', r', p', h => by
    rw [levelRounds, pure_ok] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
    refine ⟨[], rfl, by simp, by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simpa [lvZd, lvRs] using hp
  | v :: order, r, p, first, m0, eps, zd, rs0, hp, F, G, c, c', r', p', h => by
    rw [levelRounds, bind_ok] at h
    obtain ⟨_, F1, c1, hm, h⟩ := h
    rw [must_ok] at hm
    obtain ⟨hb, e1⟩ := hm
    obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
    rw [bind_ok] at h
    obtain ⟨⟨x, p1⟩, F2, c2, hr, h⟩ := h
    obtain ⟨sent, hs, hev, rfl, ht, hst, hsd, hrm, -, hp1⟩ := ran_roundIn2 hp _ _ _ _ _ _ _ _ hr
    simp only [] at h
    obtain ⟨rs, hl, hv, hq, hE, rfl, rfl, ht2, hst2, hsd2, hrm2, hp2⟩ :=
      levelRounds_ran mu rho order _ p1 first m0 eps _ _ hp1 _ _ _ _ _ _ h
    have hb' : v < mu ∧ mu - 1 - v < rho.size := by simpa using hb
    refine ⟨(sent, x) :: rs, by simp [hl], ?_, ?_, ?_, ?_, rfl, ht2.trans ht, hst2.trans hst,
      hsd2.trans hsd, hrm2.trans hrm, ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hb'
      · exact hv u hu
    · intro q hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact hs
      · exact hq q hq'
    · exact (evs_append [.read 2 sent, .ans .pscRound x] (lvEv rs) _ _).2 ⟨_, hev, hE⟩
    · rw [took_took, List.length_cons, Nat.mul_add, Nat.add_comm 2]
    · simpa [lvZd, lvRs, List.append_assoc] using hp2

/-- The channel's calls of a whole level. -/
def levelEv (m0 eps : E) (rs : List (Array E × E)) (sentY : Array E) (beta : E) (vals : Array E)
    (tau : E) : List Ev :=
  [.sum m0, .ans .pscEpsilon eps] ++ (lvEv rs ++
    ([.read 2 sentY, .ansNZ .pscY beta, .read 2 vals, .empty .pscValues] ++ [.ans .line tau]))

theorem levelIn_ran (mu : ℕ) (rho : Array E) (C : Aff) (order : List ℕ) (F G : Fork) (c c' : Ctx)
    (o : Level) (h : levelIn mu rho C order F c = .ok ((o, G), c')) :
    ∃ (p : Psc) (m0 eps : E) (rs : List (Array E × E)) (sentY : Array E) (beta : E)
      (vals : Array E) (vL vR : E) (F3 : Fork) (p' : Psc),
      order.length = mu ∧ F.publicPart C = some p.target ∧ p.start = C ∧
      rs.length = order.length ∧ (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) ∧
      (∀ q ∈ rs, q.1.size = 2) ∧ sentY.size = 2 ∧ vals.size = 2 ∧
      Evs (levelEv m0 eps rs sentY beta vals o.tau) c c' ∧
      Ran p F.next m0 eps (lvZd mu rho order ++ [(zeroE, 3)])
        (lvRs rs ++ [(sentY.toList, beta)]) ∧
      o.sL = F.next + 1 + 2 * order.length + 2 ∧ o.sR = o.sL + 1 ∧
      (took F (1 + 2 * order.length + (2 + 2))).hideRun o.sL vals beta = some F3 ∧
      F3.shown o.sL = some vL ∧ F3.shown (o.sL + 1) = some vR ∧
      F3.hideRun F.next (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G ∧
      o.r = stored mu order (rs.map (·.2)) (Array.replicate mu zeroE) ∧
      o.row = p.rowForm (mulE vL vR) {} ∧
      pscRow p (mulE vL vR) {} F3 c' = .ok (((o.row, p'), G), c') := by
  unfold levelIn at h
  rw [bind_ok] at h
  obtain ⟨_, F0, c0, h0, h⟩ := h
  rw [must_ok] at h0
  obtain ⟨hlen, e0⟩ := h0
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e0
  rw [bind_ok] at h
  obtain ⟨p0, F1, c1, h1, h⟩ := h
  obtain ⟨target, m0, eps, hpub, hE1, rfl, hp0⟩ := pscBegin_ok _ _ _ _ _ _ h1
  have hR0 : Ran p0 F.next m0 eps [] [] := hp0 ▸ ran_begin C target m0 eps F.next
  have ht0 : p0.target = target := by rw [hp0]
  have hs0 : p0.start = C := by rw [hp0]
  clear hp0
  rw [bind_ok] at h
  obtain ⟨⟨r1, p1⟩, F2, c2, h2, h⟩ := h
  obtain ⟨rs, hl, hv, hq, hE2, rfl, rfl, ht1, hs1, -, -, hR1⟩ :=
    levelRounds_ran _ _ _ _ _ _ _ _ _ _ hR0 _ _ _ _ _ _ h2
  simp only [] at h
  rw [bind_ok] at h
  obtain ⟨⟨sL, p2⟩, F3, c3, h3, h⟩ := h
  obtain ⟨sentY, beta, vals, hsY, hsv, hE3, rfl, hH3, ht2, hs2, -, -, -, hR2⟩ :=
    ran_ends hR1 _ _ _ _ _ _ _ _ h3
  simp only [] at h
  rw [bind_ok] at h
  obtain ⟨tau, F4, c4, h4, h⟩ := h
  obtain ⟨hE4, rfl⟩ := (answer_ok _ _ _ _ _ _).1 h4
  rw [bind_ok] at h
  obtain ⟨vL, F5, c5, h5, h⟩ := h
  obtain ⟨vL', hvL, e5⟩ := (shown_ok _ _ _ _).1 h5
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e5
  rw [bind_ok] at h
  obtain ⟨vR, F6, c6, h6, h⟩ := h
  obtain ⟨vR', hvR, e6⟩ := (shown_ok _ _ _ _).1 h6
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e6
  rw [bind_ok] at h
  obtain ⟨⟨row, p3⟩, F7, c7, h7, h⟩ := h
  have h7' := h7
  obtain ⟨-, -, -, -, rfl, hH7, rfl, -⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h7
  simp only [] at h
  rw [pure_ok] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  rw [took_took, took_took] at hH3
  rw [hR2.first_eq] at hH7
  refine ⟨p2, m0, eps, rs, sentY, beta, vals, _, _, _, p3, by simpa using hlen,
    by rw [ht2, ht1, ht0]; exact hpub, by rw [hs2, hs1, hs0], hl, hv, hq, hsY, hsv, ?_,
    by simpa using hR2, rfl, rfl, hH3, hvL, hvR, hH7, rfl, rfl, h7'⟩
  exact (evs_append _ _ _ _).2 ⟨_, hE1, (evs_append _ _ _ _).2 ⟨_, hE2,
    (evs_append _ _ _ _).2 ⟨_, hE3, hE4⟩⟩⟩

theorem level_ok (s : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Ctx)
    (s' : Forest.Descent) (h : Forest.level s mu order F c = .ok ((s', G), c')) :
    ∃ o : Level, levelIn mu s.rho s.form order F c = .ok ((o, G), c') ∧
      s'.rows = s.rows.push o.row ∧ s'.rho = #[o.tau] ++ o.r ∧
      s'.form = Aff.scale (Aff.slot o.sL) (subE oneE o.tau) + Aff.scale (Aff.slot o.sR) o.tau := by
  unfold Forest.level at h
  rw [bind_ok] at h
  obtain ⟨o, F1, c1, h1, h⟩ := h
  simp only [Level.handDown] at h
  rw [pure_ok] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨o, h1, rfl, rfl, rfl⟩

end Fo
