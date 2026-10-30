-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscLayer.lean: one layer of a product tree (levelIn of
OnBytes/Model/Psc.lean) on a run: what was heard, the sumcheck's record, all five fields of Level,
and the state.

Main names:
  `levelWeights`: the weights of a layer's rounds.
  `placed`: the challenges of the rounds, each put at the place mu - 1 - v of its variable v.
    `placed_size`, `placed_other`, `placed_get`: if no variable stands twice in the order, the place
    of the j-th variable holds the j-th challenge.
  `levelRounds_r`: the rounds of a layer, with what they leave in r.
  `levelIn_seam`: Parts and Ended (PscSeam.lean in this folder), the rounds' sizes and the weights'
    fits, the fields r, sL, sR, tau and row, and two fillings of the state.
Limits: levelIn does not test that the order has no variable twice, only its length and that each
variable is below mu; with a variable twice a place of o.r stays 0. The round LINE is given as
Blk.closeOne "LINE" .elems 0, not in the words of the block's own line. One direction only, from a
success of the model's routine. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscSeam

set_option autoImplicit false

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany hear claimAfter polyAt hidingWalk hidingEntries)

theorem shownS_ok (j : Nat) (F G : Fork) (c c' : Ctx) (y : E) :
    SubM.shown j F c = .ok ((y, G), c') ↔ F.shown j = some y ∧ G = F ∧ c' = c := by
  unfold SubM.shown
  exact ask_ok _ F G c c' y

/-- The weights of a layer's rounds. -/
def levelWeights (mu : Nat) (rho : Array E) (order : List Nat) : List Weight :=
  order.map fun v => Weight.equality (rho.getD (mu - 1 - v) zeroE) 3

/-- Each challenge put at the place of its variable. -/
def placed (mu : Nat) : Array E → List Nat → List E → Array E
  | r, v :: order, x :: xs => placed mu (r.set! (mu - 1 - v) x) order xs
  | r, _, _ => r

theorem placed_size (mu : Nat) : ∀ (order : List Nat) (xs : List E) (r : Array E),
    (placed mu r order xs).size = r.size
  | [], _, _ => by simp [placed]
  | _ :: _, [], _ => by simp [placed]
  | v :: order, x :: xs, r => by
    simp only [placed]
    rw [placed_size mu order xs]
    simp [Array.set!_eq_setIfInBounds]

theorem placed_other (mu : Nat) (i : Nat) : ∀ (order : List Nat) (xs : List E) (r : Array E),
    (∀ v ∈ order, mu - 1 - v ≠ i) → (placed mu r order xs).getD i zeroE = r.getD i zeroE
  | [], _, _, _ => by simp [placed]
  | _ :: _, [], _, _ => by simp [placed]
  | v :: order, x :: xs, r, h => by
    simp only [placed]
    rw [placed_other mu i order xs _ fun u hu => h u (List.mem_cons_of_mem _ hu)]
    exact getD_set_other _ _ _ _ _ (h v List.mem_cons_self).symm

/-- If no variable stands twice in the order, the place of the j-th variable holds the j-th
challenge. -/
theorem placed_get (mu : Nat) : ∀ (order : List Nat) (xs : List E) (r : Array E) (j : Nat),
    order.Nodup → (∀ v ∈ order, v < mu) → r.size = mu → xs.length = order.length →
        j < order.length →
    (placed mu r order xs).getD (mu - 1 - order.getD j 0) zeroE = xs.getD j zeroE
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, h, _ => by simp at h
  | v :: order, x :: xs, r, 0, nd, hb, hr, _, _ => by
    simp only [placed, List.getD_cons_zero]
    have hv := hb v List.mem_cons_self
    rw [placed_other mu _ order xs]
    · exact getD_set_same _ _ _ _ (by omega)
    · intro u hu he
      have hu' := hb u (List.mem_cons_of_mem _ hu)
      have : u = v := by omega
      rw [this] at hu
      exact (List.nodup_cons.1 nd).1 hu
  | v :: order, x :: xs, r, j + 1, nd, hb, hr, hl, hj => by
    simp only [placed, List.getD_cons_succ]
    exact placed_get mu order xs _ j (List.nodup_cons.1 nd).2
      (fun u hu => hb u (List.mem_cons_of_mem _ hu)) (by simp [Array.set!_eq_setIfInBounds, hr])
      (by simpa using hl) (by simpa using hj)

/-- The rounds of a layer, with what they leave in r. -/
theorem levelRounds_r (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r r' : Array E)
    (p p' : Psc) (F G : Fork) (c c' : Ctx),
    levelRounds mu rho order r p F c = .ok (((r', p'), G), c') →
    ∃ rs, (hearMany ((levelWeights mu rho order).map fun w => w.d - 1)).Yields c rs c' ∧
      Stepped p p' (levelWeights mu rho order) rs ∧
      (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) ∧ G = taken F (2 * order.length) ∧
      r' = placed mu r order (rs.map (·.2))
  | [], r, r', p, p', F, G, c, c', h => by
    simp only [levelRounds] at h
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    obtain ⟨e0, e4⟩ := Prod.mk.inj e1
    rw [e4, e2, e3, e0]
    exact ⟨[], hearMany_nil _, Stepped.nil _, by simp, rfl, rfl⟩
  | v :: order, r, r', p, p', F, G, c, c', h => by
    simp only [levelRounds] at h
    obtain ⟨_, F0, c0, h0, k0⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨b0, e1, e2⟩ := (must_ok _ _ _ _ _ _).1 h0
    rw [e1, e2] at k0
    obtain ⟨⟨x, p1⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 k0
    obtain ⟨w, sent, b1, _, y1, a1, a2, a3, a4, a5⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h1
    rw [eq2_weight] at b1
    have hw := Option.some.inj b1
    rw [← hw] at y1 a1 a2 a3 a4 a5
    obtain ⟨rs, y2, s2, o2, e3, e4⟩ := levelRounds_r mu rho order _ _ _ _ _ _ _ _ k1
    rw [a4] at s2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at b0
    refine ⟨(sent, x) :: rs, hearMany_cons _ _ _ _ _ _ _ y1 y2,
        Stepped.cons _ _ _ _ _ _ _ a1 a2 a3 s2,
      ?_, ?_, ?_⟩
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact b0
      · exact o2 u hu
    · rw [e3, a5]
      show taken (taken F 2) (2 * order.length) = taken F (2 * (order.length + 1))
      rw [taken_taken, show 2 + 2 * order.length = 2 * (order.length + 1) by omega]
    · rw [e4]; rfl

/-- One layer of a product tree. p: the sumcheck's record behind pscEnds. -/
theorem levelIn_seam (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) (F G : Fork) (c c' :
    Ctx)
    (o : Level) (h : levelIn mu rho C order F c = .ok ((o, G), c')) (hs : Sized F) :
    ∃ (τ m eps : E) (rs : List (List E × E)) (sentY : List E) (beta vL vR : E) (cL : Ctx) (p : Psc)
      (F1 : Fork),
      Parts c c cL [] m eps (levelWeights mu rho order) rs 2 sentY beta [vL, vR] ∧
      (Blk.closeOne "LINE" .elems 0).Yields cL o.tau c' ∧
      order.length = mu ∧ (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) ∧
      F.publicPart C = some τ ∧
      rs.length = (levelWeights mu rho order).length ∧
      (∀ x ∈ (levelWeights mu rho order).zip rs, x.2.1.length + 1 = x.1.d) ∧
      (∀ w ∈ levelWeights mu rho order, w.fits = true) ∧
      Ended p C τ m eps F.next (levelWeights mu rho order) rs 2 sentY beta ∧ sentY.length = 2 ∧
      o.r = placed mu (Array.replicate mu zeroE) order (rs.map (·.2)) ∧
      o.row = p.rowForm (mulE vL vR) {} ∧
      o.sL = F.next + (1 + 2 * mu + 2) ∧ o.sR = o.sL + 1 ∧
      Filled (taken F (1 + 2 * mu + 2 + 2)) F1 o.sL [vL, vR] beta ∧
      Filled F1 G F.next (List.replicate p.walk.1.length zeroE) (subE zeroE oneE) := by
  unfold levelIn at h
  obtain ⟨_, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨ba, ea1, ea2⟩ := (must_ok _ _ _ _ _ _).1 ha
  rw [ea1, ea2] at ka
  obtain ⟨p0, Fc, cc, hc, kc⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨⟨r1, p1⟩, Fd, cd, hd, kd⟩ := (bind_ok _ _ _ _ _).1 kc
  obtain ⟨rs, yd, sd, od, Gd, hr1⟩ := levelRounds_r mu rho order _ _ _ _ _ _ _ _ hd
  obtain ⟨⟨sL, p2⟩, Fe, ce, he, ke⟩ := (bind_ok _ _ _ _ _).1 kd
  have hmu : order.length = mu := by simpa using ba
  have hFc : Fc = taken F 1 := (pscBegin_ok C F Fc c cc p0 hc).choose_spec.choose_spec.2.2.2
  have hFd : Fd = taken F (1 + 2 * mu) := by rw [Gd, hFc, taken_taken, hmu]
  obtain ⟨τ, m, sentY, beta, v, pc, _, parts, ran, en, sY, lv, _, _, hE, fE⟩ :=
    seam [] C p0 p1 p2 (levelWeights mu rho order) rs 2 2 sL F Fc Fd Fe c c cc cd ce (recvEs_zero c)
        hc yd sd he
      (by rw [hFd]; exact sized_taken F _ hs)
  obtain ⟨tau, Ff, cf, hf, kf⟩ := (bind_ok _ _ _ _ _).1 ke
  obtain ⟨yf, ef⟩ := (liftY_ok _ _ _ _ _ _).1 hf
  obtain ⟨a, Fg, cg, hg, kg⟩ := (bind_ok _ _ _ _ _).1 kf
  obtain ⟨ag, eg1, eg2⟩ := (shownS_ok _ _ _ _ _ _).1 hg
  obtain ⟨b, Fh, ch, hh, kh⟩ := (bind_ok _ _ _ _ _).1 kg
  obtain ⟨bh, eh1, eh2⟩ := (shownS_ok _ _ _ _ _ _).1 hh
  obtain ⟨⟨row, p3⟩, Fi, ci, hi, ki⟩ := (bind_ok _ _ _ _ _).1 kh
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 ki
  obtain ⟨vL, vR, hv⟩ : ∃ vL vR, v = [vL, vR] := by
    cases v with
    | nil => simp at lv
    | cons a1 l =>
      cases l with
      | nil => simp at lv
      | cons a2 l' =>
        cases l' with
        | nil => exact ⟨a1, a2, rfl⟩
        | cons a3 l'' => simp at lv
  rw [hv] at fE parts
  rw [hFd, taken_taken, ← Nat.add_assoc] at fE
  rw [ef] at ag
  rw [eg1, ef] at bh
  have sa : a = vL := by
    have := fE.shown 0 (by simp)
    rw [Nat.add_zero, ag] at this
    simpa using this
  have sb : b = vR := by
    have := fE.shown 1 (by simp)
    rw [bh] at this
    simpa using this
  rw [eh1, eg1, ef, eh2, eg2] at hi
  obtain ⟨r1', r2', _, fR⟩ := pscRow_filled p2 p3 (mulE a b) {} row Fe Fi cf ci hi fE.sized
  rw [en.first] at fR
  refine ⟨τ, m, p0.eps, rs, sentY, beta, vL, vR, ce, p2, Fe, parts, ?_, hmu, od, pc, ran.len,
      ran.sizes,
    fun w hw => (ran.held w hw).1, en, sY, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e3, r1']
    exact trAnswer_closeOne .line tau ce cf yf
  · rw [e1]; exact hr1
  · rw [e1]; show row = _; rw [r2', sa, sb]
  · rw [e1]; show sL = _; rw [hE, hFd]; rfl
  · rw [e1]
  · rw [e1]; exact fE
  · rw [e2]; exact fR

#print axioms levelIn_seam
#print axioms placed_get

end OnBytes.Model.Road
