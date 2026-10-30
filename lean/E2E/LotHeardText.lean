-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotHeardText.lean: for HeardOfFold: WHERE THE VERIFIER's HEARING OF A LOOKUP WITH SEVERAL PARTS
OF KEYS RETURNS, EACH PART's KEY POINT IS MADE OF THE ROUNDS' FIRST SAMPLES, FOUND BY NUMBER. On the general text
(messagesG, Johnson/Desc/First/Look/K3LookupGeneral.lean), at every face without a shift that passes the verifier's tests.

  firsts, Cut     the first sample of each round of a tape; «u is t behind n rounds»
  ptL             the point behind a level with m variables whose first round has the number a
  whole_cut, level_cut, levels_cut   a masked sumcheck, a level, a run of levels: how many rounds, which samples
  Kr, offK, oKeys   the numbers of rounds: of a run of levels; in front of part q's tree; in front of all trees
  tie_cut, parts_cut, keys_pts   the tie, the parts' steps: how many rounds; the trees: each part's point
  messages_pts    THE TEXT: part q's point is ptL at the number oKeys f + offK f.parts q + (the levels in front)
  tape_firsts, heard_pts   the same of a hearing on rounds (hearE): at the rounds' own first samples (e1)

After: the walk is that of Johnson/Desc/First/Look/KeyLaw/KeySizes.lean (messages_keys), with the samples carried.

Limits. Where the hearing returns. Of what was heard the parts' points alone. Nothing on any prover; nothing on
soundness, completeness, hiding or binding.
-/
import Johnson.Desc.First.Look.KeyLaw.KeySizes
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName)
open OnBytes.PscRun (Ran)
open VerifiableInference.Desc.K3 (Face HeardG messagesG keysG partsG tieG)
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.First.Prod (Carried Whole LevelOut turn level layBack wholeStandIn)

/-! ## 1 A tape's first samples -/

/-- The first element that each round of a tape drew; 0 where it drew none. -/
def firsts (t : Tape) : List E := t.map fun r => r.drawn.headD zeroE

theorem firsts_key (t : Tape) : firsts t = (t.map key).map fun k => k.2.2.2.headD zeroE := by
  unfold firsts
  rw [List.map_map]
  rfl

/-- u is t behind n rounds. -/
def Cut (t u : Tape) (n : Nat) : Prop := ∃ pre, firsts t = pre ++ firsts u ∧ pre.length = n

theorem Cut.refl (t : Tape) : Cut t t 0 := ⟨[], rfl, rfl⟩

theorem Cut.trans {t u v : Tape} {a b : Nat} (h : Cut t u a) (h' : Cut u v b) : Cut t v (a + b) := by
  obtain ⟨p, e, l⟩ := h
  obtain ⟨q, e', l'⟩ := h'
  exact ⟨p ++ q, by rw [e, e', List.append_assoc], by rw [List.length_append, l, l']⟩

theorem Cut.drop {t u : Tape} {n : Nat} (h : Cut t u n) : firsts u = (firsts t).drop n := by
  obtain ⟨p, e, l⟩ := h
  rw [e, List.drop_left' l]

theorem Cut.le {t u : Tape} {n : Nat} (h : Cut t u n) : n ≤ (firsts t).length := by
  obtain ⟨p, e, l⟩ := h
  rw [e, List.length_append, l]
  exact Nat.le_add_right _ _

theorem Cut.cast {t u : Tape} {a b : Nat} (h : Cut t u a) (e : a = b) : Cut t u b := e ▸ h

/-- **The point behind a level with m variables** whose first round has the number a in the list L of first
samples: the sample of "LINE", then the level's challenges laid back. -/
def ptL (m : Nat) (order : List Nat) (L : List E) (a : Nat) : Array E :=
  #[L.getD (a + m + 3) zeroE] ++ layBack m order ((L.drop (a + 1)).take m)

theorem ptL_drop (m : Nat) (order : List Nat) (L : List E) (b a : Nat) :
    ptL m order (L.drop b) a = ptL m order L (b + a) := by
  unfold ptL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, List.drop_drop,
    Nat.add_assoc b a m, Nat.add_assoc b (a + m) 3, Nat.add_assoc b a 1]

/-! ## 2 A sumcheck, a level, a run of levels -/

/-- **One whole masked sumcheck**: its rounds' first samples, and the challenges that it hands back. -/
theorem whole_cut {C : Aff} {zs : List E} {dY n : Nat} {endTerm : List E → E} {F G : Fork}
    {t u : Tape} {w : Whole} (h : wholeStandIn C zs dY n endTerm F t = some (w, G, u)) :
    ∃ (eps beta : E) (cs : List E), cs.length = zs.length ∧
      firsts t = eps :: (cs ++ (beta :: zeroE :: firsts u)) ∧ w.challenges = cs ++ [beta] := by
  unfold wholeStandIn at h
  replace h := bind_some h
  obtain ⟨p0, G0, u0, h0, h⟩ := h
  obtain ⟨τ, mu, eps, hτ, k0, rfl, rfl⟩ := begin_fl h0
  replace h := bind_some h
  obtain ⟨p1, G1, u1, h1, h⟩ := h
  obtain ⟨rs, hl, hl2, hR, k1, a1, s1, t1⟩ := loop2_fl zs _ p1 _ G1 _ u1 [] [] h1
    (PscRun.ran_begin C τ mu eps F.next)
  replace h := bind_some h
  obtain ⟨⟨sEnd, p2⟩, G2, u2, h2, h⟩ := h
  obtain ⟨sent, v, beta, k2, hs, hv, rfl, hh, rfl⟩ := ends_fl h2
  replace h := bind_some h
  obtain ⟨ends, G3, u3, h3, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := shownLoop _ _ [] ends _ G3 _ u3 h3
  replace h := bind_some h
  obtain ⟨⟨row, p3⟩, G4, u4, h4, h⟩ := h
  obtain ⟨hr, rfl, rfl⟩ := row_fl h4
  cases pure_some h
  refine ⟨eps, beta, rs.map (·.2), by rw [List.length_map, hl], ?_, ?_⟩
  · rw [firsts_key, firsts_key, k0, k1, k2]
    simp only [List.map_cons, List.map_append, List.map_map]
    rfl
  · show (p1.r.push beta).toList = _
    rw [Array.toList_push, hR.r_eq]
    simp

/-- A sumcheck without a variable takes three rounds. -/
theorem whole_three {C : Aff} {dY n : Nat} {endTerm : List E → E} {F G : Fork} {t u : Tape}
    {w : Whole} (h : wholeStandIn C [] dY n endTerm F t = some (w, G, u)) : Cut t u 3 := by
  obtain ⟨eps, beta, cs, hl, e, -⟩ := whole_cut h
  obtain rfl : cs = [] := List.length_eq_zero_iff.1 hl
  exact ⟨[eps, beta, zeroE], e, rfl⟩

/-- **One level**: m + 4 rounds; the point behind it. -/
theorem level_cut {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork} {t u : Tape}
    {o : LevelOut} (ho : order.length = m) (h : level m z order C F t = some (o, G, u)) :
    Cut t u (m + 4) ∧ #[o.xi] ++ o.r = ptL m order (firsts t) 0 := by
  unfold level at h
  replace h := bind_some h
  obtain ⟨w, G3, u3, h3, h⟩ := h
  replace h := bind_some h
  obtain ⟨xi, G4, u4, h4, h⟩ := h
  cases pure_some h
  obtain ⟨eps, beta, cs, hl, e, hc⟩ := whole_cut h3
  rw [List.length_map, ho] at hl
  obtain ⟨wr, rfl, -⟩ := answer_fl h4
  have e' : firsts t = eps :: (cs ++ (beta :: zeroE :: xi :: firsts u)) := e
  refine ⟨⟨eps :: (cs ++ [beta, zeroE, xi]), by rw [e']; simp, by simp [hl]⟩, ?_⟩
  show #[xi] ++ layBack m order (w.challenges.take m) = _
  unfold ptL
  rw [hc, List.take_left' hl, e', Nat.zero_add, Nat.zero_add, List.drop_succ_cons, List.drop_zero,
    List.take_left' hl, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_append_right (by omega), hl]
  have e2 : m + 2 - m = 2 := by omega
  rw [e2]
  rfl

/-- The rounds of n levels, with more + l, more + l + 1, … variables. -/
def Kr (more l n : Nat) : Nat := ((List.range' l n).map fun i => more + i + 4).sum

theorem Kr_succ (more l n : Nat) : Kr more l (n + 1) = (more + l + 4) + Kr more (l + 1) n := by
  unfold Kr
  rw [List.range'_succ, List.map_cons, List.sum_cons]

/-- **A run of levels**: how many rounds; the last level's point. -/
theorem levels_cut (more : Nat) (orders : Nat → List Nat) : ∀ (n l : Nat) (cf cf' : Carried)
    (F G : Fork) (t u : Tape),
    ((List.range' l n).foldlM (m := Fl) (fun s i => turn (orders (more + i)) s (more + i)) cf) F t =
      some (cf', G, u) →
    (∀ i, l ≤ i → i < l + n → (orders (more + i)).length = more + i) →
    Cut t u (Kr more l n) ∧ ∀ k, n = k + 1 →
      cf'.point = ptL (more + (l + k)) (orders (more + (l + k))) (firsts t) (Kr more l k) := by
  intro n
  induction n with
  | zero =>
    intro l cf cf' F G t u h _
    cases pure_some h
    exact ⟨Cut.refl _, fun k hk => by cases hk⟩
  | succ n ih =>
    intro l cf cf' F G t u h ho
    rw [List.range'_succ, List.foldlM_cons] at h
    replace h := bind_some h
    obtain ⟨cf1, G1, u1, h1, h⟩ := h
    unfold turn at h1
    replace h1 := bind_some h1
    obtain ⟨o, G2, u2, h2, h1⟩ := h1
    cases pure_some h1
    obtain ⟨c1, p1⟩ := level_cut (ho l (Nat.le_refl _) (by omega)) h2
    obtain ⟨c2, p2⟩ := ih (l + 1) _ cf' _ G _ u h fun i hi hi' => ho i (by omega) (by omega)
    refine ⟨(c1.trans c2).cast (Kr_succ more l n).symm, fun k hk => ?_⟩
    obtain rfl : n = k := Nat.succ.inj hk
    cases n with
    | zero =>
      cases pure_some h
      exact p1
    | succ j =>
      rw [p2 j rfl, c1.drop, ptL_drop, Kr_succ, show l + 1 + j = l + (j + 1) by omega]

/-! ## 3 The lookup's text up to the parts' trees -/

/-- The rounds in front of part q's tree, from the first tree on. -/
def offK (vs : List Nat) (q : Nat) : Nat := ((vs.take q).map (Kr 0 0)).sum

/-- The rounds in front of the first tree, at a face without a shift. -/
def oKeys (f : Face) : Nat := 1 + 3 * (f.planes - 1) + 3 * (f.parts.length - 1) + 1

theorem tie_loop {β : Type} (g : Array Aff × Nat × Array Nat → β →
    Fl (Array Aff × Nat × Array Nat))
    (hg : ∀ s b F G t u r, g s b F t = some (r, G, u) → Cut t u 3) :
    ∀ (l : List β) (s r : Array Aff × Nat × Array Nat) (F G : Fork) (t u : Tape),
      (l.foldlM (m := Fl) g s) F t = some (r, G, u) → Cut t u (3 * l.length)
  | [], s, r, F, G, t, u, h => by
    cases pure_some h
    exact Cut.refl _
  | b :: l, s, r, F, G, t, u, h => by
    rw [List.foldlM_cons] at h
    replace h := bind_some h
    obtain ⟨s1, G1, u1, h1, h⟩ := h
    exact ((hg _ _ _ _ _ _ _ h1).trans (tie_loop g hg l _ _ _ _ _ _ h)).cast
      (by rw [List.length_cons]; omega)

/-- The tie takes 3 (w - 1) rounds, at two planes at least. -/
theorem tie_cut {w : Nat} {a : E} {F G : Fork} {t u : Tape} {r : Array Aff × Nat × Array Nat}
    (hw : 2 ≤ w) (h : tieG w a F t = some (r, G, u)) : Cut t u (3 * (w - 1)) := by
  unfold tieG at h
  replace h := bind_some h
  obtain ⟨x, G1, u1, h1, h⟩ := h
  replace h := bind_some h
  obtain ⟨s, G2, u2, h2, h⟩ := h
  cases pure_some h
  have c2 := tie_loop _ (fun s b F G t u r hh => by
    replace hh := bind_some hh
    obtain ⟨y, G', u', hy, hh⟩ := hh
    cases pure_some hh
    exact whole_three hy) _ _ _ _ _ _ _ h2
  rw [List.length_range] at c2
  exact ((whole_three h1).trans c2).cast (by omega)

/-- The parts' steps take 3 n rounds. -/
theorem parts_cut : ∀ (n : Nat) (rows : Array Aff) (C : Aff) (F G : Fork) (t u : Tape)
    (r : Array Aff × List Aff), partsG n rows C F t = some (r, G, u) → Cut t u (3 * n)
  | 0, rows, C, F, G, t, u, r, h => by
    cases pure_some h
    exact Cut.refl _
  | n + 1, rows, C, F, G, t, u, r, h => by
    unfold partsG at h
    replace h := bind_some h
    obtain ⟨w, G1, u1, h1, h⟩ := h
    replace h := bind_some h
    obtain ⟨x, G2, u2, h2, h⟩ := h
    cases pure_some h
    exact ((whole_three h1).trans (parts_cut n _ _ _ _ _ _ _ h2)).cast (by omega)

/-- **The parts' key trees: each part's point.** -/
theorem keys_pts (f : Face) : ∀ (vs : List Nat) (i : Nat) (Cs' : List Aff) (rows : Array Aff)
    (F G : Fork) (t u : Tape) (res : Array Aff × List (Array E × Aff)),
    keysG f (vs.zipIdx i) Cs' rows F t = some (res, G, u) →
    (∀ q, q < vs.length → ∀ m, m < vs.getD q 0 → (f.orders (i + q) m).length = m) →
    ∀ q k, q < res.2.length → vs.getD q 0 = k + 1 →
      (res.2.getD q (#[], {})).1 = ptL k (f.orders (i + q) k) (firsts t) (offK vs q + Kr 0 0 k) ∧
        offK vs q + Kr 0 0 (k + 1) ≤ (firsts t).length := by
  intro vs
  induction vs with
  | nil =>
    intro i Cs' rows F G t u res h _
    have h' : (pure (rows, []) : Fl (Array Aff × List (Array E × Aff))) F t = some (res, G, u) := by
      cases Cs' <;> exact h
    cases pure_some h'
    exact fun q k hq => (by cases hq)
  | cons v vs ih =>
    intro i Cs' rows F G t u res h ho
    cases Cs' with
    | nil =>
      have h' : (pure (rows, []) : Fl (Array Aff × List (Array E × Aff))) F t = some (res, G, u) :=
        h
      cases pure_some h'
      exact fun q k hq => (by cases hq)
    | cons C Cs' =>
      rw [List.zipIdx_cons] at h
      unfold keysG at h
      replace h := bind_some h
      obtain ⟨kk, G1, u1, h1, h⟩ := h
      replace h := bind_some h
      obtain ⟨y, G2, u2, h2, h⟩ := h
      cases pure_some h
      unfold VerifiableInference.Desc.First.Prod.run at h1
      rw [List.range_eq_range'] at h1
      obtain ⟨c1, p1⟩ := levels_cut 0 (f.orders i) v 0 _ kk F G1 t u1 h1 fun m _ hm => by
        have := ho 0 (Nat.succ_pos _) m (by simpa using hm)
        simpa using this
      have r2 := ih (i + 1) Cs' kk.rows G1 _ u1 _ y h2 fun q hq m hm => by
        have := ho (q + 1) (Nat.succ_lt_succ hq) m (by simpa using hm)
        rwa [show i + (q + 1) = i + 1 + q by omega] at this
      intro q k hq hk
      cases q with
      | zero =>
        have hv : v = k + 1 := hk
        refine ⟨?_, ?_⟩
        · show kk.point = _
          rw [p1 k hv]
          simp [offK]
        · have := c1.le
          rw [hv] at this
          simpa [offK] using this
      | succ q =>
        obtain ⟨a, b⟩ := r2 q k (by simpa using hq) (by simpa using hk)
        have eo : offK (v :: vs) (q + 1) = Kr 0 0 v + offK vs q := by
          unfold offK
          rw [List.take_succ_cons, List.map_cons, List.sum_cons]
        refine ⟨?_, ?_⟩
        · show (y.2.getD q (#[], {})).1 = _
          rw [a, c1.drop, ptL_drop, eo, show i + 1 + q = i + (q + 1) by omega, Nat.add_assoc]
        · rw [c1.drop, List.length_drop] at b
          have := c1.le
          rw [eo]
          omega

/-- What the verifier's tests on a face say of the orders. -/
theorem orders_len {f : Face} (hok : f.ok = true) (q : Nat) (hq : q < f.parts.length) (m : Nat)
    (hm : m < f.parts.getD q 0) : (f.orders q m).length = m := by
  unfold Face.ok at hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  have h := hok.2 (f.parts.getD q 0, q) (by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq])
  unfold VerifiableInference.Desc.First.Prod.runOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have h' := h.2 m hm
  rw [Nat.zero_add] at h'
  exact (orderOk_spec h').1

theorem planes_two {f : Face} (hok : f.ok = true) : 2 ≤ f.planes := by
  unfold Face.ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1.1.1.1.1.1.2

theorem answer_cut {r : RoundName} {F G : Fork} {t u : Tape} {x : E}
    (h : Fl.answer r F t = some (x, G, u)) : Cut t u 1 := by
  obtain ⟨wr, rfl, -⟩ := answer_fl h
  exact ⟨[x], rfl, rfl⟩

theorem point_cut {r : RoundName} {n : Nat} {F G : Fork} {t u : Tape} {x : Array E}
    (h : Fl.point r n F t = some (x, G, u)) : Cut t u 1 := by
  obtain ⟨wr, rfl, -, -⟩ := point_fl h
  exact ⟨[x.toList.headD zeroE], rfl, rfl⟩

/-- **THE TEXT.** -/
theorem messages_pts {f : Face} {F G : Fork} {t u : Tape} {g : HeardG} (hs : f.shifted = false)
    (hok : f.ok = true) (h : messagesG f F t = some (g, G, u)) :
    ∀ q k, q < f.parts.length → f.parts.getD q 0 = k + 1 →
      (g.keys.getD q (#[], {})).1 =
          ptL k (f.orders q k) (firsts t) (oKeys f + offK f.parts q + Kr 0 0 k) ∧
        oKeys f + offK f.parts q + Kr 0 0 (k + 1) ≤ (firsts t).length := by
  unfold messagesG at h
  rw [hs] at h
  replace h := bind_some h
  obtain ⟨slot0, F0, t0, e0, h⟩ := h
  replace e0 := slot_some e0
  obtain ⟨rfl, rfl, rfl⟩ := e0
  replace h := bind_some h
  obtain ⟨w1, F1, t1, e1, h⟩ := h
  replace e1 := owe_some e1
  obtain ⟨rfl, rfl⟩ := e1
  replace h := bind_some h
  obtain ⟨w2, F2, t2, e2, h⟩ := h
  replace e2 := owe_some e2
  obtain ⟨rfl, rfl⟩ := e2
  replace h := bind_some h
  obtain ⟨w3, F3, t3, e3, h⟩ := h
  replace e3 := owe_some e3
  obtain ⟨rfl, rfl⟩ := e3
  replace h := bind_some h
  obtain ⟨theta, F4, t4, e4, h⟩ := h
  cases pure_some e4
  replace h := bind_some h
  obtain ⟨alpha, F5, t5, e5, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows1, sZ, sG⟩, F6, t6, e6, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows2, roots⟩, F7, t7, e7, h⟩ := h
  replace h := bind_some h
  obtain ⟨x3, F8, t8, e8, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨rows3, keys⟩, F9, t9, e9, h⟩ := h
  replace h := bind_some h
  obtain ⟨_, F10, t10, e10, h⟩ := h
  replace e10 := must_some e10
  obtain ⟨hk, rfl, rfl⟩ := e10
  replace h := bind_some h
  obtain ⟨table, F11, t11, e11, h⟩ := h
  replace h := bind_some h
  obtain ⟨_, F12, t12, e12, h⟩ := h
  replace e12 := must_some e12
  obtain ⟨-, rfl, rfl⟩ := e12
  replace h := bind_some h
  obtain ⟨lv0, F13, t13, e13, h⟩ := h
  replace h := bind_some h
  obtain ⟨⟨zb0, lv⟩, F14, t14, e14, h⟩ := h
  replace h := bind_some h
  obtain ⟨x5, F15, t15, e15, h⟩ := h
  replace h := bind_some h
  obtain ⟨bits, F16, t16, e16, h⟩ := h
  replace h := bind_some h
  obtain ⟨sl, F17, t17, e17, h⟩ := h
  replace e17 := slot_some e17
  obtain ⟨rfl, rfl, rfl⟩ := e17
  replace h := bind_some h
  obtain ⟨_, F18, t18, e18, h⟩ := h
  replace e18 := must_some e18
  obtain ⟨hmust, rfl, rfl⟩ := e18
  cases pure_some h
  have hk' : keys.length = f.parts.length := by simpa using hk
  have c := (((answer_cut e5).trans (tie_cut (planes_two hok) e6)).trans
    (parts_cut _ _ _ _ _ _ _ _ e7)).trans (point_cut e8)
  have c : Cut _ t8 (oKeys f) := c
  intro q k hq hv
  obtain ⟨a, b⟩ := keys_pts f f.parts 0 roots rows2 _ _ _ _ _ e9
    (fun q hq m hm => by rw [Nat.zero_add]; exact orders_len hok q hq m hm) q k
    (by rw [hk']; exact hq) hv
  refine ⟨?_, ?_⟩
  · show (keys.getD q (#[], {})).1 = _
    rw [a, c.drop, ptL_drop, Nat.zero_add, Nat.add_assoc]
  · rw [c.drop, List.length_drop] at b
    have := c.le
    omega

/-! ## 4 On rounds -/

open ProofFile.Honest.K3 (e1 one seg)

/-- The strict tape's first samples are the rounds'. -/
theorem tape_firsts : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    VerifiableInference.Desc.First.Tape.tapeT {} rs es = some t → firsts t = rs.map e1
  | [], [], t, h => by
    cases h
    rfl
  | [], _ :: _, t, h => by cases h
  | _ :: _, [], t, h => by cases h
  | r :: rs, e :: es, t, h => by
    unfold VerifiableInference.Desc.First.Tape.tapeT at h
    cases h1 : VerifiableInference.Desc.First.Tape.roundT {} r e with
    | none => rw [h1] at h; cases h
    | some x =>
      cases h2 : VerifiableInference.Desc.First.Tape.tapeT {} rs es with
      | none => rw [h1, h2] at h; cases h
      | some t' =>
        rw [h1, h2] at h
        cases h
        have ih := tape_firsts rs es t' h2
        unfold VerifiableInference.Desc.First.Tape.roundT at h1
        cases h3 : VerifiableInference.Desc.First.Tape.elemsOf r.vals with
        | none => rw [h3] at h1; cases h1
        | some sent =>
          rw [h3] at h1
          dsimp only at h1
          split at h1
          · cases h1
            show (r.drawn.elems.map E.ofTriple).headD zeroE :: firsts t' = e1 r :: rs.map e1
            rw [ih]
            rfl
          · cases h1

/-- **A hearing that returns: each part's key point, of the rounds' first samples by number.** -/
theorem heard_pts {f : Face} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardG}
    (hs : f.shifted = false) (h : hearE f es F rs = some (g, G)) :
    ∀ q k, q < f.parts.length → f.parts.getD q 0 = k + 1 →
      (g.keys.getD q (#[], {})).1 = ProofFile.Honest.K3.behind k (f.orders q k)
          (seg rs (oKeys f + offK f.parts q + Kr 0 0 k + 1) k)
          (one rs (oKeys f + offK f.parts q + Kr 0 0 k + k + 3)) ∧
        oKeys f + offK f.parts q + Kr 0 0 (k + 1) ≤ rs.length := by
  obtain ⟨hok, t, ht, hm⟩ := hearE_inv h
  intro q k hq hv
  obtain ⟨a, b⟩ := messages_pts hs hok hm q k hq hv
  rw [tape_firsts rs es t ht] at a b
  exact ⟨a, by simpa using b⟩

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.whole_cut
#print axioms AtPublicFiles.FirstH.Lots.level_cut
#print axioms AtPublicFiles.FirstH.Lots.levels_cut
#print axioms AtPublicFiles.FirstH.Lots.keys_pts
#print axioms AtPublicFiles.FirstH.Lots.messages_pts
#print axioms AtPublicFiles.FirstH.Lots.heard_pts
