-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscToken.lean: the token sumcheck (OnBytes/Model/Tsc.lean) on a run:
tscRounds and tscIn, in the records of PscSeam.lean in this folder.

Main names:
  `tokenWeights`, `tokenWeights_length`, `tokenWeights_sizes`, `hidingEntries_token`: the weights of
    the rounds and their numbers.
  `publicPart_slot_word`: the public part of the form of one slot, as the exact word.
  `tscRounds_seam`: the one rider, the beginning and the rounds, for callers that go on with rounds
    of their own: what was heard, Ran, the fields of Tsc, the state.
  `tscIn_seam`: the token sumcheck whole, with the end values: Parts, Ended, the sizes, the fields
    of Tsc, two fillings of the state.
Limits: one direction only, from a success of the model's routine. No statement has a hypothesis on
whether the channel is a view or the dry run. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscSeam

set_option autoImplicit false

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany hear claimAfter polyAt hidingWalk hidingEntries)

/-- The weights of the token sumcheck's rounds. -/
def tokenWeights (P : Array E) (lt : Nat) : List Weight :=
  (P.toList.take lt).map fun z => Weight.equality z 3

theorem tokenWeights_length (P : Array E) (lt : Nat) (h : lt ≤ P.size) :
    (tokenWeights P lt).length = lt := by
  unfold tokenWeights
  rw [List.length_map, List.length_take, Array.length_toList]; omega

theorem tokenWeights_sizes (P : Array E) (lt : Nat) :
    (tokenWeights P lt).map (fun w => w.d - 1) = (P.toList.take lt).map fun _ => 2 := by
  unfold tokenWeights
  rw [List.map_map]; rfl

theorem hidingEntries_token (P : Array E) (lt dY : Nat) (h : lt ≤ P.size) :
    hidingEntries (tokenWeights P lt ++ [Weight.atZero (dY + 1)]) = 1 + 2 * lt + dY := by
  unfold hidingEntries
  rw [List.map_append, tokenWeights_sizes, List.sum_append]
  have h2 : (List.map (fun w : Weight => w.d - 1) [Weight.atZero (dY + 1)]).sum = dY := by
    simp [Weight.atZero, Weight.equality]
  rw [h2, List.map_const', List.sum_replicate, List.length_take, Array.length_toList]
  simp only [smul_eq_mul]
  have : min lt P.size = lt := by omega
  rw [this]; omega

/-- The public part of "the hidden value under one slot", as the exact word. -/
theorem publicPart_slot_word (G : Fork) (j : Nat) (y τ : E) (hy : G.shown j = some y)
    (h : G.publicPart (Aff.slot j) = some τ) : τ = addE zeroE (mulE oneE y) := by
  unfold Fork.publicPart Aff.slot at h
  simp only [← Array.foldlM_toList, List.foldlM_cons, List.foldlM_nil, hy, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
  exact h.symm

/-- The rider, the beginning and the rounds of the token sumcheck. x: the shown scalar of Cl. -/
theorem tscRounds_seam (P : Array E) (lt : Nat) (F G : Fork) (c c' : Ctx) (t : Tsc)
    (h : tscRounds P lt F c = .ok ((t, G), c')) (hs : Sized F) :
    ∃ (x mu : E) (rs : List (List E × E)) (F1 : Fork) (c1 c2 : Ctx),
      (Blk.recvEs 1).Yields c [x] c1 ∧
      (hearOne "PSC epsilon" .join 1 0).Yields c1 ([mu], t.p.eps) c2 ∧
      (hearMany ((tokenWeights P lt).map fun w => w.d - 1)).Yields c2 rs c' ∧
      lt ≤ P.size ∧ rs.length = lt ∧
      Ran t.p (Aff.slot F.next) (addE zeroE (mulE oneE x)) mu t.p.eps (F.next + 1) (tokenWeights P
          lt) rs ∧
      t.sCl = F.next ∧ t.sEnd = 0 ∧ t.r.toList = rs.map (·.2) ∧ t.rowU = {} ∧
      Filled (taken F 1) F1 F.next [x] oneE ∧ G = taken F1 (1 + 2 * lt) := by
  unfold tscRounds at h
  obtain ⟨_, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨ba, ea1, ea2⟩ := (must_ok _ _ _ _ _ _).1 ha
  rw [ea1, ea2] at ka
  obtain ⟨sCl, Fb, cb, hb, kb⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨rider, yb, sb, jb, Hb⟩ := claimsIn_ok 1 F Fb c cb sCl hb
  obtain ⟨p0, Fc, cc, hc, kc⟩ := (bind_ok _ _ _ _ _).1 kb
  obtain ⟨τ, mu, pc, yc, hp0, Gc⟩ := pscBegin_ok _ Fb Fc cb cc p0 hc
  obtain ⟨⟨r1, p1⟩, Fd, cd, hd, kd⟩ := (bind_ok _ _ _ _ _).1 kc
  obtain ⟨rs, yd, sd, rd1, Gd⟩ := tscLoop_ok _ _ _ _ _ _ _ _ _ hd
  obtain ⟨ee1, ee2, ee3⟩ := (pure_ok _ _ _ _ _ _).1 kd
  rw [jb] at pc hp0
  have hlt : lt ≤ P.size := by simpa using ba
  have hlen : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]; omega
  obtain ⟨x, hx⟩ : ∃ x, rider.toList = [x] := by
    have : rider.toList.length = 1 := by simpa using sb
    cases hr : rider.toList with
    | nil => rw [hr] at this; simp at this
    | cons a l =>
      cases l with
      | nil => exact ⟨a, rfl⟩
      | cons b l' => rw [hr] at this; simp at this
  have fb : Filled (taken F 1) Fb F.next [x] oneE := by
    rw [← hx]; exact hideRun_ok _ _ _ _ _ Hb (sized_taken F 1 hs)
  have nb : Fb.next = F.next + 1 := by rw [fb.next]; rfl
  have shx : Fb.shown F.next = some x := by
    have := fb.shown 0 (by simp)
    simpa using this
  have hτ : τ = addE zeroE (mulE oneE x) := publicPart_slot_word Fb F.next x τ shx pc
  have tp : t.p = p1 := by rw [ee1]
  have ran : Ran p1 (Aff.slot F.next) τ mu p0.eps Fb.next (tokenWeights P lt) rs := by
    have := (Ran.begun p0 _ τ mu Fb.next hp0).step sd
    rw [List.nil_append, List.nil_append] at this
    exact this
  have he : p1.eps = p0.eps := ran.eps
  rw [hx] at yb
  refine ⟨x, mu, rs, Fb, cb, cc, yb, by rw [tp, he]; exact yc, ?_, hlt, ?_, ?_, ?_, ?_, ?_, ?_, fb,
      ?_⟩
  · rw [tokenWeights_sizes, ee3]; exact yd
  · rw [sd.len, List.length_map, hlen]
  · rw [tp, he, ← hτ, ← nb]; exact ran
  · rw [ee1]; exact jb
  · rw [ee1]
  · rw [ee1]; show r1.toList = _; rw [rd1]; rfl
  · rw [ee1]
  · rw [ee2, Gd, Gc, taken_taken, hlen]

/-- The token sumcheck, whole. -/
theorem tscIn_seam (P : Array E) (lt shown degreeInY : Nat) (F G : Fork) (c c' : Ctx) (t : Tsc)
    (h : tscIn P lt shown degreeInY F c = .ok ((t, G), c')) (hs : Sized F) :
    ∃ (x mu : E) (rs : List (List E × E)) (sentY : List E) (beta : E) (v : List E) (F1 : Fork) (c1 :
        Ctx),
      Parts c c1 c' [x] mu t.p.eps (tokenWeights P lt) rs degreeInY sentY beta v ∧
      lt ≤ P.size ∧ rs.length = lt ∧ (∀ y ∈ (tokenWeights P lt).zip rs, y.2.1.length + 1 = y.1.d) ∧
      (∀ w ∈ tokenWeights P lt, w.fits = true) ∧
      sentY.length = degreeInY ∧ v.length = shown ∧ 1 ≤ degreeInY ∧ 1 ≤ shown ∧
      Ended t.p (Aff.slot F.next) (addE zeroE (mulE oneE x)) mu t.p.eps (F.next + 1) (tokenWeights P
          lt) rs
        degreeInY sentY beta ∧
      t.sCl = F.next ∧ t.r.toList = rs.map (·.2) ∧ t.rowU = {} ∧
      t.sEnd = t.p.first + hidingEntries (tokenWeights P lt ++ [Weight.atZero (degreeInY + 1)]) ∧
      Filled (taken F 1) F1 F.next [x] oneE ∧
      Filled (taken F1 (1 + 2 * lt + degreeInY + shown)) G t.sEnd v beta := by
  unfold tscIn at h
  obtain ⟨o1, F2, c2, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨⟨sEnd, p2⟩, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k3
  obtain ⟨x, mu, rs, F1, d1, d2, y0, y1, y2, hlt, hl, ran, a1, _, a3, a4, fb, hF2⟩ :=
    tscRounds_seam P lt F F2 c c2 o1 h1 hs
  obtain ⟨sentY, beta, v, c5, c6, y5, y6, y7, sv, dd, nn, _, sY, hp2, hE, HG⟩ :=
    pscEnds_ok o1.p p2 degreeInY shown F2 F3 c2 c3 sEnd h3
  have en := ran.ends degreeInY sentY beta hp2
  have tp : t.p = p2 := by rw [e1]
  have lv : v.toList.length = shown := by simpa using sv
  have fG : Filled (taken F1 (1 + 2 * lt + degreeInY + shown)) F3 sEnd v.toList beta := by
    have := hideRun_ok _ _ _ _ _ HG (sized_taken F2 _
        (by rw [hF2]; exact sized_taken F1 _ fb.sized))
    rw [hF2, taken_taken, ← Nat.add_assoc] at this
    exact this
  have nb : F1.next = F.next + 1 := by rw [fb.next]; rfl
  have he : p2.eps = o1.p.eps := en.eps
  refine ⟨x, mu, rs, sentY, beta, v.toList, F1, d1, ⟨d2, c2, c5, c6, y0, by rw [tp, he]; exact y1,
      y2, y5,
    by rw [lv]; exact y6, by rw [e3]; exact y7⟩, hlt, hl, ran.sizes, fun w hw => (ran.held w hw).1,
        sY, lv, dd,
    nn, by rw [tp, he]; exact en, ?_, ?_, ?_, ?_, fb, ?_⟩
  · rw [e1]; exact a1
  · rw [e1]; exact a3
  · rw [e1]; exact a4
  · rw [tp, en.first, hidingEntries_token P lt degreeInY hlt, e1]
    show sEnd = _
    rw [hE, hF2]
    show F1.next + (1 + 2 * lt) + degreeInY = _
    rw [nb]; omega
  · rw [e2, e1]; exact fG

#print axioms tscRounds_seam
#print axioms tscIn_seam

end OnBytes.Model.Road
