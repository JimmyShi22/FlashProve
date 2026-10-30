-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/TotalB.lean: THE HEARING RETURNS: at a face without a shift that
passes its tests, from a ledger that is ready, on every stretch that the strict reading takes and
that has the lookup's shape, the kind's hearing hears, and the run "planes" behind it closes the
leaves' sumcheck. With it the two statements of Statement.lean are theorems of the kind's own
hearing.

Main names:
  keys_ok, loopEq_ok, join_shown, planes_ok, go_start: the pieces left.
  messages_ok: messagesG returns, and planesG behind it.
  total_hearE: Law.total of hearE (Rounds.hears is drawn from it inside K03key_rounds).
  K03key_rounds : Rounds hearE. K03key_law : Law hearE.

Limits. See Statement.lean.

-/
import Johnson.Desc.First.Look.KeyLaw.TotalA
import Johnson.Desc.First.Look.KeyLaw.Out

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm eqTab orderDefault)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole Carried turn)

variable {T : ℕ}

theorem keys_ok (f : Face) : ∀ (vs : List ℕ) (i : ℕ) (Cs' : List Aff) (rows : Array Aff) (F : Fork)
    (t : Tape) (pat : List Bool) (L : List Shape),
    Go T F t (keysPat vs ++ pat) (keysShape vs ++ L) → Cs'.length = vs.length →
    (∀ c ∈ Cs', AllShown F c) →
    (∀ q < vs.length, ∀ j < vs.getD q 0, (f.orders (i + q) j).length = j) →
    ∃ res G u, keysG f (vs.zipIdx i) Cs' rows F t = some (res, G, u) ∧ Go T G u pat L ∧ Later F G ∧
      res.1.size = rows.size + vs.sum ∧ res.2.length = vs.length := by
  intro vs
  induction vs with
  | nil =>
    intro i Cs' rows F t pat L h hl _ _
    obtain rfl : Cs' = [] := List.length_eq_zero_iff.1 hl
    exact ⟨(rows, []), F, t, rfl, h, Later.refl _, rfl, rfl⟩
  | cons v vs ih =>
    intro i Cs' rows F t pat L h hl hC ho
    cases Cs' with
    | nil => simp at hl
    | cons C Cs' =>
      have h' : Go T F t (levelsPat true 0 v 0 ++ (keysPat vs ++ pat))
          (levelsShape 0 v 0 ++ (keysShape vs ++ L)) := by
        have e1 : keysPat (v :: vs) ++ pat = levelsPat true 0 v 0 ++ (keysPat vs ++ pat) := by
          show (levelsPat true 0 v 0 ++ keysPat vs) ++ pat = _
          rw [List.append_assoc]
        have e2 : keysShape (v :: vs) ++ L = levelsShape 0 v 0 ++ (keysShape vs ++ L) := by
          show (levelsShape 0 v 0 ++ keysShape vs) ++ L = _
          rw [List.append_assoc]
        rw [e1, e2] at h
        exact h
      obtain ⟨k, G1, u1, e, g1, g2, -, g4, -⟩ := levels_ok true 0 (f.orders i) v 0
        { rows := rows, point := #[], form := C } F t _ _ h' (hC C List.mem_cons_self)
        (fun j _ h2 => by
          have := ho 0 (by simp) j (by simpa using h2)
          rw [Nat.add_zero] at this
          rw [Nat.zero_add]
          exact this) rfl
      obtain ⟨y, G, u, e', r1, r2, r3, r4⟩ := ih (i + 1) Cs' k.rows G1 u1 pat L g1
        (by simpa using hl) (fun c hc => (hC c (List.mem_cons_of_mem _ hc)).later g2)
        (fun q hq j hj => by
          have := ho (q + 1) (by simpa using hq) j (by simpa using hj)
          rwa [show i + (q + 1) = i + 1 + q by omega] at this)
      refine ⟨(y.1, (k.point, k.form) :: y.2), G, u, ?_, r1, g2.trans r2, ?_, by simp [r4]⟩
      · rw [List.zipIdx_cons]
        unfold keysG
        have er : First.Prod.run 0 v (f.orders i) { rows := rows, point := #[], form := C } F t =
            some (k, G1, u1) := by
          unfold First.Prod.run
          rw [List.range_eq_range']
          exact e
        rw [bind_eq er, bind_eq e']
        rfl
      · rw [r3, g4, List.sum_cons]
        show rows.size + v + vs.sum = _
        omega

theorem loopEq_ok (zs : List (E × ℕ)) : ∀ (x : Array E × Psc) (F : Fork) (t : Tape)
    (L : List Shape), x.2.ended = false →
    (∀ z ∈ zs, RoundForm.eq.weight z.1 z.2 = some (OnBytes.Psc.Weight.equality z.1 (z.2 + 1)) ∧
      1 ≤ z.2) →
    t.map shapeOf = (zs.map (·.2)).map (fun g => (RoundName.pscRound.name, g, 1, 0)) ++ L →
    ∃ x' u, (zs.foldlM (m := Fl) (fun (s : Array E × Psc) z => do
        let (r, q) ← Fl.roundIn .eq s.2 z.1 z.2
        pure (s.1.push r, q)) x) F t = some (x', took F (zs.map (·.2)).sum, u) ∧
      u.map shapeOf = L ∧ x'.2.ended = false ∧ x'.2.rowMade = x.2.rowMade ∧
      x'.2.started = x.2.started := by
  induction zs with
  | nil =>
    intro x F t L he _ h
    exact ⟨x, t, rfl, h, he, rfl, rfl⟩
  | cons z zs ih =>
    intro x F t L he hw h
    obtain ⟨hw1, hw2⟩ := hw z List.mem_cons_self
    obtain ⟨sent, r, u, e, hu, -⟩ := pscRound_ok (p := x.2)
      (w := OnBytes.Psc.Weight.equality z.1 (z.2 + 1)) (name := .pscRound) (nz := 0) (F := F)
      (by decide) ((PscRun.fits_equality z.1 (z.2 + 1)).2 (by omega))
      (PscRun.weightHeld_equality z.1 (z.2 + 1)) h (Nat.le_add_left 1 z.2)
    have hd : (OnBytes.Psc.Weight.equality z.1 (z.2 + 1)).d - 1 = z.2 := Nat.add_sub_cancel z.2 1
    rw [hd] at e
    obtain ⟨q, hq⟩ : ∃ q : Psc, q = { x.2 with
        claim := OnBytes.Psc.polyAt
          ((OnBytes.Psc.Weight.equality z.1 (z.2 + 1)).complete sent.toList x.2.claim) r,
        vars := x.2.vars.push (OnBytes.Psc.Weight.equality z.1 (z.2 + 1)),
        r := x.2.r.push r } := ⟨_, rfl⟩
    rw [← hq] at e
    have q1 : q.ended = false := by rw [hq]; exact he
    have q2 : q.rowMade = x.2.rowMade := by rw [hq]
    have q3 : q.started = x.2.started := by rw [hq]
    have er : Fl.roundIn .eq x.2 z.1 z.2 F t = some ((r, q), took F z.2, u) := by
      unfold Fl.roundIn
      rw [bind_eq (must_ok (by rw [he]; rfl) F t),
        bind_eq (a := OnBytes.Psc.Weight.equality z.1 (z.2 + 1)) (G := F) (u := t) (by
          show Fl.need (RoundForm.eq.weight z.1 z.2) F t = _
          rw [hw1]; rfl)]
      exact e
    obtain ⟨x', u', e', h1, h2, h3, h4⟩ := ih (x.1.push r, q) (took F z.2) u L q1
      (fun y hy => hw y (List.mem_cons_of_mem _ hy)) hu
    have h3' : x'.2.rowMade = q.rowMade := h3
    have h4' : x'.2.started = q.started := h4
    refine ⟨x', u', ?_, h1, h2, h3'.trans q2, h4'.trans q3⟩
    rw [List.foldlM_cons, bind_eq (bind_eq er)]
    rw [took_took] at e'
    exact e'

/-- The state of a sumcheck that has begun. -/
def pscStart (C : Aff) (τ : E) (slot : ℕ) (mu eps : E) : Psc :=
  { start := C, started := true, target := τ, first := slot, eps := eps,
    claim := addE mu (mulE eps τ) }

theorem join_shown {F : Fork} {pl : ℕ} {sG : Array ℕ} {ej : Array E}
    (hp : ∀ j < pl, AllShown F (Aff.slot (sG.getD j 0))) : ∀ (js : List ℕ) (a : Aff),
    AllShown F a →
    AllShown F (js.foldl (fun (c : Aff) j =>
      if j < pl then Aff.addMul c (Aff.slot (sG.getD j 0)) (ej.getD j zeroE)
      else c + Aff.ofConst (ej.getD j zeroE)) a)
  | [], a, h => h
  | j :: js, a, h => by
    rw [List.foldl_cons]
    refine join_shown hp js _ ?_
    split
    · rename_i hj
      exact h.addMul (hp j hj) _
    · exact h.add (allShown_const F _)


theorem planes_ok (f : Face) (g : HeardG) (F G' : Fork) (x : Aff × Psc)
    (h : Fl.pscRow g.leaves oneE {} F [] = some (x, G', [])) :
    ∃ pl, planesG f g F [] = some (pl, G', []) := by
  unfold planesG
  rw [bind_eq h]
  exact ⟨_, rfl⟩

/-- A ledger that is ready has the pattern's slots free ahead, also behind the three debts. -/
theorem go_start {f : Face} {first : ℕ} {F : Fork} {t : Tape} (hR : Ready f first F)
    (hsh : t.map shapeOf = shapeG f) :
    Go (first + f.slots) (owed3 F) t (fromKeys f) (shapeG f) := by
  refine ⟨⟨hR.sized, ?_, ?_⟩, ?_, hsh⟩
  · rw [fromKeys_length]
    show F.next + f.slots ≤ F.ns
    rw [hR.next]
    exact hR.room
  · intro j h1 h2
    rw [fromKeys_length] at h2
    have h1' : first ≤ j := hR.next ▸ h1
    have h2' : j < first + f.slots := hR.next ▸ h2
    have hf := hR.free (j - first) (by omega)
    rw [show first + (j - first) = j by omega] at hf
    have hj : j < F.gotF.size := by
      rw [hR.sized.2.2]
      have := hR.room
      omega
    show ¬ F.gotF.getD j false = true
    have e : F.gotF.getD j false = F.gotF.getD j true := by
      simp [Array.getD_eq_getD_getElem?, hj]
    rw [e, hf]
    simp
  · rw [fromKeys_length]
    show F.next + f.slots = _
    rw [hR.next]

set_option maxHeartbeats 1000000 in
/-- **The hearing returns, and "planes" behind it.** -/
theorem messages_ok {f : Face} {first : ℕ} {F : Fork} {t : Tape} (hs : f.shifted = false)
    (hok : f.ok = true) (hR : Ready f first F) (hsh : t.map shapeOf = shapeG f) :
    ∃ g G pl G', messagesG f F t = some (g, G, []) ∧ planesG f g G [] = some (pl, G', []) := by
  have hok' := hok
  unfold Face.ok at hok'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨k1, -⟩, k3⟩, -⟩, k5⟩, -⟩, -⟩, -⟩, -⟩ := hok'
  have hlen1 : 1 ≤ f.parts.length := by
    cases hp : f.parts with
    | nil => rw [hp] at k5; simp at k5
    | cons _ _ => simp
  have g0 := go_start hR hsh
  rw [fromKeys_cut, shape_cut] at g0
  obtain ⟨alpha, t5, e5, g5⟩ := go_answer (by decide) g0
  obtain ⟨r6, F6, t6, e6, g6, l6, z6, a6, b6⟩ := tie_ok (a := f.factor zeroE alpha) k3 g5
  obtain ⟨r7, F7, t7, e7, g7, l7, z7, y7, a7⟩ := parts_ok (f.parts.length - 1) r6.1
    (Aff.slot r6.2.1) F6 t6 _ _ g6 a6
  obtain ⟨x3, t8, e8, g8⟩ := go_point (by decide) g7
  obtain ⟨-, -, hx3, -⟩ := point_fl e8
  obtain ⟨r9, F9, t9, e9, g9, l9, z9, y9⟩ := keys_ok f f.parts 0 r7.2 r7.1 F7 t8 _ _ g8
    (by rw [y7]; omega) a7
    (fun q hq j hj => by
      rw [Nat.zero_add]
      exact (orderOk_spec (ok_orders hok q hq j hj)).1)
  have hjoin : AllShown F9 (joinAff f r6.2.2 x3) :=
    (join_shown (fun j hj => (b6 j hj).later l7) _ _ (allShown_const F7 zeroE)).later l9
  obtain ⟨table, F11, t11, e11, g11, l11, a11, z11, p11⟩ := levels_ok false f.mu orderDefault f.d 0
    { rows := r9.1, point := x3.reverse, form := joinAff f r6.2.2 x3 } F9 t9 _ _ g9 hjoin
    (fun i _ _ => by simp [orderDefault]) (by simp [hx3])
  -- the leaves' sumcheck
  have g11sh := g11.sh
  have g11sh' : t11.map shapeOf = (RoundName.pscEpsilon.name, 1, 1, 0) ::
      ((((List.range (f.mu + f.d)).map fun j =>
          (table.point.getD j zeroE, if j < f.d then 2 else 1)).map (·.2)).map
          (fun g => (RoundName.pscRound.name, g, 1, 0)) ++
        ([(RoundName.zero.name, 0, f.mu + f.d, 0)] ++
          pscShape (List.replicate (f.mu + f.d) 2) (some (2, 1)))) := by
    rw [g11sh, List.map_map]
    simp [pscShape, Function.comp_def]
  obtain ⟨τ, mu, eps, t13, e13, s13⟩ := begin_ok a11 g11sh'
  have e13' : Fl.pscBegin table.form F11 t11 =
      some (pscStart table.form τ F11.next mu eps, took F11 1, t13) := e13
  obtain ⟨x14, t14, e14, s14, f1, f2, f3⟩ := loopEq_ok ((List.range (f.mu + f.d)).map fun j =>
      (table.point.getD j zeroE, if j < f.d then 2 else 1))
    ((#[] : Array E), pscStart table.form τ F11.next mu eps) (took F11 1) t13 _ rfl
    (fun z hz => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz
      by_cases hj : j < f.d
      · simp only [hj, if_true]
        exact ⟨rfl, by decide⟩
      · simp only [hj, if_false]
        exact ⟨rfl, by decide⟩) s13
  obtain ⟨rs, -, -, hRan, -, -, -, -, -⟩ := loopEq_fl _ _ x14 _ _ _ t14 [] [] e14
    (PscRun.ran_begin table.form τ mu eps F11.next)
  have hsum : (((List.range (f.mu + f.d)).map fun j =>
      (table.point.getD j zeroE, if j < f.d then 2 else 1)).map (·.2)).sum = 2 * f.d + f.mu := by
    rw [List.map_map]
    exact degs_sum f.mu f.d
  rw [hsum] at e14
  have hne : (List.range (f.mu + f.d)) ≠ [] := by
    intro h0
    have := congrArg List.length h0
    simp at this
    omega
  have hwl := ran_walk_len hRan (by simpa using hne) (fun x hx => by
    rw [List.nil_append] at hx
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
    exact Nat.le_add_left 1 z.2)
  have hwl' : x14.2.walk.1.length = 1 + (2 * f.d + f.mu) := by
    rw [hwl, List.nil_append, List.map_map, ← hsum]
    rfl
  obtain ⟨hz1, hz2⟩ := ran_sizes hRan
  -- the ledger behind the leaves' rounds
  have g14 : Go (first + f.slots) (took (took F11 1) (2 * f.d + f.mu)) t14
      (own (1 + 2 * (f.mu + f.d) + 2 + 1) ++ [])
      ([(RoundName.zero.name, 0, f.mu + f.d, 0)] ++
        (pscShape (List.replicate (f.mu + f.d) 2) (some (2, 1)) ++ [])) := by
    have hfr := g11.fr
    have htot := g11.tot
    rw [List.length_append, own_length] at hfr htot
    refine ⟨⟨hfr.sized, ?_, fun j h1 h2 => hfr.free j ?_ ?_⟩, ?_, by rw [s14, List.append_nil]⟩
    · have := hfr.room
      show F11.next + 1 + (2 * f.d + f.mu) + _ ≤ F11.ns
      omega
    · have h1' : F11.next + 1 + (2 * f.d + f.mu) ≤ j := h1
      omega
    · have h2' : j < F11.next + 1 + (2 * f.d + f.mu) + _ := h2
      omega
    · show F11.next + 1 + (2 * f.d + f.mu) + _ = _
      omega
  obtain ⟨x5, t15, e15, g15⟩ := go_point (by decide) g14
  obtain ⟨-, -, hx5, -⟩ := point_fl e15
  have hx5l : x5.reverse.toList.length = f.mu + f.d := by simp [hx5]
  obtain ⟨bits, G, u, e16, g16, l16, -, low16, -⟩ := go_whole (zs := x5.reverse.toList)
    (endTerm := fun x => subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE))
    (by rw [hx5l]; exact own_length _) (by rw [hx5l]; exact g15)
    (allShown_const _ zeroE) (by decide) (by decide)
  obtain rfl : u = [] := List.map_eq_nil_iff.1 g16.sh
  -- "planes"
  have hfr11 := g11.fr
  rw [List.length_append, own_length] at hfr11
  obtain ⟨G', hG'⟩ := hideRun_some (F := G) (first := F11.next)
    (v := Array.replicate (1 + (2 * f.d + f.mu)) zeroE) g16.fr.sized
    (by
      rw [Array.size_replicate, l16.ns]
      have := hfr11.room
      show _ ≤ F11.ns
      omega)
    (fun i hi => by
      rw [Array.size_replicate] at hi
      rw [low16 (F11.next + i) (by
        show _ < F11.next + 1 + (2 * f.d + f.mu)
        omega)]
      exact hfr11.free _ (by omega) (by omega)) (subE zeroE oneE)
  have erow := row_ok (S0 := oneE) (kept := {}) (t := []) (p := x14.2) (F := G) (G := G') f2 f3
    (by
      have : x14.2.vars.size ≠ 0 := by
        rw [hz2]
        simpa using hne
      simpa using this) hz1
    (by rw [hwl', hRan.first_eq]; exact hG')
  obtain ⟨g, hg⟩ : ∃ g : HeardG, g =
      { theta := zeroE, alpha := alpha, a := f.factor zeroE alpha,
        rows := table.rows.push bits.row, leaves := x14.2, sBit := bits.sEnd, keys := r9.2,
        zb0 := x14.1, zb1 := (bits.challenges.take (f.mu + f.d)).toArray,
        owedObjects := (F.owe "look-up-mask-claims").1,
        owedPlanes := ((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").1,
        owedJoin := (((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2.owe
          "look-up-join").1 } := ⟨_, rfl⟩
  obtain ⟨pl, hp⟩ := planes_ok f g G G' _ (by rw [hg]; exact erow)
  refine ⟨g, G, pl, G', ?_, hp⟩
  · rw [hg]
    unfold messagesG
    rw [hs]
    dsimp only
    rw [bind_eq (a := F.next) (G := F) (u := t) rfl,
      bind_eq (a := (F.owe "look-up-mask-claims").1) (G := (F.owe "look-up-mask-claims").2)
        (u := t) rfl,
      bind_eq (a := ((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").1)
        (G := ((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2) (u := t) rfl,
      bind_eq (a := (((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2.owe
        "look-up-join").1) (G := owed3 F) (u := t) rfl, if_neg Bool.false_ne_true,
      bind_eq (a := zeroE) (G := owed3 F) (u := t) rfl, bind_eq e5, bind_eq e6]
    try dsimp only
    rw [bind_eq e7]
    try dsimp only
    rw [bind_eq e8, bind_eq e9]
    try dsimp only
    rw [bind_eq (must_ok (by rw [y9]; simp) _ _)]
    have er : First.Prod.run f.mu f.d orderDefault
        { rows := r9.1, point := x3.reverse, form := joinAff f r6.2.2 x3 } F9 t9 =
        some (table, F11, t11) := by
      unfold First.Prod.run
      rw [List.range_eq_range']
      exact e11
    unfold joinAff at er
    rw [bind_eq er, bind_eq (must_ok (by rw [p11]; simp) _ _), bind_eq e13']
    have er2 : Fl.roundsIn RoundForm.eq (pscStart table.form τ F11.next mu eps)
        ((List.range (f.mu + f.d)).map fun j =>
          (table.point.getD j zeroE, if j < f.d then 2 else 1)) (took F11 1) t13 =
        some (x14, took (took F11 1) (2 * f.d + f.mu), t14) := e14
    rw [bind_eq er2]
    try dsimp only
    rw [bind_eq e15, bind_eq e16, bind_eq (a := G.next) (G := G) (u := []) rfl,
      bind_eq (must_ok (by
        have h1 := g16.tot
        rw [List.length_nil, Nat.add_zero] at h1
        rw [h1, hR.next, Array.size_push, z11, z9, z7, z6]
        unfold Face.lins
        simp) _ _)]
    rfl

/-- **Law.total of the kind's own hearing.** -/
theorem total_hearE (f : Face) (es : List Fmt.Entry) (F : Fork) (rs : List Fmt.RoundView) (t : Tape)
    (first : ℕ) (hs : f.shifted = false) (hok : f.ok = true) (hR : Ready f first F)
    (ht : First.Tape.tapeT {} rs es = some t) (hsh : t.map shapeOf = shapeG f) :
    ∃ g G pl G', hearE f es F rs = some (g, G) ∧ planesG f g G [] = some (pl, G', []) := by
  obtain ⟨g, G, pl, G', h1, h2⟩ := messages_ok hs hok hR hsh
  refine ⟨g, G, pl, G', ?_, h2⟩
  unfold hearE First.Tape.flRun
  rw [if_pos hok, ht]
  dsimp only
  rw [h1]

/-- **K03key_rounds, of the kind's own hearing.** -/
theorem K03key_rounds : Rounds hearE where
  shape := fun A st f es F rs g G hf hadm hF h => shape_hearE A st f es F rs g G hf hadm hF h
  hears := fun f es F rs t first hs hok hR ht hsh => by
    obtain ⟨g, G, -, -, h, -⟩ := total_hearE f es F rs t first hs hok hR ht hsh
    rw [h]
    rfl
  fits := fun A st P f es F rs g G hf hadm hF hw h =>
    fits_hearE A st P f es F rs g G hf hadm hF hw h

/-- **K03key_law, of the kind's own hearing.** -/
theorem K03key_law : Law hearE where
  total := total_hearE
  out := fun A sl st f first o k home es F rs g G hf hadm hh hw hn hF h =>
    out_hearE A sl st f first o k home es F rs g G hf hadm hh hw hn hF h

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.messages_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.K03key_rounds
#print axioms VerifiableInference.Desc.K3.KeyLaw.K03key_law
#print axioms VerifiableInference.Desc.K3.KeyLaw.keys_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.loopEq_ok
