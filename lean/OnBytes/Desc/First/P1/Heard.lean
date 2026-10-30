-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/Heard.lean: what `Fl.levelIn` and `Fl.tscIn` (OnBytes/K/Kc/Flat.lean) have
heard, AS FUNCTIONS OF THE TAPE, and what a later ledger's world holds under their slots.
Definitions, statements and proofs.

  `roundAt w t`: the tape's first round as a sumcheck's round under the weight w.
  `levelMs`, `levelY`, `levelRec`: a layer's rounds, its further round and the record behind them.
  `levelIn_heard`: where the function returns, the facts of `levelIn_tape` hold of these functions'
    values: nothing of the rounds or the record stands under "there is".
  `level_world`: with a ledger in front whose arrays have the right sizes: in the world of every
    later ledger, the sumcheck's own slots hold their mask entries; what is shown under the two end
    values' slots is the hidden value plus the further challenge times the mask entry; and the
    layer's row is the record's form at the product of what that later ledger shows there.
  `tscMs`, `tscY`, `tscIn_heard`, `tsc_world`: the like for a token sumcheck. Its record is
    returned. Its own slots are filled later, where the row is made.
  `walk_length`, `own_slots`, `tsc_walk`: the step that makes a row lays 0 with the factor -1 under
    the sumcheck's own slots; in every later ledger's world they hold their mask entries.
  `levelVals`, `tscVals`, `level_shown`, `tsc_shown`: what every later ledger shows under the end
    values' slots is what the tape's values round sent.

One direction: from a return. No law of a sumcheck is applied here.
-/
import OnBytes.Desc.First.P1.TscLaw
import OnBytes.Desc.First.P1.OrderDefault

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc Polynomial
open OnBytes.PscRun (Sized Filled hideRun_ok)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### Rounds and records, read off a tape -/

/-- The tape's first round as a sumcheck's round under the weight w: what it has to send, and the
first element that it drew. -/
def roundAt (w : OnBytes.Psc.Weight) (t : Tape) : Rnd :=
  (w, (t.head?.map (·.sent)).getD [], tapeEps t)

theorem roundAt_cons (w : OnBytes.Psc.Weight) (nm : Option String) (z k : Nat) (s : List E) (e : E)
    (d : List E) (u : Tape) : roundAt w (⟨nm, z, k, s, e :: d⟩ :: u) = (w, s, e) := rfl

theorem drop_first {α : Type} (r0 : α) (rs more : List α) :
    (r0 :: (rs ++ more)).drop (rs.length + 1) = more :=
  drop_cons_append r0 rs more 0

/-- A layer's rounds. -/
def levelMs (mu : Nat) (rho : Array E) (order : List Nat) (t : Tape) : List Rnd :=
  msOf (levelWs mu rho order) (t.drop 1)

/-- A layer's round in the further variable. -/
def levelY (mu : Nat) (t : Tape) : Rnd := roundAt (OnBytes.Psc.Weight.atZero 3) (t.drop (mu + 1))

/-- The record behind a layer's rounds. -/
def levelRec (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) (F : Fork) (t : Tape) : Psc :=
  endP { target := (F.publicPart C).getD zeroE, first := F.next, eps := tapeEps t,
         claim := addE (tapeMu t) (mulE (tapeEps t) ((F.publicPart C).getD zeroE)),
         start := C, started := true } (levelMs mu rho order t) (levelY mu t)

/-- **What a layer has heard.** -/
theorem levelIn_heard {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    order.length = mu ∧ (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) ∧
      F.publicPart C = some (levelRec mu rho C order F t).target ∧
      (levelMs mu rho order t).map (·.1) = levelWs mu rho order ∧
      (levelY mu t).1 = OnBytes.Psc.Weight.atZero 3 ∧
      (∀ m ∈ levelMs mu rho order t ++ [levelY mu t], Held m.1) ∧
      (∀ m ∈ levelMs mu rho order t ++ [levelY mu t], m.2.1.length + 1 = m.1.d) ∧
      (levelRec mu rho C order F t).vars.toList =
        levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3] ∧
      (levelRec mu rho C order F t).r.toList =
        (levelMs mu rho order t ++ [levelY mu t]).map (·.2.2) ∧
      (levelRec mu rho C order F t).claim =
        claimAfter (levelMs mu rho order t ++ [levelY mu t])
          (addE (tapeMu t) (mulE (levelRec mu rho C order F t).eps
            (levelRec mu rho C order F t).target)) ∧
      (levelRec mu rho C order F t).eps = tapeEps t ∧
      (levelRec mu rho C order F t).start = C ∧
      (levelRec mu rho C order F t).first = F.next ∧
      L.r = levelR mu order ((levelMs mu rho order t).map (·.2.2)) (Array.replicate mu zeroE) ∧
      L.sL = F.next + 1 + 2 * mu + 2 ∧ L.sR = L.sL + 1 ∧ L.tau = tapeEps (t.drop (mu + 3)) ∧
      u = t.drop (mu + 4) ∧
      ∃ (v : Array E) (G1 : Fork), v.size = 2 ∧
        ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork).hideRun L.sL v (levelY mu t).2.2 =
          some G1 ∧
        L.row = (levelRec mu rho C order F t).rowForm
          (mulE (G1.vp.getD L.sL zeroE) (G1.vp.getD (L.sL + 1) zeroE)) {} ∧
        G1.hideRun (levelRec mu rho C order F t).first
          (Array.replicate (levelRec mu rho C order F t).walk.1.length zeroE)
          (subE zeroE oneE) = some G := by
  obtain ⟨hom, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, ht,
    hrs, _, htest, htau, hms, hyy, hp, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, htar, heps,
    hstart, hfirst, hrow, hLr, hsL, hsR, hv2, hG1, hshL, hshR, hG⟩ := levelIn_tape h
  have hwr : (levelWs mu rho order).length = rs.length := by
    rw [levelWs, List.length_map, hom, hrs]
  have q1 : levelMs mu rho order t = ms := by
    unfold levelMs
    rw [ht, drop_one_cons, msOf_append_same _ _ _ hwr, hms]
  have q2 : levelY mu t = y := by
    unfold levelY
    rw [ht, ← hrs, drop_first, roundAt_cons, hyy]
  have q3 : tapeMu t = mu0 := by rw [ht, tapeMu_cons]
  have q4 : tapeEps t = eps := by rw [ht, tapeEps_cons]
  have q5 : (F.publicPart C).getD zeroE = T := by rw [hT, Option.getD_some]
  have q6 : levelRec mu rho C order F t = p := by
    unfold levelRec
    rw [q1, q2, q3, q4, q5, hp]
  have hu : u = t.drop (mu + 4) := by rw [ht, ← hrs, drop_level]
  have htau' : L.tau = tapeEps (t.drop (mu + 3)) := by
    rw [htau, ht, ← hrs, drop_level', tapeEps_cons]
  rw [q6, q1, q2, q3, q4]
  refine ⟨hom, htest, by rw [htar]; exact hT, a1, hy, hheld, hlens, hvars, hr,
    by rw [hclaim, heps, htar], heps, hstart, hfirst, hLr, hsL, hsR, htau', hu, v, G1, hv2, hG1,
    ?_, hG⟩
  rw [hrow, (shown_some hshL).2.2, (shown_some hshR).2.2]

/-- **What a later ledger's world holds under a layer's slots.** -/
theorem level_world (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) {mu : Nat} {rho : Array E} {C : Aff}
    {order : List Nat} {F G : Fork} {t u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    Fo.Later F G ∧ Sized G ∧ G.next = F.next + 1 + 2 * mu + 2 + 2 ∧
      ∀ H : Fork, Fo.Later G H →
        (∀ i, i < OnBytes.Psc.hidingEntries
            (levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]) →
          (H.worldOf ρ mask entry).slot ((levelRec mu rho C order F t).first + i) =
            mask (F.next + i)) ∧
        (∀ e, e < 2 → ρ.val (H.vp.getD (L.sL + e) zeroE) =
          (H.worldOf ρ mask entry).slot (L.sL + e) +
            ρ.val (levelY mu t).2.2 * mask (L.sL + e)) ∧
        L.row = (levelRec mu rho C order F t).rowForm
          (mulE (H.vp.getD L.sL zeroE) (H.vp.getD (L.sL + 1) zeroE)) {} ∧
        C.value ρ (H.worldOf ρ mask entry) = C.value ρ (F.worldOf ρ mask entry) := by
  obtain ⟨hom, _, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, heps, hstart, hfirst, hLr, hsL, hsR,
    _, _, v, G1, hv2, hG1, hrow, hG⟩ := levelIn_heard h
  generalize levelRec mu rho C order F t = p at *
  generalize levelMs mu rho order t = ms at *
  generalize levelY mu t = y at *
  -- the ledgers, one later than the other
  have hF' : Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) := hF
  have l0 : Fo.Later F ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) :=
    ⟨by show F.next ≤ F.next + 1 + 2 * mu + 2 + 2; omega, rfl, fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨hSa, hS1, hin1, _⟩ := hideRun_ok _ G1 L.sL v y.2.2 hF' hG1
  have l1 := Fo.hideRun_later hF' hG1
  obtain ⟨hSb, hS2, hin2, _⟩ := hideRun_ok G1 G p.first _ _ hS1 hG
  have l2 := Fo.hideRun_later hS1 hG
  refine ⟨(l0.trans l1).trans l2, hS2, by rw [hSb.next, hSa.next], ?_⟩
  intro H lH
  -- the hiding coefficients
  have hzipl : p.vars.toList.zip p.r.toList = (ms ++ [y]).map fun m => (m.1, m.2.2) := by
    have hv' : p.vars.toList = (ms ++ [y]).map (·.1) := by
      rw [hvars, List.map_append, a1]
      simp [hy]
    rw [hv', hr]
    exact zip_maps _ _ _
  have hwl : p.walk.1.length =
      OnBytes.Psc.hidingEntries (levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]) := by
    rw [Psc.walk, zipT_eq, hidingWalk_length _ (by rw [hzipl]; simp) (by
      intro x hx
      rw [hzipl] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      have := (hheld m hm).spec.1
      show 1 ≤ m.1.d
      omega), hzipl, List.map_map, ← hvars]
    have hv' : p.vars.toList = (ms ++ [y]).map (·.1) := by
      rw [hvars, List.map_append, a1]
      simp [hy]
    rw [hv']
    rfl
  have hslots : ∀ i, i < OnBytes.Psc.hidingEntries
      (levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]) →
      (H.worldOf ρ mask entry).slot (p.first + i) = mask (F.next + i) := by
    intro i hi
    have q := hin2 i (by rw [Array.size_replicate, hwl]; exact hi)
    have r := lH.keep (p.first + i) q.2.2.1
    rw [slot_worldOf, r.2.1, r.2.2, q.2.2.2.1, q.2.2.2.2, hfirst]
    have hz : (Array.replicate p.walk.1.length zeroE).getD i zeroE = zeroE := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [hz, ρ.zero, ρ.sub, ρ.zero, ρ.one]
    ring
  have hkeep : ∀ e, e < 2 → H.vp.getD (L.sL + e) zeroE = G1.vp.getD (L.sL + e) zeroE ∧
      H.mf.getD (L.sL + e) zeroE = y.2.2 := by
    intro e he
    have k := hin1 e (by omega)
    have g := l2.keep (L.sL + e) k.2.2.1
    have f := lH.keep (L.sL + e) g.1
    exact ⟨f.2.1.trans g.2.1, (f.2.2.trans g.2.2).trans k.2.2.2.2⟩
  refine ⟨hslots, ?_, ?_, ?_⟩
  · intro e he
    rw [slot_worldOf, (hkeep e he).2]
    ring
  · have k0 := (hkeep 0 (by omega)).1
    rw [Nat.add_zero] at k0
    rw [hrow, k0, (hkeep 1 (by omega)).1]
  · exact Fo.value_later ρ (((l0.trans l1).trans l2).trans lH) C (filledA_of_publicPart hT) mask
      entry

/-! ### A token sumcheck -/

/-- A token sumcheck's rounds. -/
def tscMs (P : Array E) (lt : Nat) (t : Tape) : List Rnd :=
  msOf (tscWs (P.toList.take lt)) (t.drop 1)

/-- A token sumcheck's round in the further variable. -/
def tscY (P : Array E) (lt dY : Nat) (t : Tape) : Rnd :=
  roundAt (OnBytes.Psc.Weight.atZero (dY + 1)) (t.drop ((P.toList.take lt).length + 1))

/-- **What a token sumcheck has heard.** -/
theorem tscIn_heard {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    lt ≤ P.size ∧
      (tscMs P lt t).map (·.1) = tscWs (P.toList.take lt) ∧
      (tscY P lt dY t).1 = OnBytes.Psc.Weight.atZero (dY + 1) ∧
      (∀ m ∈ tscMs P lt t ++ [tscY P lt dY t], Held m.1) ∧
      (∀ m ∈ tscMs P lt t ++ [tscY P lt dY t], m.2.1.length + 1 = m.1.d) ∧
      o.p.vars.toList = tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero (dY + 1)] ∧
      o.p.r.toList = (tscMs P lt t ++ [tscY P lt dY t]).map (·.2.2) ∧
      o.p.claim = claimAfter (tscMs P lt t ++ [tscY P lt dY t])
        (addE (tapeMu2 t) (mulE o.p.eps o.p.target)) ∧
      o.p.eps = tapeEps t ∧ o.p.start = Aff.slot F.next ∧ o.sCl = F.next ∧
      o.r.toList = (tscMs P lt t).map (·.2.2) ∧
      u = t.drop ((P.toList.take lt).length + 3) ∧
      ∃ (v : Array E) (G0 : Fork),
        ({ F with next := F.next + 1 } : Fork).hideRun F.next #[tapeCl t] oneE = some G0 ∧
        G0.publicPart (Aff.slot F.next) = some o.p.target ∧ o.p.first = G0.next ∧
        o.sEnd = G0.next + 1 + 2 * (P.toList.take lt).length + dY ∧ v.size = n ∧
        ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork).hideRun
          o.sEnd v (tscY P lt dY t).2.2 = some G := by
  obtain ⟨hlt, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0, ht, hrs, _, hms, hyy,
    hv1c, hsCl, hv1, hG0, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, htar, heps, hstart, hfirst,
    hor, hsEnd, hvn, hG⟩ := tscIn_tape h
  have hwr : (tscWs (P.toList.take lt)).length = rs.length := by
    rw [tscWs, List.length_map, hrs]
  have q1 : tscMs P lt t = ms := by
    unfold tscMs
    rw [ht, drop_one_cons, msOf_append_same _ _ _ hwr, hms]
  have q2 : tscY P lt dY t = y := by
    unfold tscY
    rw [ht, ← hrs, drop_first, roundAt_cons, hyy]
  have q3 : tapeMu2 t = mu0 := by rw [ht, tapeMu2_cons]
  have q4 : tapeEps t = eps := by rw [ht, tapeEps_cons]
  have q6 : tapeCl t = cl := by rw [ht, tapeCl_cons]
  have hu : u = t.drop ((P.toList.take lt).length + 3) := by rw [ht, ← hrs, drop_tsc]
  rw [hv1c] at hG0
  rw [q1, q2, q3, q4, q6]
  exact ⟨hlt, a1, hy, hheld, hlens, hvars, hr, by rw [hclaim, heps, htar], heps, hstart, hsCl, hor,
    hu, v, G0, hG0, by rw [htar]; exact hT, hfirst, hsEnd, hvn, hG⟩

/-- **What a later ledger's world holds under a token sumcheck's slots.** -/
theorem tsc_world (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) {P : Array E} {lt n dY : Nat}
    {F G : Fork} {t u : Tape} {o : Tsc} (hF : Sized F)
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    Fo.Later F G ∧ Sized G ∧ o.p.first = F.next + 1 ∧
      o.sEnd = F.next + 1 + 1 + 2 * (P.toList.take lt).length + dY ∧ G.next = o.sEnd + n ∧
      o.p.target = tapeT t ∧ (∀ e, e < n → Filled G (o.sEnd + e)) ∧
      ∀ H : Fork, Fo.Later G H →
        (H.worldOf ρ mask entry).slot o.sCl = ρ.val (tapeCl t) - mask F.next ∧
        ∀ e, e < n → ρ.val (H.vp.getD (o.sEnd + e) zeroE) =
          (H.worldOf ρ mask entry).slot (o.sEnd + e) +
            ρ.val (tscY P lt dY t).2.2 * mask (o.sEnd + e) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsCl, _, _, v, G0, hG0, hT, hfirst, hsEnd, hvn, hG⟩ :=
    tscIn_heard h
  generalize tscY P lt dY t = y at *
  have hF' : Sized ({ F with next := F.next + 1 } : Fork) := hF
  have l0 : Fo.Later F ({ F with next := F.next + 1 } : Fork) :=
    ⟨by show F.next ≤ F.next + 1; omega, rfl, fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨hSame0, hS0, hin0, _⟩ := hideRun_ok _ G0 F.next _ oneE hF' hG0
  have l1 := Fo.hideRun_later hF' hG0
  have hnext : G0.next = F.next + 1 := hSame0.next
  have hS0' : Sized ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } :
      Fork) := hS0
  have l2 : Fo.Later G0
      ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) :=
    ⟨by show G0.next ≤ G0.next + 1 + 2 * (P.toList.take lt).length + dY + n; omega, rfl,
      fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨hSame1, hS1, hin1, _⟩ := hideRun_ok _ G o.sEnd v y.2.2 hS0' hG
  have l3 := Fo.hideRun_later hS0' hG
  have c0 := hin0 0 Nat.zero_lt_one
  rw [Nat.add_zero, getD_one] at c0
  have hGn : G.next = G0.next + 1 + 2 * (P.toList.take lt).length + dY + n := hSame1.next
  refine ⟨((l0.trans l1).trans l2).trans l3, hS1, by rw [hfirst, hnext], by rw [hsEnd, hnext],
    by rw [hGn, hsEnd], ?_, fun e he => (hin1 e (by omega)).2.2.1, ?_⟩
  · rw [publicPart_slot_eq hT, c0.2.2.2.1]
    rfl
  · intro H lH
    have kc' := (l2.trans l3).keep F.next c0.2.2.1
    have kc := lH.keep F.next kc'.1
    refine ⟨?_, ?_⟩
    · rw [hsCl, slot_worldOf, kc.2.1, kc'.2.1, kc.2.2, kc'.2.2, c0.2.2.2.1, c0.2.2.2.2, ρ.one]
      ring
    · intro e he
      have q := hin1 e (by omega)
      have r := lH.keep (o.sEnd + e) q.2.2.1
      rw [slot_worldOf, r.2.2, q.2.2.2.2]
      ring

/-! ### A sumcheck's own slots, where its row is made -/

/-- The hiding polynomial of a record behind rounds has just `hidingEntries` coefficients. -/
theorem walk_length {p : Psc} {ms : List Rnd} (hne : ms ≠ []) (hv : p.vars.toList = ms.map (·.1))
    (hr : p.r.toList = ms.map (·.2.2)) (hheld : ∀ m ∈ ms, Held m.1) :
    p.walk.1.length = OnBytes.Psc.hidingEntries (ms.map (·.1)) := by
  have hzipl : p.vars.toList.zip p.r.toList = ms.map fun m => (m.1, m.2.2) := by
    rw [hv, hr]
    exact zip_maps _ _ _
  have h2 : (p.vars.toList.zip p.r.toList).map (·.1) = ms.map (·.1) := by
    rw [hzipl, List.map_map]
    rfl
  rw [Psc.walk, zipT_eq, hidingWalk_length _ (by rw [hzipl]; simpa using hne) (by
    intro x hx
    rw [hzipl] at hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    have := (hheld m hm).spec.1
    show 1 ≤ m.1.d
    omega), h2]

/-- **Where a row is made.** The step that makes a sumcheck's row lays 0 with the factor -1 under
the sumcheck's own slots. In the world of every later ledger these slots hold their mask entries. -/
theorem own_slots (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) {G G' : Fork} {p : Psc} (hG : Sized G)
    (h : G.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G') :
    Fo.Later G G' ∧ Sized G' ∧ ∀ H : Fork, Fo.Later G' H → ∀ i, i < p.walk.1.length →
      (H.worldOf ρ mask entry).slot (p.first + i) = mask (p.first + i) := by
  obtain ⟨_, hS2, hin2, _⟩ := hideRun_ok G G' p.first _ _ hG h
  refine ⟨Fo.hideRun_later hG h, hS2, fun H lH i hi => ?_⟩
  have q := hin2 i (by rw [Array.size_replicate]; exact hi)
  have r := lH.keep (p.first + i) q.2.2.1
  rw [slot_worldOf, r.2.1, r.2.2, q.2.2.2.1, q.2.2.2.2]
  have hz : (Array.replicate p.walk.1.length zeroE).getD i zeroE = zeroE := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  rw [hz, ρ.zero, ρ.sub, ρ.zero, ρ.one]
  ring

/-- The number of a token sumcheck's own slots. -/
theorem tsc_walk {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    o.p.walk.1.length = OnBytes.Psc.hidingEntries
      (tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero (dY + 1)]) := by
  obtain ⟨_, a1, hy, hheld, _, hvars, hr, _⟩ := tscIn_heard h
  have hv' : o.p.vars.toList = (tscMs P lt t ++ [tscY P lt dY t]).map (·.1) := by
    rw [hvars, List.map_append, a1]
    simp [hy]
  rw [walk_length (by simp) hv' hr hheld, ← hv', hvars]

/-! ### What is shown under the end values' slots is what the tape's values round sent -/

/-- What the tape's first round has to send. -/
def sentOf (t : Tape) : List E := (t.head?.map (·.sent)).getD []

theorem sentOf_cons (nm : Option String) (z k : Nat) (s d : List E) (u : Tape) :
    sentOf (⟨nm, z, k, s, d⟩ :: u) = s := rfl

theorem drop_second {α : Type} (r0 : α) (rs : List α) (a : α) (more : List α) :
    (r0 :: (rs ++ a :: more)).drop (rs.length + 2) = more :=
  drop_cons_append r0 rs (a :: more) 1

/-- What a layer's values round sent. -/
def levelVals (mu : Nat) (t : Tape) : List E := sentOf (t.drop (mu + 2))

/-- What a token sumcheck's values round sent. -/
def tscVals (P : Array E) (lt : Nat) (t : Tape) : List E :=
  sentOf (t.drop ((P.toList.take lt).length + 2))

/-- Every later ledger shows, under a layer's two end values' slots, what the values round sent. -/
theorem level_shown {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    ∀ H : Fork, Fo.Later G H → ∀ e, e < 2 →
      H.vp.getD (L.sL + e) zeroE = (levelVals mu t).getD e zeroE := by
  obtain ⟨hom, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, ht,
    hrs, _, htest, htau, hms, hyy, hp, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, htar, heps,
    hstart, hfirst, hrow, hLr, hsL, hsR, hv2, hG1, hshL, hshR, hG⟩ := levelIn_tape h
  have hvt : v.toList = levelVals mu t := by
    unfold levelVals
    rw [ht, ← hrs, drop_second, sentOf_cons]
  have hF' : Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) := hF
  obtain ⟨_, hS1, hin1, _⟩ := hideRun_ok _ G1 L.sL v y.2.2 hF' hG1
  have l2 := Fo.hideRun_later hS1 hG
  intro H lH e he
  have k := hin1 e (by omega)
  have g := l2.keep (L.sL + e) k.2.2.1
  have f := lH.keep (L.sL + e) g.1
  rw [f.2.1, g.2.1, k.2.2.2.1, array_getD_toList, hvt]

/-- Every later ledger shows, under a token sumcheck's end values' slots, what the values round
sent. -/
theorem tsc_shown {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (hF : Sized F) (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    ∀ H : Fork, Fo.Later G H → ∀ e, e < n →
      H.vp.getD (o.sEnd + e) zeroE = (tscVals P lt t).getD e zeroE := by
  obtain ⟨hlt, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0, ht, hrs, _, hms, hyy,
    hv1c, hsCl, hv1, hG0, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, htar, heps, hstart, hfirst,
    hor, hsEnd, hvn, hG⟩ := tscIn_tape h
  have hvt : v.toList = tscVals P lt t := by
    unfold tscVals
    rw [ht, ← hrs, drop_second, sentOf_cons]
  have hF' : Sized ({ F with next := F.next + 1 } : Fork) := hF
  obtain ⟨_, hS0, _, _⟩ := hideRun_ok _ G0 F.next v1 oneE hF' hG0
  have hS0' : Sized ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } :
      Fork) := hS0
  obtain ⟨_, _, hin1, _⟩ := hideRun_ok _ G o.sEnd v y.2.2 hS0' hG
  intro H lH e he
  have q := hin1 e (by omega)
  have r := lH.keep (o.sEnd + e) q.2.2.1
  rw [r.2.1, q.2.2.2.1, array_getD_toList, hvt]

end OnBytes.Desc.First.P1
