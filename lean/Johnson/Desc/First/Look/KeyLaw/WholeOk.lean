-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/WholeOk.lean: one whole masked sumcheck as the kind "lookup" calls it
(wholeStandIn) RETURNS, on a tape whose next rounds have its shape, from a ledger with enough free
slots ahead, for a claim whose slots are filled.

Main names:
  Fr F n: the ledger has its sizes and n free slots ahead.
  round2_ok, loop2_ok, ends_ok, shownLoop_ok, row_ok: the pieces.
  ran_walk_len: the number of the hiding polynomial's coefficients.
  whole_ok: THE WHOLE: it returns; the tape left has the shapes left; the slots ahead are still
    free; the slots behind are as they were; the end values' slots are filled.

Limits. Nothing on what the values are.

-/
import Johnson.Desc.First.Look.KeyLaw.Forward
import Johnson.Desc.First.Look.KeyLaw.Sim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole)

/-- The ledger has its sizes and n free slots ahead. -/
structure Fr (F : Fork) (n : ℕ) : Prop where
  sized : Sized F
  room : F.next + n ≤ F.ns
  free : ∀ j, F.next ≤ j → j < F.next + n → ¬ Filled F j

theorem took_took (F : Fork) (a b : ℕ) : took (took F a) b = took F (a + b) := by
  show ({ F with next := F.next + a + b } : Fork) = { F with next := F.next + (a + b) }
  rw [Nat.add_assoc]

theorem round2_ok {p : Psc} {z : E} {F : Fork} {t : Tape} {L : List Shape} (he : p.ended = false)
    (h : t.map shapeOf = (RoundName.pscRound.name, 2, 1, 0) :: L) :
    ∃ (sent : Array E) (x : E) (u : Tape), Fl.roundIn .eq2 p z 0 F t =
        some ((x, { p with
          claim := OnBytes.Psc.polyAt
            ((OnBytes.Psc.Weight.equality z 3).complete sent.toList p.claim) x,
          vars := p.vars.push (OnBytes.Psc.Weight.equality z 3), r := p.r.push x }),
          took F 2, u) ∧ u.map shapeOf = L := by
  obtain ⟨sent, x, u, e, hu, -⟩ := pscRound_ok (p := p) (w := OnBytes.Psc.Weight.equality z 3)
    (name := .pscRound) (nz := 0) (F := F) (by decide) ((PscRun.fits_equality z 3).2 (by decide))
    (PscRun.weightHeld_equality z 3) h (show 1 ≤ 3 by decide)
  refine ⟨sent, x, u, ?_, hu⟩
  unfold Fl.roundIn
  rw [bind_eq (must_ok (by rw [he]; rfl) F t),
    bind_eq (a := OnBytes.Psc.Weight.equality z 3) (G := F) (u := t) rfl]
  exact e

theorem loop2_ok : ∀ (zs : List E) (p : Psc) (F : Fork) (t : Tape) (L : List Shape),
    p.ended = false →
    t.map shapeOf = (List.replicate zs.length 2).map
      (fun g => (RoundName.pscRound.name, g, 1, 0)) ++ L →
    ∃ p' u, (zs.foldlM (m := Fl) (fun (p : Psc) z => do
        let x ← Fl.roundIn .eq2 p z
        pure x.2) p) F t = some (p', took F (2 * zs.length), u) ∧ u.map shapeOf = L ∧
      p'.ended = false ∧ p'.rowMade = p.rowMade ∧ p'.started = p.started
  | [], p, F, t, L, he, h => ⟨p, t, rfl, h, he, rfl, rfl⟩
  | z :: zs, p, F, t, L, he, h => by
    obtain ⟨sent, x, u, e, hu⟩ := round2_ok (z := z) (F := F) he h
    obtain ⟨p', u', e', h1, h2, h3, h4⟩ := loop2_ok zs _ (took F 2) u L
      (show ({ p with
        claim := OnBytes.Psc.polyAt
          ((OnBytes.Psc.Weight.equality z 3).complete sent.toList p.claim) x,
        vars := p.vars.push (OnBytes.Psc.Weight.equality z 3),
        r := p.r.push x } : Psc).ended = false from he) hu
    refine ⟨p', u', ?_, h1, h2, h3, h4⟩
    rw [List.foldlM_cons, bind_eq (bind_eq e)]
    rw [took_took, show 2 + 2 * zs.length = 2 * (z :: zs).length by
      rw [List.length_cons]; omega] at e'
    exact e'

theorem ends_ok {p : Psc} {dY n : ℕ} {F : Fork} {t : Tape} {L : List Shape} (he : p.ended = false)
    (hdY : 1 ≤ dY) (hn : 1 ≤ n)
    (h : t.map shapeOf = (RoundName.pscY.name, dY, 1, 1) :: (RoundName.pscValues.name, n, 0, 0) ::
        L)
    (hF : Sized F) (hr : F.next + dY + n ≤ F.ns) (hf : ∀ i < n, ¬ Filled F (F.next + dY + i)) :
    ∃ (sent v : Array E) (beta : E) (G : Fork) (u : Tape),
      Fl.pscEnds p dY n F t = some ((F.next + dY, { p with
        claim := OnBytes.Psc.polyAt
          ((OnBytes.Psc.Weight.equality zeroE (dY + 1)).complete sent.toList p.claim) beta,
        vars := p.vars.push (OnBytes.Psc.Weight.equality zeroE (dY + 1)),
        r := p.r.push beta, ended := true }), G, u) ∧ u.map shapeOf = L ∧ sent.size = dY ∧
      v.size = n ∧ (took (took F dY) n).hideRun (F.next + dY) v beta = some G := by
  obtain ⟨sent, beta, u1, e1, hu1, hss⟩ := pscRound_ok (p := p)
    (w := OnBytes.Psc.Weight.atZero (dY + 1)) (name := .pscY) (nz := 1) (F := F) (by decide)
    ((PscRun.fits_equality zeroE (dY + 1)).2 (by omega)) (PscRun.weightHeld_atZero (dY + 1)) h
    (Nat.le_add_left 1 dY)
  have hd : (OnBytes.Psc.Weight.atZero (dY + 1)).d - 1 = dY := rfl
  rw [hd] at e1
  obtain ⟨w, s, d, u, rfl, h1, h2, h3⟩ := head_of hu1 (show RoundName.pscValues.name ≠ "" by decide)
  obtain rfl : d = [] := List.length_eq_zero_iff.1 h2
  obtain ⟨v, hv, hvs⟩ := read_ok n (took F dY) (some RoundName.pscValues.name) 0 w s [] u h1
  obtain ⟨G, hG⟩ := hideRun_some (F := took (took F dY) n) (first := F.next + dY) (v := v) hF
    (by rw [hvs]; exact hr) (by rw [hvs]; exact hf) beta
  refine ⟨sent, v, beta, G, u, ?_, h3, by
    have : sent.size + 1 = dY + 1 := hss
    omega, hvs, hG⟩
  unfold Fl.pscEnds
  rw [bind_eq (must_ok (by rw [he]; simp; omega) F _), bind_eq e1]
  dsimp only
  rw [bind_eq hv, bind_eq (must_ok (by rw [hvs]; simp) _ _),
    bind_eq (a := ()) (G := took F dY) (u := u) (by
      unfold Fl.empty Fl.onTape Fl.emptyOn
      rw [show (0 : ℕ) = ([] : List E).length from rfl, closeN_ok RoundName.pscValues.name _ w [] u]
      rfl),
    bind_eq (takeSlots_eq _ _ _),
    bind_eq (a := ()) (G := G) (u := u) (by
      show ((took (took F dY) n).hideRun (F.next + dY) v beta).map _ = _
      rw [hG]; rfl)]
  rfl

theorem shownLoop_ok (e : ℕ) : ∀ (l : List ℕ) (acc : List E) (F : Fork) (t : Tape),
    (∀ i ∈ l, e + i < F.ns ∧ Filled F (e + i)) →
    List.mapM.loop (fun i => Fl.shown (e + i)) l acc F t =
      some (acc.reverse ++ l.map (fun i => F.vp.getD (e + i) zeroE), F, t)
  | [], acc, F, t, _ => by
    show some (acc.reverse, F, t) = _
    simp
  | i :: l, acc, F, t, h => by
    obtain ⟨h1, h2⟩ := h i List.mem_cons_self
    unfold List.mapM.loop
    rw [bind_eq (a := F.vp.getD (e + i) zeroE) (G := F) (u := t) (by
      show (F.shown (e + i)).map _ = _
      rw [(PscRun.shown_iff F _ _).2 ⟨h1, h2, rfl⟩]; rfl),
      shownLoop_ok e l _ F t fun j hj => h j (List.mem_cons_of_mem _ hj)]
    simp

theorem row_ok {p : Psc} {S0 : E} {kept : Aff} {F G : Fork} {t : Tape} (h1 : p.rowMade = false)
    (h2 : p.started = true) (h3 : p.vars.isEmpty = false) (h4 : p.r.size = p.vars.size)
    (hG : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    Fl.pscRow p S0 kept F t = some ((p.rowForm S0 kept, { p with rowMade := true }), G, t) := by
  unfold Fl.pscRow
  rw [bind_eq (must_ok (by rw [h1, h2, h3, h4]; simp) F t),
    bind_eq (a := ()) (G := G) (u := t) (by
      show (F.hideRun _ _ _).map _ = _
      rw [hG]; rfl)]
  rfl

/-- The number of the hiding polynomial's coefficients. -/
theorem ran_walk_len {p : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (h : Ran p first mu eps zd rs) (hne : zd ≠ [])
    (hd : ∀ x ∈ zd, 1 ≤ x.2) : p.walk.1.length = 1 + (zd.map fun x => x.2 - 1).sum := by
  have hwk := (ran_read h).2
  have hl : zd.length = rs.length := h.fits.length
  have := PscF.hidingWalk_length (wF zd) ((rs.map readRound).map (·.2)) (by simpa [wF] using hne)
    (by simp [wF, hl]) (fun w hw => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hw
      exact hd q hq)
  rw [← congrArg Prod.fst hwk, List.length_map, entries_wF] at this
  exact this

theorem ran_sizes {p : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (h : Ran p first mu eps zd rs) :
    p.r.size = p.vars.size ∧ p.vars.size = zd.length := by
  have h1 : p.vars.size = zd.length := by
    rw [← Array.length_toList, h.vars_eq]; simp [PscTie.eqW]
  have h2 : p.r.size = rs.length := by
    rw [← Array.length_toList, h.r_eq]; simp
  exact ⟨by rw [h1, h2, h.fits.length], h1⟩


/-- **One whole masked sumcheck returns.** -/
theorem whole_ok {C : Aff} {zs : List E} {dY n n' : ℕ} {endTerm : List E → E} {F : Fork} {t : Tape}
    {L : List Shape} (hFr : Fr F (1 + 2 * zs.length + dY + n + n')) (hC : AllShown F C)
    (hdY : 1 ≤ dY) (hn : 1 ≤ n)
    (ht : t.map shapeOf = pscShape (List.replicate zs.length 2) (some (dY, n)) ++ L) :
    ∃ w G u, wholeStandIn C zs dY n endTerm F t = some (w, G, u) ∧ u.map shapeOf = L ∧ Fr G n' ∧
      G.next = F.next + (1 + 2 * zs.length + dY + n) ∧ Later F G ∧
      (∀ i < n, AllShown G (Aff.slot (w.sEnd + i))) ∧
      (∀ j < F.next, (Filled G j ↔ Filled F j)) ∧ w.challenges.length = zs.length + 1 := by
  have ht' : t.map shapeOf = (RoundName.pscEpsilon.name, 1, 1, 0) ::
      ((List.replicate zs.length 2).map (fun g => (RoundName.pscRound.name, g, 1, 0)) ++
        ((RoundName.pscY.name, dY, 1, 1) :: (RoundName.pscValues.name, n, 0, 0) :: L)) := by
    rw [ht]; simp [pscShape]
  obtain ⟨τ, mu, eps, u0, e0, s0⟩ := begin_ok hC ht'
  obtain ⟨p1, u1, e1, s1, f1, f2, f3⟩ := loop2_ok zs
    { start := C, started := true, target := τ, first := F.next, eps := eps,
      claim := addE mu (mulE eps τ) } (took F 1) u0 _ rfl s0
  obtain ⟨rs, hl, -, hR, -, -, -, -⟩ := loop2_fl zs _ p1 _ _ _ u1 [] [] e1
    (PscRun.ran_begin C τ mu eps F.next)
  have hn1 : (took (took F 1) (2 * zs.length)).next = F.next + 1 + 2 * zs.length := rfl
  obtain ⟨sent, v, beta, G2, u2, e2, s2, hs, hv, hh⟩ := ends_ok
    (F := took (took F 1) (2 * zs.length)) f1 hdY hn s1 hFr.sized
    (by rw [hn1]; have := hFr.room; show _ ≤ F.ns; omega)
    (fun i hi => by rw [hn1]; exact hFr.free _ (by omega) (by omega))
  have hS1 : Sized (took (took (took (took F 1) (2 * zs.length)) dY) n) := hFr.sized
  obtain ⟨g1, g2, g3, g4⟩ := PscRun.hideRun_ok _ _ _ _ _ hS1 hh
  have hR2 := PscRun.ran_push hR zeroE (dY + 1) sent beta (by omega)
    { p1 with
      claim := OnBytes.Psc.polyAt
        ((OnBytes.Psc.Weight.equality zeroE (dY + 1)).complete sent.toList p1.claim) beta,
      vars := p1.vars.push (OnBytes.Psc.Weight.equality zeroE (dY + 1)),
      r := p1.r.push beta, ended := true } rfl rfl rfl rfl rfl rfl
  obtain ⟨P2, hP2⟩ : ∃ P : Psc, P = { p1 with
      claim := OnBytes.Psc.polyAt
        ((OnBytes.Psc.Weight.equality zeroE (dY + 1)).complete sent.toList p1.claim) beta,
      vars := p1.vars.push (OnBytes.Psc.Weight.equality zeroE (dY + 1)),
      r := p1.r.push beta, ended := true } := ⟨_, rfl⟩
  rw [← hP2] at hR2 e2
  have f2' : P2.rowMade = false := by rw [hP2]; exact f2
  have f3' : P2.started = true := by rw [hP2]; exact f3
  have f4' : P2.vars.isEmpty = false := by rw [hP2]; simp
  have hlen := ran_walk_len hR2 (by simp) (fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · cases hx
      · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
        exact (by decide : 1 ≤ 3)
    · obtain rfl : x = (zeroE, dY + 1) := by simpa using hx
      exact Nat.le_add_left 1 dY)
  have hsum : ((([] : List (E × ℕ)) ++ zs.map (·, 3) ++ [(zeroE, dY + 1)]).map
      fun x : E × ℕ => x.2 - 1).sum =
      2 * zs.length + dY := by
    rw [List.nil_append, List.map_append, List.map_map, List.sum_append]
    have e : (zs.map ((fun p : E × ℕ => p.2 - 1) ∘ fun x => (x, 3))).sum = zs.length * 2 :=
      sum_const 2 zs
    rw [e]
    show zs.length * 2 + (dY + 1 - 1 + 0) = _
    omega
  rw [hsum] at hlen
  obtain ⟨hz1, hz2⟩ := ran_sizes hR2
  obtain ⟨G, hG⟩ := hideRun_some (F := G2) (first := F.next)
    (v := Array.replicate (1 + (2 * zs.length + dY)) zeroE) g2
    (by rw [g1.ns, Array.size_replicate]; have := hFr.room; show _ ≤ F.ns; omega)
    (fun i hi => by
      rw [Array.size_replicate] at hi
      rw [(g4 (F.next + i) (Or.inl (by rw [hn1]; omega))).2.2]
      exact hFr.free _ (by omega) (by omega)) (subE zeroE oneE)
  obtain ⟨k1, k2, k3, k4⟩ := PscRun.hideRun_ok _ _ _ _ _ g2 hG
  have e3 := shownLoop_ok ((took (took F 1) (2 * zs.length)).next + dY) (List.range n) [] G2 u2
    (fun i hi => by
      obtain ⟨c1, -, c3, -, -⟩ := g3 i (by rw [hv]; exact List.mem_range.1 hi)
      exact ⟨by rw [g1.ns]; exact c1, c3⟩)
  obtain ⟨ends, hends⟩ : ∃ l : List E, l = ([] : List E).reverse ++ (List.range n).map fun i =>
      G2.vp.getD ((took (took F 1) (2 * zs.length)).next + dY + i) zeroE := ⟨_, rfl⟩
  rw [← hends] at e3
  have e4 := row_ok (S0 := endTerm ends) (kept := {}) (t := u2) (p := P2) (F := G2) (G := G) f2' f3'
    f4' hz1 (by rw [hlen, hR2.first_eq]; exact hG)
  refine ⟨⟨P2.r.toList, (took (took F 1) (2 * zs.length)).next + dY, P2.rowForm (endTerm ends) {}⟩,
    G, u2, ?_, s2, ⟨k2, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold wholeStandIn
    rw [bind_eq e0, bind_eq e1, bind_eq e2]
    dsimp only
    rw [bind_eq (show (List.mapM (m := Fl) (fun i =>
      Fl.shown ((took (took F 1) (2 * zs.length)).next + dY + i)) (List.range n)) G2 u2 = _ from
          e3),
      bind_eq e4]
    rfl
  · rw [k1.next, g1.next, k1.ns, g1.ns]
    have := hFr.room
    show F.next + 1 + 2 * zs.length + dY + n + n' ≤ F.ns
    omega
  · intro j h1 h2
    rw [k1.next, g1.next] at h1 h2
    have h1' : F.next + 1 + 2 * zs.length + dY + n ≤ j := h1
    have h2' : j < F.next + 1 + 2 * zs.length + dY + n + n' := h2
    rw [(k4 j (Or.inr (by rw [Array.size_replicate]; omega))).2.2,
      (g4 j (Or.inr (by rw [hn1, hv]; omega))).2.2]
    exact hFr.free _ (by omega) (by omega)
  · rw [k1.next, g1.next]
    show F.next + 1 + 2 * zs.length + dY + n = _
    omega
  · exact (((PscRun.took_later F 1).trans (PscRun.took_later _ _)).trans
      ((PscRun.took_later _ dY).trans (PscRun.took_later _ n))).trans
      ((PscRun.hideRun_later hS1 hh).trans (PscRun.hideRun_later g2 hG))
  · intro i hi x hx
    obtain rfl : x = ((took (took F 1) (2 * zs.length)).next + dY + i, oneE) := by
      simpa [Aff.slot] using hx
    obtain ⟨c1, -, c3, -, -⟩ := g3 i (by rw [hv]; exact hi)
    exact ⟨by rw [k1.ns, g1.ns]; exact c1,
      ((PscRun.hideRun_later g2 hG).keep _ c3).1⟩
  · intro j hj
    rw [(k4 j (Or.inl hj)).2.2, (g4 j (Or.inl (by rw [hn1]; omega))).2.2]
    rfl
  · show P2.r.toList.length = _
    rw [Array.length_toList, hz1, hz2]
    simp

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.whole_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.loop2_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.ends_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.row_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.ran_walk_len
