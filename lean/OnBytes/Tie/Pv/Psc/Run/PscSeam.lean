-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscSeam.lean: from successes of pscBegin, of rounds and of pscEnds, one set
of witnesses for what was heard, for the sumcheck's record and for the state.

The routines are those of OnBytes/Model/Psc.lean; what was heard is said in the words of the block's
listener (OnBytes/Iop/Psc.lean). Scalars before mu in the first message are called riders.

Main names:
  `Ran p C τ mu eps first ws rs`: the record p of a sumcheck behind pscBegin and the rounds rs.
    `Ran.begun`, `Ran.step`.
  `Ended`: the record behind pscEnds, with the walk and its length. `Ran.ends`.
  `Parts c c1 c' …`: what was heard from c to c': the riders from c to c1, then from c1 the round
    PSC epsilon with the one scalar that is left, the variables' rounds, the round in Y, the end
    values and their closing.
  `Parts.whole`: the first round heard whole from c, with the riders and then mu.
  `Parts.verify`: the block's Psc.verify succeeds from c1, and Psc.run gives the named term outW.
  `seam`: riders received, and successes of pscBegin, of rounds (Stepped) and of pscEnds, give
    Parts, Ran, Ended, the lengths and the state (Filled).
  `Filled.masks`: after a filling with zeros under the factor -1, the value under each slot in the
    world of Fork.worldOf is that slot's mask entry.
  `pscRow_filled`: pscRow on a run, with its filling.
Limits: one direction only, from the model's routines to the block's listener. No statement has a
hypothesis on whether the channel is a view or the dry run. Nothing is said on hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscRow
import OnBytes.Tie.Pv.Psc.Run.PscHide
import OnBytes.Tie.Pv.Psc.Run.PscPure

set_option autoImplicit false

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany hear claimAfter polyAt hidingWalk hidingEntries)

/-! ## The record -/

/-- p: a sumcheck on the claim C with public target τ, begun with mu and eps at the slot first,
after the rounds rs
under the weights ws. -/
structure Ran (p : Psc) (C : Aff) (τ mu eps : E) (first : Nat) (ws : List Weight)
    (rs : List (List E × E)) : Prop where
  claim : p.claim = claimAfter ws rs (addE mu (mulE eps τ))
  vars : p.vars.toList = ws
  r : p.r.toList = rs.map (·.2)
  start : p.start = C
  target : p.target = τ
  eps : p.eps = eps
  first : p.first = first
  started : p.started = true
  ended : p.ended = false
  rowMade : p.rowMade = false
  len : rs.length = ws.length
  sizes : ∀ x ∈ ws.zip rs, x.2.1.length + 1 = x.1.d
  held : ∀ w ∈ ws, w.fits = true ∧ weightHeld w = true

theorem Ran.begun (p0 : Psc) (C : Aff) (τ mu : E) (first : Nat)
    (h : p0 = { start := C, started := true, target := τ, first := first, eps := p0.eps,
                claim := addE mu (mulE p0.eps τ) }) : Ran p0 C τ mu p0.eps first [] [] where
  claim := by conv => lhs; rw [h]
              rfl
  vars := by rw [h]
  r := by rw [h]; rfl
  start := by rw [h]
  target := by rw [h]
  eps := rfl
  first := by rw [h]
  started := by rw [h]
  ended := by rw [h]
  rowMade := by rw [h]
  len := rfl
  sizes := by simp
  held := by simp

theorem Ran.step {p p' : Psc} {C : Aff} {τ mu eps : E} {first : Nat} {ws ws' : List Weight}
    {rs rs' : List (List E × E)} (a : Ran p C τ mu eps first ws rs) (s : Stepped p p' ws' rs') :
    Ran p' C τ mu eps first (ws ++ ws') (rs ++ rs') where
  claim := by rw [s.claim, a.claim, claimAfter_app _ _ _ _ _ a.len]
  vars := by rw [s.vars, a.vars]
  r := by rw [s.r, a.r, List.map_append]
  start := s.start.trans a.start
  target := s.target.trans a.target
  eps := s.eps.trans a.eps
  first := s.first.trans a.first
  started := s.started.trans a.started
  ended := s.ended.trans a.ended
  rowMade := s.rowMade.trans a.rowMade
  len := by simp [a.len, s.len]
  sizes := by
    intro x hx
    rw [List.zip_append a.len.symm] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact a.sizes x hx
    · exact s.sizes x hx
  held := by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact a.held w hw
    · exact s.held w hw

/-- p: the same sumcheck behind pscEnds. -/
structure Ended (p : Psc) (C : Aff) (τ mu eps : E) (first : Nat) (ws : List Weight)
    (rs : List (List E × E)) (dY : Nat) (sentY : List E) (beta : E) : Prop where
  claim : p.claim = claimAfter (ws ++ [Weight.atZero (dY + 1)]) (rs ++ [(sentY, beta)])
    (addE mu (mulE eps τ))
  walk : p.walk = hidingWalk ((ws ++ [Weight.atZero (dY + 1)]).zip (rs.map (·.2) ++ [beta]))
  walkLen : p.walk.1.length = hidingEntries (ws ++ [Weight.atZero (dY + 1)])
  vars : p.vars.toList = ws ++ [Weight.atZero (dY + 1)]
  r : p.r.toList = rs.map (·.2) ++ [beta]
  start : p.start = C
  target : p.target = τ
  eps : p.eps = eps
  first : p.first = first
  started : p.started = true
  ended : p.ended = true
  rowMade : p.rowMade = false

theorem fits_d {w : Weight} (h : w.fits = true) : 2 ≤ w.d := by
  unfold Weight.fits at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem Ran.ends {p1 p2 : Psc} {C : Aff} {τ mu eps : E} {first : Nat} {ws : List Weight}
    {rs : List (List E × E)} (a : Ran p1 C τ mu eps first ws rs) (dY : Nat) (sentY : List E) (beta :
        E)
    (h : p2 = { p1 with claim := polyAt ((Weight.atZero (dY + 1)).complete sentY p1.claim) beta,
                        vars := p1.vars.push (Weight.atZero (dY + 1)), r := p1.r.push beta,
                        ended := true }) : Ended p2 C τ mu eps first ws rs dY sentY beta := by
  have hw : p2.walk = hidingWalk ((ws ++ [Weight.atZero (dY + 1)]).zip (rs.map (·.2) ++ [beta])) :=
      by
    rw [h]
    unfold Psc.walk
    rw [zipT_eq]
    simp only [Array.toList_push, a.vars, a.r]
  refine ⟨?_, hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [claimAfter_append ws rs _ _ _ a.len, h, ← a.claim]
  · rw [hw]
    refine walk_length _ _ (by simp) (by simp [a.len]) ?_
    intro w hwm
    rcases List.mem_append.1 hwm with hwm | hwm
    · have := fits_d (a.held w hwm).1; omega
    · rw [List.mem_singleton.1 hwm]
      show 1 ≤ dY + 1
      omega
  · rw [h]; simp only [Array.toList_push, a.vars]
  · rw [h]; simp only [Array.toList_push, a.r]
  · rw [h]; exact a.start
  · rw [h]; exact a.target
  · rw [h]; exact a.eps
  · rw [h]; exact a.first
  · rw [h]; exact a.started
  · rw [h]
  · rw [h]; exact a.rowMade

/-! ## What was heard -/

/-- The rounds of one sumcheck with end values, heard from c to c': the riders are received from c
to c1; from c1
the round "PSC epsilon" is heard with the one scalar that is left; then the rounds of the variables,
the round in
Y, the end values and their closing. -/
def Parts (c c1 c' : Ctx) (riders : List E) (mu eps : E) (ws : List Weight) (rs : List (List E × E))
    (dY : Nat) (sentY : List E) (beta : E) (v : List E) : Prop :=
  ∃ c2 c3 c4 c5,
    (Blk.recvEs riders.length).Yields c riders c1 ∧
    (hearOne "PSC epsilon" .join 1 0).Yields c1 ([mu], eps) c2 ∧
    (hearMany (ws.map fun w => w.d - 1)).Yields c2 rs c3 ∧
    (hearOne "PSC Y" .elems dY 1).Yields c3 (sentY, beta) c4 ∧
    (Blk.recvEs v.length).Yields c4 v c5 ∧ (Blk.closeEmpty "PSC values").Yields c5 () c'

theorem recvEs_zero (c : Ctx) : (Blk.recvEs 0).Yields c [] c := by
  unfold Blk.recvEs
  refine (Blk.yields_bind _ _ _ _ _).2 ⟨#[], c, ?_, (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩⟩
  simp only [Blk.recvEsInto]
  exact (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩

/-- The first round whole, from c: all that was received from c on: the riders, then mu. -/
theorem Parts.whole {c c1 c' : Ctx} {riders : List E} {mu eps : E} {ws : List Weight}
    {rs : List (List E × E)} {dY : Nat} {sentY : List E} {beta : E} {v : List E}
    (a : Parts c c1 c' riders mu eps ws rs dY sentY beta v) :
    ∃ c2 c3 c4 c5,
      (hearOne "PSC epsilon" .join (riders.length + 1) 0).Yields c (riders ++ [mu], eps) c2 ∧
      (hearMany (ws.map fun w => w.d - 1)).Yields c2 rs c3 ∧
      (hearOne "PSC Y" .elems dY 1).Yields c3 (sentY, beta) c4 ∧
      (Blk.recvEs v.length).Yields c4 v c5 ∧ (Blk.closeEmpty "PSC values").Yields c5 () c' := by
  obtain ⟨c2, c3, c4, c5, h0, h1, h2, h3, h4, h5⟩ := a
  exact ⟨c2, c3, c4, c5, hearOne_riders _ _ _ _ _ _ _ h0 h1, h2, h3, h4, h5⟩

/-- The block's Psc.verify from the context behind the riders, with what it hands on by name, for
any mask form, any summand and any list of slots of fitting sizes. -/
theorem Parts.verify {c c1 c' : Ctx} {riders : List E} {mu eps : E} {ws : List Weight}
    {rs : List (List E × E)} {sentY : List E} {beta : E} {v : List E} (S : OnBytes.Psc.Summand)
    (a : Parts c c1 c' riders mu eps ws rs S.degree sentY beta v) (m : MaskForm) (τ : E) (fresh :
        List Slot)
    (len : rs.length = ws.length) (sizes : ∀ x ∈ ws.zip rs, x.2.1.length + 1 = x.1.d)
    (fits : ∀ w ∈ ws, w.fits = true) (hY : sentY.length = S.degree) (hv : v.length = S.shown)
    (d1 : 1 ≤ S.degree) (n1 : 1 ≤ S.shown)
    (hf : fresh.length = OnBytes.Psc.masksOf ⟨ws, m, τ⟩ S)
    (ha : (S.coeffs (rs.map (·.2)) v).length = 1 + S.kept) :
    (Blk.recvEs riders.length).Yields c riders c1 ∧
      (OnBytes.Psc.verify ⟨ws, m, τ⟩ S fresh).Yields c1
        (outW ⟨ws, m, τ⟩ S fresh (heardOf mu eps rs sentY beta v)) c' ∧
      OnBytes.Psc.run ⟨ws, m, τ⟩ S fresh (heardOf mu eps rs sentY beta v) =
        some (outW ⟨ws, m, τ⟩ S fresh (heardOf mu eps rs sentY beta v)) := by
  obtain ⟨c2, c3, c4, c5, h0, h1, h2, h3, h4, h5⟩ := a
  have hr := run_of_sizes ws m τ S fresh mu eps beta rs sentY v len sizes fits hY hv d1 n1 hf ha
  have htake : ((rs.map (·.2)) ++ [beta]).take ws.length = rs.map (·.2) := by
    rw [List.take_append_of_le_length (by simp [len]), List.take_of_length_le (by simp [len])]
  rw [hv] at h4
  obtain ⟨o, y, ho⟩ := verify_of ws m τ S fresh mu eps beta rs sentY v c1 c2 c3 c4 c5 c' h1 h2 h3 h4
      h5
    len sizes fits hY hv d1 n1 hf (by rw [htake]; exact ha)
  rw [hr] at ho
  rw [← Option.some.inj ho] at y
  exact ⟨h0, y, hr⟩

/-! ## The seam -/

theorem sized_taken (F : Fork) (n : Nat) (h : Sized F) : Sized (taken F n) := ⟨h.vp, h.mf, h.got⟩

/-- The seam. Riders were received from c to c1; pscBegin C succeeded from (F1, c1); rounds were
heard from c2 to c3 that stepped its record from p0 to p1; pscEnds succeeded from (F3, c3). -/
theorem seam (riders : List E) (C : Aff) (p0 p1 p2 : Psc) (ws : List Weight) (rs :
    List (List E × E))
    (dY n e : Nat) (F1 F2 F3 G : Fork) (c c1 c2 c3 c' : Ctx)
    (hr : (Blk.recvEs riders.length).Yields c riders c1)
    (hb : pscBegin C F1 c1 = .ok ((p0, F2), c2))
    (hm : (hearMany (ws.map fun w => w.d - 1)).Yields c2 rs c3) (hs : Stepped p0 p1 ws rs)
    (he : pscEnds p1 dY n F3 c3 = .ok (((e, p2), G), c')) (hz : Sized F3) :
    ∃ (τ mu : E) (sentY : List E) (beta : E) (v : List E),
      F1.publicPart C = some τ ∧ F2 = taken F1 1 ∧
      Parts c c1 c' riders mu p0.eps ws rs dY sentY beta v ∧
      Ran p1 C τ mu p0.eps F1.next ws rs ∧
      Ended p2 C τ mu p0.eps F1.next ws rs dY sentY beta ∧
      sentY.length = dY ∧ v.length = n ∧ 1 ≤ dY ∧ 1 ≤ n ∧ e = F3.next + dY ∧
      Filled (taken F3 (dY + n)) G e v beta := by
  obtain ⟨τ, mu, pc, yc, hp0, Gc⟩ := pscBegin_ok C F1 F2 c1 c2 p0 hb
  obtain ⟨sentY, beta, v, c5, c6, y5, y6, y7, sv, d1, n1, _, sY, hp2, hE, HG⟩ :=
    pscEnds_ok p1 p2 dY n F3 G c3 c' e he
  have ran : Ran p1 C τ mu p0.eps F1.next ws rs := by
    have := (Ran.begun p0 C τ mu F1.next hp0).step hs
    simpa using this
  have lv : v.toList.length = n := by simpa using sv
  refine ⟨τ, mu, sentY, beta, v.toList, pc, Gc, ⟨c2, c3, c5, c6, hr, yc, hm, y5,
      by rw [lv]; exact y6, y7⟩, ran,
    ran.ends dY sentY beta hp2, sY, lv, d1, n1, hE, hideRun_ok _ _ _ _ _ HG (sized_taken F3 _ hz)⟩

/-- A filling with zeros under the factor -1: the hidden value under each slot is that slot's mask
entry. -/
theorem Filled.masks {K : Type} [CommRing K] (ρ : Reading K) {F G : Fork} {first n : Nat}
    (a : Filled F G first (List.replicate n zeroE) (subE zeroE oneE)) (mask : Nat → K)
    (entry : Nat → Nat → Nat → K) (i : Nat) (hi : i < n) :
    (G.worldOf ρ mask entry).slot (first + i) = mask (first + i) := by
  have hz : (List.replicate n zeroE).getD i zeroE = zeroE := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  rw [a.world ρ mask entry i (by simpa using hi), hz, ρ.sub, ρ.zero, ρ.one]
  ring

/-- pscRow on a run, with the filling. -/
theorem pscRow_filled (p p' : Psc) (S0 : E) (kept row : Aff) (F G : Fork) (c c' : Ctx)
    (h : pscRow p S0 kept F c = .ok (((row, p'), G), c')) (hs : Sized F) :
    c' = c ∧ row = p.rowForm S0 kept ∧ p' = { p with rowMade := true } ∧
      Filled F G p.first (List.replicate p.walk.1.length zeroE) (subE zeroE oneE) := by
  obtain ⟨a1, a2, a3, _, _, _, _, H⟩ := pscRow_ok p p' S0 kept row F G c c' h
  have f := hideRun_ok _ _ _ _ _ H hs
  rw [Array.toList_replicate] at f
  exact ⟨a1, a2, a3, f⟩

#print axioms seam
#print axioms Parts.verify
#print axioms Parts.whole
#print axioms Filled.masks

end OnBytes.Model.Road
