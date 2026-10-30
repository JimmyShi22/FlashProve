-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPscForm.lean.
One sumcheck of the byte-level verifier, routine by routine, in the words in which the lookup's
routine is compared with the flat function: statements that chain.

Each takes a run of one routine that returns, and gives the calls on the channel (Evs), what the
sumcheck's own state holds (Ran, OnBytes/Tie/Pv/Psc/PscWhole.lean) and what the sub-proof's state
holds (Sized,
Later, FormIs, RowIs; the number of the next slot). A caller's own code may stand between them.
Each asks of the states before what the one before it gives: Sized, and behind the beginning Ran;
the claim's statements also ask FormIs of the start form in an earlier state, that the target reads
tg, and LedAt of the ledger's places; walk_len asks at least one variable.

* dgOf zd: the degrees: one less than each variable's number of coefficients.
* begin_form: pscBegin C, where C is read by FormIs ρ F C tg inc: the target reads tg; one slot.
* round_next: a round leaves took F (d - 1): the next slot's number behind it, from the one before.
* ends_form: pscEnds: each end value e + a is a form with what was sent for it as its public part
  and beta on mask entry e + a; Fork.shown (e + a) gives what was sent.
* psc_ends: the same on the ledger's places: [(L.sh a, beta)], where LedAt L first dg n.
* row_form: pscRow: no call on the channel; in every later state the claim's value is that of the
  flat function's row rowU L dg s inc S0, plus eps times the value of what is kept.
* psc_rowIs: with nothing kept: RowIs ρ G row (rowU L dg s inc S0), s what the flat step takeSc
  reads off the sumcheck's rounds as plain data.
* walk_len, ends_same, row_same: which fields turn and which slots are filled, exactly: pscEnds
  fills [e, e + n), pscRow fills [first, first + 1 + the degrees' sum); with filled_tile
  (OnBytes/Tie/Pv/Lookup/Forest/FoFork.lean) and e = first + 1 + the degrees' sum these two lie side
    by side. What lies under
  every other slot, free or filled, stays.
The rounds between are ran_roundIn2 and ran_roundIn of OnBytes/Tie/Pv/Psc/PscWhole.lean: they leave
took F n, so
took_sized and took_later carry Sized and Later over them. That the calls are rounds off the view:
OnBytes/Tie/Pv/Lookup/Forest/FoTook.lean.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoFork
import OnBytes.Tie.Pv.Lookup.Forest.FoLedAt

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

/-- The degrees. -/
def dgOf (zd : List (E × ℕ)) : List ℕ := zd.map (·.2 - 1)

theorem dgOf_snoc (zd : List (E × ℕ)) (z : E) (d : ℕ) :
    dgOf (zd ++ [(z, d)]) = dgOf zd ++ [d - 1] := by
  simp [dgOf]

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The beginning. -/
theorem begin_form {C : Aff} {F G : Fork} {c c' : Ctx} {p : Psc} {tg : K} {inc : List (Pl × K)}
    (h : pscBegin C F c = .ok ((p, G), c')) (hF : Sized F) (hC : FormIs ρ F C tg inc) :
    ∃ mu eps, Evs [.sum mu, .ans .pscEpsilon eps] c c' ∧ G = took F 1 ∧ Sized G ∧ Later F G ∧
      G.next = F.next + 1 + (dgOf []).sum ∧
      Ran p F.next mu eps [] [] ∧ p.start = C ∧ ρ.val p.target = tg ∧ p.started = true ∧
      p.ended = false ∧ p.rowMade = false := by
  obtain ⟨target, mu, eps, h1, h2, rfl, rfl⟩ := pscBegin_ok C F G c c' p h
  exact ⟨mu, eps, h2, rfl, took_sized 1 hF, took_later F 1, rfl,
    ran_begin C target mu eps F.next, rfl, (hC F (Later.refl F)).1 target h1, rfl, rfl, rfl⟩

/-- The book of slots over one round. -/
theorem round_next {F : Fork} {first : ℕ} {zd : List (E × ℕ)} (z : E) (d : ℕ)
    (hN : F.next = first + 1 + (dgOf zd).sum) :
    (took F (d - 1)).next = first + 1 + (dgOf (zd ++ [(z, d)])).sum := by
  rw [dgOf_snoc, List.sum_append]
  show F.next + (d - 1) = _
  rw [hN]
  simp
  omega

/-- The round in the further variable, and the end values. -/
theorem ends_form {p p' : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) {dY n e : ℕ} {F G : Fork} {c c' : Ctx}
    (h : pscEnds p dY n F c = .ok (((e, p'), G), c')) (hF : Sized F) :
    ∃ (sent : Array E) (beta : E) (v : Array E), sent.size = dY ∧ v.size = n ∧
      Evs [.read dY sent, .ansNZ .pscY beta, .read n v, .empty .pscValues] c c' ∧
      e = F.next + dY ∧ Later F G ∧ Sized G ∧ G.next = F.next + (dY + n) ∧
      p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = true ∧
      Ran p' first mu eps (zd ++ [(zeroE, dY + 1)]) (rs ++ [(sent.toList, beta)]) ∧
      ∀ a, a < n → FormIs ρ G (Aff.slot (e + a)) (ρ.val (v.getD a zeroE))
          [(Pl.mask (e + a), ρ.val beta)] ∧ G.shown (e + a) = some (v.getD a zeroE) := by
  obtain ⟨sent, beta, v, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    ran_ends hp dY n F G c c' e p' h
  obtain ⟨b1, b2, b3, b4⟩ := ends_fork ρ hF a2 a5
  exact ⟨sent, beta, v, a1, a2, a3, a4, b1, b2, b3, a6, a7, a8, a9, a10, a11, b4⟩

/-- An end value on the ledger's place. e: the slot that pscEnds returns, from a state whose next
slot is first + 1 + the degrees so far. -/
theorem psc_ends {G : Fork} {first dY n e a : ℕ} {zd : List (E × ℕ)} {next : ℕ} {y beta : E}
    {L : Led Pl} (hL : LedAt L first (dgOf (zd ++ [(zeroE, dY + 1)])) n)
    (hN : next = first + 1 + (dgOf zd).sum) (he : e = next + dY) (ha : a < n)
    (hf : FormIs ρ G (Aff.slot (e + a)) (ρ.val y) [(Pl.mask (e + a), ρ.val beta)]) :
    FormIs ρ G (Aff.slot (e + a)) (ρ.val y) [(L.sh a, ρ.val beta)] := by
  have : L.sh a = Pl.mask (e + a) := by
    rw [hL.sh a ha, dgOf_snoc, List.sum_append, he, hN]
    simp
    omega
  rw [this]
  exact hf

/-- The claim. F0: the state in which the start's form was read. -/
theorem row_form {p p' : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) {S0 : E} {kept row : Aff}
    {F0 F G : Fork} {c c' : Ctx} (h : pscRow p S0 kept F c = .ok (((row, p'), G), c'))
    {tg : K} {inc : List (Pl × K)} (hC : FormIs ρ F0 p.start tg inc) (ht : ρ.val p.target = tg)
    (h0 : Later F0 F) (hF : Sized F) {L : Led Pl} {n : ℕ} (hL : LedAt L first (dgOf zd) n)
    (vals : List K) :
    c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧ p' = { p with rowMade := true } ∧
      ∀ H, Later G H → ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
        row.value ρ (H.worldOf ρ mask entry) =
          rowRes (muOf mask) (rowU L (dgOf zd)
            ⟨ρ.val p.eps, p.r.toList.map ρ.val, ρ.val p.claim, vals⟩ inc (ρ.val S0)) +
            ρ.val eps * kept.value ρ (H.worldOf ρ mask entry) := by
  obtain ⟨_, _, _, _, a5, a6, rfl, a8⟩ := pscRow_ok p S0 kept F G c c' row p' h
  rw [hp.first_eq] at a6
  obtain ⟨b1, b2, b3, _⟩ := row_fork ρ hF a6
  have hlen : (p.r.toList.map ρ.val).length = (dgOf zd).length := by
    rw [List.length_map, hp.r_eq, List.length_map, dgOf, List.length_map, hp.fits.length]
  exact ⟨a5, b1, b2, b3, a8, fun H hH mask entry =>
    row_is ρ hp hC ht h0 hF a6 S0 kept L (fun mask => hL.hide K _ mask hlen) vals H hH mask entry⟩

/-- The claim of a sumcheck in which nothing is kept is the flat function's row. -/
theorem psc_rowIs {p p' : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) {S0 : E} {row : Aff}
    {F0 F G : Fork} {c c' : Ctx} (h : pscRow p S0 {} F c = .ok (((row, p'), G), c'))
    {inc : List (Pl × K)} (hC : FormIs ρ F0 p.start (ρ.val p.target) inc)
    (h0 : Later F0 F) (hF : Sized F) {L : Led Pl} {n : ℕ} (hL : LedAt L first (dgOf zd) n)
    (values : Option (List E)) (rest : Rounds K) :
    c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧ p' = { p with rowMade := true } ∧
      RowIs ρ G row (rowU L (dgOf zd)
        (takeSc (flH ρ mu eps rs values ++ rest) (ρ.val p.target) (zd.map fun x => ρ.val x.1)
          values.isSome).1 inc (ρ.val S0)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ :=
    row_form ρ hp h hC rfl h0 hF hL ((values.getD []).map ρ.val)
  refine ⟨a1, a2, a3, a4, a5, fun H hH mask entry => ?_⟩
  rw [a6 H hH mask entry, ran_takeSc ρ hp values rest, Aff.value_empty, mul_zero, add_zero]

/-! ### which fields turn, and which slots are filled, exactly -/

/-- The walk has one weight for each coefficient of the hiding polynomial. -/
theorem walk_len {p : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)} {rs : List (List E × E)}
    (hp : Ran p first mu eps zd rs) (hz : zd ≠ []) : p.walk.1.length = 1 + (dgOf zd).sum := by
  have h1 := congrArg List.length (ran_walk Reading.gl hp).1
  rw [List.length_map] at h1
  have hw : (zd.zip rs).map (fun x => (x.1.2, Reading.gl.val x.2.2)) =
      Cb.Fo.Walk.pairs (dgOf zd) (rs.map fun r => Reading.gl.val r.2) := by
    unfold Cb.Fo.Walk.pairs dgOf
    rw [List.map_map, List.zip_map]
    refine List.map_congr_left fun x hx => ?_
    have := fits_pos hp.fits x.1 (List.of_mem_zip hx).1
    show _ = (x.1.2 - 1 + 1, Reading.gl.val x.2.2)
    rw [Nat.sub_add_cancel this]
  rw [h1, hw, Cb.Fo.Walk.walk_length _ _ (by simpa [dgOf] using hz)
    (by rw [List.length_map, dgOf, List.length_map, hp.fits.length])]

/-- Behind pscEnds: no field turns but what lies under the slots and the number of the next slot;
the slots of the end values are filled, and no other. -/
theorem ends_same {p p' : Psc} {dY n e : ℕ} {F G : Fork} {c c' : Ctx}
    (h : pscEnds p dY n F c = .ok (((e, p'), G), c')) (hF : Sized F) :
    Same (took F (dY + n)) G ∧ (∀ j, Filled G j ↔ Filled F j ∨ (e ≤ j ∧ j < e + n)) ∧
      ∀ j, (j < e ∨ e + n ≤ j) →
        G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE := by
  obtain ⟨_, _, v, _, _, _, _, hv, _, _, hG, _⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h
  obtain ⟨a, b, b'⟩ := hideRun_filled (took_sized (dY + n) hF) hG
  rw [hv] at b b'
  exact ⟨a, b, b'⟩

/-- Behind pscRow: no field turns but what lies under the slots; the slots of the hiding
polynomial's coefficients are filled, and no other. -/
theorem row_same {p p' : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) {S0 : E} {kept row : Aff}
    {F G : Fork} {c c' : Ctx} (h : pscRow p S0 kept F c = .ok (((row, p'), G), c'))
    (hF : Sized F) :
    Same F G ∧ (∀ j, Filled G j ↔ Filled F j ∨ (first ≤ j ∧ j < first + (1 + (dgOf zd).sum))) ∧
      ∀ j, (j < first ∨ first + (1 + (dgOf zd).sum) ≤ j) →
        G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE := by
  obtain ⟨_, _, a3, _, _, a6, _, _⟩ := pscRow_ok p S0 kept F G c c' row p' h
  have hz : zd ≠ [] := by
    intro e
    have hv := hp.vars_eq
    rw [e] at hv
    have : p.vars.isEmpty = true := by
      rw [Array.isEmpty_iff]
      exact Array.toList_eq_nil_iff.1 hv
    rw [this] at a3
    cases a3
  obtain ⟨a, b, b'⟩ := hideRun_filled hF a6
  rw [Array.size_replicate, walk_len hp hz, hp.first_eq] at b b'
  exact ⟨a, b, b'⟩

end
end Fo
