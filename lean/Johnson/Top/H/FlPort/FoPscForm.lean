-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPscForm.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPscForm.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  begin_form, ends_form, row_form, psc_rowIs, ends_same, row_same
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Filled, FormIs, Later, Later.refl, LedAt, RowIs, Same, Sized, dgOf, ends_fork, hideRun_filled,
  muOf, ran_begin, ran_takeSc, rowRes, row_fork, row_is, took, took_later, took_sized, walk_len
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPscForm
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoTieRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The beginning. -/
theorem begin_form {C : Aff} {F G : Fork} {c c' : Tape} {p : Psc} {tg : K} {inc : List (Pl × K)}
    (h : Fl.pscBegin C F c = .ok ((p, G), c')) (hF : Sized F) (hC : FormIs ρ F C tg inc) :
    ∃ mu eps, Evs [.sum mu, .ans .pscEpsilon eps] c c' ∧ G = took F 1 ∧ Sized G ∧ Later F G ∧
      G.next = F.next + 1 + (dgOf []).sum ∧
      Ran p F.next mu eps [] [] ∧ p.start = C ∧ ρ.val p.target = tg ∧ p.started = true ∧
      p.ended = false ∧ p.rowMade = false := by
  obtain ⟨target, mu, eps, h1, h2, rfl, rfl⟩ := pscBegin_ok C F G c c' p h
  exact ⟨mu, eps, h2, rfl, took_sized 1 hF, took_later F 1, rfl,
    ran_begin C target mu eps F.next, rfl, (hC F (Later.refl F)).1 target h1, rfl, rfl, rfl⟩

/-- The round in the further variable, and the end values. -/
theorem ends_form {p p' : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) {dY n e : ℕ} {F G : Fork} {c c' : Tape}
    (h : Fl.pscEnds p dY n F c = .ok (((e, p'), G), c')) (hF : Sized F) :
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

/-- The claim. F0: the state in which the start's form was read. -/
theorem row_form {p p' : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) {S0 : E} {kept row : Aff}
    {F0 F G : Fork} {c c' : Tape} (h : Fl.pscRow p S0 kept F c = .ok (((row, p'), G), c'))
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
    {F0 F G : Fork} {c c' : Tape} (h : Fl.pscRow p S0 {} F c = .ok (((row, p'), G), c'))
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

/-- Behind Fl.pscEnds: no field turns but what lies under the slots and the number of the next slot;
the slots of the end values are filled, and no other. -/
theorem ends_same {p p' : Psc} {dY n e : ℕ} {F G : Fork} {c c' : Tape}
    (h : Fl.pscEnds p dY n F c = .ok (((e, p'), G), c')) (hF : Sized F) :
    Same (took F (dY + n)) G ∧ (∀ j, Filled G j ↔ Filled F j ∨ (e ≤ j ∧ j < e + n)) ∧
      ∀ j, (j < e ∨ e + n ≤ j) →
        G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE := by
  obtain ⟨_, _, v, _, _, _, _, hv, _, _, hG, _⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h
  obtain ⟨a, b, b'⟩ := hideRun_filled (took_sized (dY + n) hF) hG
  rw [hv] at b b'
  exact ⟨a, b, b'⟩

/-- Behind Fl.pscRow: no field turns but what lies under the slots; the slots of the hiding
polynomial's coefficients are filled, and no other. -/
theorem row_same {p p' : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) {S0 : E} {kept row : Aff}
    {F G : Fork} {c c' : Tape} (h : Fl.pscRow p S0 kept F c = .ok (((row, p'), G), c'))
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

end Fo.Tp
