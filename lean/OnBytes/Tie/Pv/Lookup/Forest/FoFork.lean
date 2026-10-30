-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoFork.lean.
One sumcheck of the byte-level verifier: what its routines do to the state of the sub-proof.

The run-lemmas of OnBytes/Tie/Pv/Psc/PscRun.lean and OnBytes/Tie/Pv/Psc/PscWhole.lean say of each
routine which state (Fork) it
leaves: took F n (n more slots taken), or a state G with F.hideRun first v factor = some G.
OnBytes/Tie/Pv/Psc/PscFork.lean says what then lies under the slots. This file reads both in the
words of
OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean (Later, FormIs, RowIs), in which the stretches of the
lookup's routine are compared
with the flat function.

* hideRun_filled: which slots a run of hideRun fills, exactly; no other field turns. filled_tile:
  the end values' slots and the hiding polynomial's lie side by side.
* ends_fork: behind pscEnds: the state is later and sized, degreeInY + n more slots are taken, and
  the slot e + a of each end value is a form with what was sent for it as its public part and beta
  on mask entry e + a (FormIs); Fork.shown (e + a) gives what was sent.
* row_fork: behind pscRow: the state is later and sized, no slot more is taken, and in every later
  state the hidden value under slot first + i is the mask entry first + i.
* row_value: the value of the claim that a sumcheck leaves, in every later state: the walk's
  weights on the mask entries from first on, plus eps times the incoming sparse form, plus eps
  times what is kept, less (claim - eps S0).
* row_is: so the claim is the flat function's row rowU L dg s inc S0 plus eps times what is kept,
  if the ledger L puts the hiding polynomial's coefficients under the slots from first on in the
  order of the verifier's walk (a premise here; OnBytes/Tie/Pv/Lookup/Forest/FoWalk.lean and
    OnBytes/Tie/Pv/Lookup/Forest/FoWalkLed.lean show it of the
  lookup's own ledgers).
Further premises: the state before fits (Sized) and hideRun returns; in row_value and row_is also
Ran of the sumcheck's state, FormIs of its start form in an earlier state, and that its target
reads tg.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieKit
import OnBytes.Tie.Pv.Psc.PscFork
import OnBytes.Tie.Pv.Psc.PscWhole

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

/-- Each variable has a coefficient. -/
theorem fits_pos : ∀ {zd : List (E × ℕ)} {rs : List (List E × E)}, Fits zd rs → ∀ x ∈ zd, 1 ≤ x.2
  | [], [], _, _, hx => absurd hx List.not_mem_nil
  | p :: _, _ :: _, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · have := h.1
      omega
    · exact fits_pos h.2 x hx
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- What a run of hideRun fills, exactly; all other fields stay, and so does what lies under the
other slots, free or filled. -/
theorem hideRun_filled {F G : Fork} {first : ℕ} {v : Array E} {f : E} (hF : Sized F)
    (h : F.hideRun first v f = some G) :
    Same F G ∧ (∀ j, Filled G j ↔ Filled F j ∨ (first ≤ j ∧ j < first + v.size)) ∧
      ∀ j, (j < first ∨ first + v.size ≤ j) →
        G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE := by
  obtain ⟨hS, _, hnew, hold⟩ := hideRun_ok F G first v f hF h
  refine ⟨hS, fun j => ?_, fun j hj => ⟨(hold j hj).1, (hold j hj).2.1⟩⟩
  by_cases hin : first ≤ j ∧ j < first + v.size
  · have h3 := (hnew (j - first) (by omega)).2.2.1
    rw [Nat.add_sub_cancel' hin.1] at h3
    exact ⟨fun _ => .inr hin, fun _ => h3⟩
  · have hout : j < first ∨ first + v.size ≤ j := by omega
    exact ⟨fun hj => .inl ((hold j hout).2.2.1 hj), fun hj => hj.elim (hold j hout).2.2.2
      fun hc => absurd hc hin⟩

/-- The slots of the end values and the slots of the hiding polynomial lie side by side. -/
theorem filled_tile {F0 G1 G : Fork} {first len e n : ℕ}
    (h1 : ∀ j, Filled G1 j ↔ Filled F0 j ∨ (e ≤ j ∧ j < e + n))
    (h2 : ∀ j, Filled G j ↔ Filled G1 j ∨ (first ≤ j ∧ j < first + len)) (he : e = first + len) :
    ∀ j, Filled G j ↔ Filled F0 j ∨ (first ≤ j ∧ j < first + (len + n)) := by
  intro j
  rw [h2 j, h1 j, he]
  constructor
  · rintro ((h | h) | h)
    · exact .inl h
    · exact .inr ⟨by omega, by omega⟩
    · exact .inr ⟨h.1, by omega⟩
  · rintro (h | h)
    · exact .inl (.inl h)
    · by_cases hc : j < first + len
      · exact .inr ⟨h.1, hc⟩
      · exact .inl (.inr ⟨by omega, by omega⟩)

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- Behind pscEnds. -/
theorem ends_fork {F G : Fork} {dY n e : ℕ} {v : Array E} {beta : E} (hF : Sized F)
    (hv : v.size = n) (h : (took F (dY + n)).hideRun e v beta = some G) :
    Later F G ∧ Sized G ∧ G.next = F.next + (dY + n) ∧
      ∀ a, a < n → FormIs ρ G (Aff.slot (e + a)) (ρ.val (v.getD a zeroE))
          [(Pl.mask (e + a), ρ.val beta)] ∧ G.shown (e + a) = some (v.getD a zeroE) := by
  have hT : Sized (took F (dY + n)) := took_sized _ hF
  obtain ⟨hS, hG, hnew, _⟩ := hideRun_ok _ G e v beta hT h
  refine ⟨(took_later F _).trans (hideRun_later hT h), hG, hS.next, fun a ha => ?_⟩
  obtain ⟨c1, _, c3, c4, c5⟩ := hnew a (by omega)
  have c1' : e + a < G.ns := by rw [hS.ns]; exact c1
  have hs := slot_formIs ρ c3
  rw [c4, c5] at hs
  refine ⟨hs, ?_⟩
  unfold Fork.shown
  have c3' : G.gotF.getD (e + a) false = true := c3
  simp [c1', c3', c4]

/-- Behind pscRow: the hiding polynomial's coefficients lie under their slots. -/
theorem row_fork {F G : Fork} {first len : ℕ} (hF : Sized F)
    (h : F.hideRun first (Array.replicate len zeroE) (subE zeroE oneE) = some G) :
    Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∀ H, Later G H → ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (i : ℕ), i < len →
        (H.worldOf ρ mask entry).slot (first + i) = mask (first + i) := by
  obtain ⟨hS, hG, hnew, _⟩ := hideRun_ok F G first _ _ hF h
  refine ⟨hideRun_later hF h, hG, hS.next, fun H hH mask entry i hi => ?_⟩
  obtain ⟨_, _, c3, c4, c5⟩ := hnew i (by simpa using hi)
  obtain ⟨_, d2, d3⟩ := hH.keep (first + i) c3
  show ρ.val (H.vp.getD (first + i) zeroE) - ρ.val (H.mf.getD (first + i) zeroE) * mask (first + i)
    = _
  have c4' : G.vp.getD (first + i) zeroE = zeroE := by
    rw [c4]
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [d2, d3, c4', c5, ρ.sub, ρ.zero, ρ.one]
  ring

theorem sumFrom_congr {α : Type} (g g' : ℕ → α → K) : ∀ (l : List α) (s : ℕ),
    (∀ i, i < l.length → ∀ x, g (s + i) x = g' (s + i) x) → sumFrom g s l = sumFrom g' s l
  | [], _, _ => rfl
  | x :: l, s, h => by
    have h0 : g s x = g' s x := h 0 (by simp) x
    have h1 : sumFrom g (s + 1) l = sumFrom g' (s + 1) l :=
      sumFrom_congr g g' l (s + 1) fun i hi y => by
        have := h (i + 1) (by simpa using hi) y
        rwa [show s + (i + 1) = s + 1 + i by omega] at this
    simp only [sumFrom]
    rw [h0, h1]

theorem sumFrom_map {α : Type} (f : α → K) (m : ℕ → K) : ∀ (l : List α) (s : ℕ),
    sumFrom (fun j x => f x * m j) s l = sumFrom (fun j x => x * m j) s (l.map f)
  | [], _ => rfl
  | x :: l, s => by
    simp only [sumFrom, List.map_cons]
    rw [sumFrom_map f m l (s + 1)]

/-- The value of the claim that a sumcheck leaves, in every later state. F0: the state in which
the start's form was read. -/
theorem row_value {p : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)} {rs : List (List E × E)}
    (hp : Ran p first mu eps zd rs) {F0 F G : Fork} {tg : K} {inc : List (Pl × K)}
    (hC : FormIs ρ F0 p.start tg inc) (ht : ρ.val p.target = tg) (h0 : Later F0 F) (hF : Sized F)
    (h : F.hideRun first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G)
    (S0 : E) (kept : Aff) (H : Fork) (hH : Later G H) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) :
    (p.rowForm S0 kept).value ρ (H.worldOf ρ mask entry) =
      sumFrom (fun j x => x * mask j) first
          (walkK ((zd.zip rs).map fun x => (x.1.2, ρ.val x.2.2))) +
        ρ.val eps * evalL (muOf mask) inc + ρ.val eps * kept.value ρ (H.worldOf ρ mask entry) -
        (ρ.val p.claim - ρ.val eps * ρ.val S0) := by
  obtain ⟨hL, _, _, hs⟩ := row_fork ρ hF h
  rw [ran_row ρ hp, (hC H ((h0.trans hL).trans hH)).2 mask entry, ht, ← (ran_walk ρ hp).1,
    ← sumFrom_map,
    sumFrom_congr _ (fun j x => ρ.val x * mask j) p.walk.1 first fun i hi x => by
      rw [hs H hH mask entry i hi]]
  ring

/-- The claim that a sumcheck leaves is the flat function's row, plus eps times what is kept.
The record of the flat step is the one that ran_takeSc reads off the same rounds. dg: the degrees:
one less than each variable's number of coefficients. hLed: the ledger L puts the hiding
polynomial's coefficients under the slots from first on, in the order of the verifier's walk. -/
theorem row_is {p : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)} {rs : List (List E × E)}
    (hp : Ran p first mu eps zd rs) {F0 F G : Fork} {tg : K} {inc : List (Pl × K)}
    (hC : FormIs ρ F0 p.start tg inc) (ht : ρ.val p.target = tg) (h0 : Later F0 F) (hF : Sized F)
    (h : F.hideRun first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G)
    (S0 : E) (kept : Aff) (L : Led Pl)
    (hLed : ∀ mask : ℕ → K,
      evalL (muOf mask) (hide L (zd.map (·.2 - 1)) (p.r.toList.map ρ.val)) =
        sumFrom (fun j x => x * mask j) first
          (walkK (((zd.map (·.2 - 1)).zip (p.r.toList.map ρ.val)).map fun y => (y.1 + 1, y.2))))
    (vals : List K) (H : Fork) (hH : Later G H) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) :
    (p.rowForm S0 kept).value ρ (H.worldOf ρ mask entry) =
      rowRes (muOf mask) (rowU L (zd.map (·.2 - 1))
        ⟨ρ.val p.eps, p.r.toList.map ρ.val, ρ.val p.claim, vals⟩ inc (ρ.val S0)) +
        ρ.val eps * kept.value ρ (H.worldOf ρ mask entry) := by
  have hw : ((zd.map (·.2 - 1)).zip (p.r.toList.map ρ.val)).map (fun y => (y.1 + 1, y.2)) =
      (zd.zip rs).map fun x => (x.1.2, ρ.val x.2.2) := by
    rw [hp.r_eq, List.map_map, List.zip_map, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    have := fits_pos hp.fits x.1 (List.of_mem_zip hx).1
    show (x.1.2 - 1 + 1, ρ.val x.2.2) = _
    rw [Nat.sub_add_cancel this]
  rw [row_value ρ hp hC ht h0 hF h S0 kept H hH mask entry]
  unfold rowRes rowU
  simp only
  rw [evalL_append, evalL_scale, hLed mask, hw, hp.eps_eq]
  ring

end
end Fo
