-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05MsgOnto.lean: the reading of the closed caller of the lookup on an
attention link's calls is onto. There is a tuple of messages with prescribed symbols and a
prescribed mask row, and so with prescribed small cells.

Definitions, statements and proofs.
Main names:
  `msgOf cs l seat tl y μr`: the tuple. In the main rows' tables it holds, at a seat at which some
    symbol address with a value that is not 0 sits, that value (one of them, by choice), and 0
    elsewhere. In the mask rows' tables entry (r, c) is μr c.
  `SymsSit cs l seat tl y`: three premises on public data and y. main: the seat of a symbol address
    lies in a main rows' table. seated: a symbol that is to be other than 0 has a seat that fits;
    one that is to be 0 may have none, for the reading's default is 0. apart: two symbol addresses
    with one seat are to hold one value.
  `symAt_msgOf`: under `SymsSit`, symAt cs l seat tl (msgOf …) = y.
  `packOf Z`, `cellValS_pack`: the cells behind the packing of small integer matrices are their
    entries (`packs_unique`, Cb/Pv/Tail/Unique.lean).
  `cells_msgOf`: for small Z and `SymsSit` at packOf Z, msgAtt … (msgOf …) (some (.inr j)) = Z j.1
    j.2.1 j.2.2 at every cell j.
  `seatCalls_main`: the first premise holds of the caller's `seatCalls`, by its text.
  `maskOf_msgOf`: under a yes of `masksUpTo` D x hi (Johnson/Desc/First/Att/K05MasksAtt.lean),
    attLin0.maskOf (msgOf …) j = μr j for j < hi. The mask row and the symbols are free of each
    other.
What it is for: a member whose out-statement is what the lookup leaves. The plan: rounds with a yes
of the lookup's decision; x0 the written out-statement at these rounds, whose target is then fixed;
m with chosen cells and a mask row that is 0 but at one entry whose coefficient in the mask form of
x0 is not 0, set so that the join's clause holds.
Limits: seated and apart are shown for no y other than 0 here, and evaluated in no file of this
library. The tuple is found by choice: no program is given. Nothing is claimed on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MsgZero
import Johnson.Desc.First.Att.K05MasksAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)
open Johnson.Pack (sigOf pMain pMask portCode)
open Cb.Pv.Tail (JCell Syms cellValS cellVal cellsOf symL Packs packs_unique packs_cellsOf uniq_gl)
open VerifiableInference.Desc.First.Look (Sent attSg JAtt msgAtt sigListCalls seatCalls valAt readAt symAt szOf finOf_some
  jMain jMask)

section Onto
variable (cs : Codes) (l : List (OracleShape × Nat)) (seat : Addr → Option VerifiableInference.Desc.First.Look.Seat) (tl : HTailF2)

/-- The address of a symbol. -/
def symAddr (μ : Fin (szOf tl).NM) (i' : Fin (Alg.symRows ((szOf tl).m μ))) (c : Fin ((szOf tl).k μ)) : Addr :=
  .cell (tl.gtTree.getD μ.val 0) i'.val c.val

open Classical in
/-- What the tuple holds at (message o, main rows' table, row r, place c). -/
noncomputable def mainAt (y : Syms Cb.Gl.E (szOf tl)) (o r c : ℕ) : Cb.Gl.E :=
  if h : ∃ μ i' c', seat (symAddr tl μ i' c') = some ⟨o, false, r, c⟩ ∧ y μ i' c' ≠ 0 then
    y h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose
  else 0

/-- **The tuple of messages with prescribed symbols and a prescribed mask row.** -/
noncomputable def msgOf (y : Syms Cb.Gl.E (szOf tl)) (μr : ℕ → Cb.Gl.E) : (sigOf cs l).Msg := fun o =>
  (Sum.elim (fun p => mainAt seat tl y o.val p.1.val p.2.val) (fun p => μr p.2.val) :
    (Fin (l.get o).1.mainRows × Fin (pMain cs (l.get o).1).ell) ⊕
      (Fin (l.get o).1.maskRows × Fin (pMask cs (l.get o).1).ell) → Cb.Gl.E)

/-- **What is asked of the public data and of y.** -/
structure SymsSit (y : Syms Cb.Gl.E (szOf tl)) : Prop where
  main : ∀ μ i' c s, seat (symAddr tl μ i' c) = some s → s.mask = false
  seated : ∀ μ i' c, y μ i' c ≠ 0 → ∃ s, seat (symAddr tl μ i' c) = some s ∧ s.Fits cs l
  apart : ∀ μ i' c μ' i'' c' s, seat (symAddr tl μ i' c) = some s → seat (symAddr tl μ' i'' c') = some s →
    y μ i' c = y μ' i'' c'

variable {cs l seat tl}

/-- At the seat of a symbol address the tuple holds that symbol's value. -/
theorem mainAt_seat {y : Syms Cb.Gl.E (szOf tl)} (H : SymsSit cs l seat tl y) {μ : Fin (szOf tl).NM}
    {i' : Fin (Alg.symRows ((szOf tl).m μ))} {c : Fin ((szOf tl).k μ)} {o r p : ℕ}
    (hs : seat (symAddr tl μ i' c) = some ⟨o, false, r, p⟩) : mainAt seat tl y o r p = y μ i' c := by
  unfold mainAt
  split
  · rename_i h
    exact H.apart _ _ _ _ _ _ _ h.choose_spec.choose_spec.choose_spec.1 hs
  · rename_i h
    by_contra hne
    exact h ⟨μ, i', c, hs, fun e => hne e.symm⟩

/-- **The symbols read off the tuple are the prescribed ones.** -/
theorem symAt_msgOf {y : Syms Cb.Gl.E (szOf tl)} (H : SymsSit cs l seat tl y) (μr : ℕ → Cb.Gl.E) :
    symAt cs l seat tl (msgOf cs l seat tl y μr) = y := by
  funext μ i' c
  show (valAt cs l seat (msgOf cs l seat tl y μr) (symAddr tl μ i' c)).getD 0 = y μ i' c
  unfold valAt
  cases hs : seat (symAddr tl μ i' c) with
  | none =>
    by_contra hne
    obtain ⟨s, h1, _⟩ := H.seated μ i' c fun e => hne e.symm
    rw [hs] at h1
    cases h1
  | some s =>
    have hm := H.main _ _ _ _ hs
    obtain ⟨o, mk, r, p⟩ := s
    obtain rfl : mk = false := hm
    show (readAt cs l (msgOf cs l seat tl y μr) ⟨o, false, r, p⟩).getD 0 = y μ i' c
    by_cases hf : (⟨o, false, r, p⟩ : VerifiableInference.Desc.First.Look.Seat).Fits cs l
    · obtain ⟨hk, h2⟩ := hf
      rw [if_neg (by simp)] at h2
      unfold readAt
      rw [dif_pos hk, if_neg (by simp), finOf_some h2.1, finOf_some h2.2]
      exact mainAt_seat H hs
    · have hy : y μ i' c = 0 := by
        by_contra hne
        obtain ⟨s, h1, h2⟩ := H.seated μ i' c hne
        rw [hs] at h1
        exact hf (Option.some.inj h1 ▸ h2)
      rw [hy]
      unfold readAt
      split
      · rename_i hk
        rw [if_neg (by simp)]
        cases e1 : VerifiableInference.Desc.First.Look.finOf (l.get ⟨o, hk⟩).1.mainRows r with
        | none => rfl
        | some r' =>
          cases e2 : VerifiableInference.Desc.First.Look.finOf (pMain cs (l.get ⟨o, hk⟩).1).ell p with
          | none => rfl
          | some p' =>
            exfalso
            unfold VerifiableInference.Desc.First.Look.finOf at e1 e2
            split at e1
            · split at e2
              · rename_i a b
                exact hf ⟨hk, by rw [if_neg (by simp)]; exact ⟨a, b⟩⟩
              · cases e2
            · cases e1
      · rfl

end Onto

section Pack
variable {s : Cb.Pv.Tail.Size}

/-- The packing of integer matrices, as symbols. -/
def packOf (Z : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) : Syms Cb.Gl.E s := fun μ i' c =>
  ((Alg.pack (s.rad : ℤ) (Z μ c) i'.val : ℤ) : Cb.Gl.E)

/-- **The cells behind the packing of small integer matrices are their entries.** -/
theorem cellValS_pack (hu : s.Uniq Cb.Gl.p) (Z : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ)
    (hZ : ∀ μ c, Alg.Small (s.beta : ℤ) (Z μ c)) (j : JCell s) :
    cellValS (packOf Z) j = ((Z j.1 j.2.1 j.2.2 : ℤ) : Cb.Gl.E) := by
  have h0 : Packs (symL Cb.Gl.E s) (packOf Z) j.1 j.2.1 (Z j.1 j.2.1) := ⟨hZ _ _, fun _ => rfl⟩
  have e := packs_unique (symL Cb.Gl.E s) Cb.Gl.p hu (fun _ => rfl) h0 (packs_cellsOf _ ⟨_, h0⟩)
  show ((cellsOf (symL Cb.Gl.E s) (packOf Z) j.1 j.2.1 j.2.2 : ℤ) : Cb.Gl.E) = _
  rw [← e]

end Pack

section Cells
variable {cs : Codes} {l : List (OracleShape × Nat)} {seat : Addr → Option VerifiableInference.Desc.First.Look.Seat} {tl : HTailF2}

/-- **A tuple of messages with prescribed small cells.** -/
theorem cells_msgOf (Z : ∀ μ : Fin (szOf tl).NM, Fin ((szOf tl).k μ) → Fin ((szOf tl).m μ) → ℤ)
    (hZ : ∀ μ c, Alg.Small ((szOf tl).beta : ℤ) (Z μ c)) (H : SymsSit cs l seat tl (packOf Z)) (μr : ℕ → Cb.Gl.E)
    (ns : ℕ) (j : JCell (szOf tl)) :
    msgAtt cs l seat tl ns (msgOf cs l seat tl (packOf Z) μr) (some (.inr j)) = ((Z j.1 j.2.1 j.2.2 : ℤ) : Cb.Gl.E) := by
  show cellValS (symAt cs l seat tl (msgOf cs l seat tl (packOf Z) μr)) j = _
  rw [symAt_msgOf H]
  exact cellValS_pack (uniq_gl (s := szOf tl) rfl rfl) Z hZ j

end Cells

section AtCaller
variable {D : Sent} {x : VerifiableInference.Desc.First.Look.Place}

/-- The caller's seat of a cell lies in a main rows' table: by its text. -/
theorem seatCalls_main (i t r c : ℕ) (s : VerifiableInference.Desc.First.Look.Seat) (h : seatCalls D i (.cell t r c) = some s) : s.mask = false := by
  unfold seatCalls at h
  obtain ⟨bn, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨rp, _, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain ⟨k, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl

/-- **The mask row is free of the symbols.** -/
theorem maskOf_msgOf {hi : ℕ} (h : masksUpTo D x hi = true) (S : Attention.Shape) (tl : HTailF2) (rad : OracleShape → ℕ)
    (y : Syms Cb.Gl.E (szOf tl)) (μr : ℕ → Cb.Gl.E) {j : ℕ} (hj : j < hi) :
    (attLin0 x S tl D rad).maskOf
      (msgOf D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl y μr : (attSg x D rad).Msg) j = μr j := by
  obtain ⟨k, hk, h0, hc, _, e⟩ := maskOf_entry S tl rad h
    (msgOf D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl y μr : (attSg x D rad).Msg) hj
  rw [e]
  rfl

end AtCaller

end VerifiableInference.Desc.First.Att.P
