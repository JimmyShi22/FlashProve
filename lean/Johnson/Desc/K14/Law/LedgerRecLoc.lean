-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerRecLoc.lean: "(rec_gamma)" AND "LOC" AT THE LEDGER OF A PROOF FILE's
SHARED CHAIN: what a kind's files owe at blocks 3 and 4 (ClauseAt, LedgerClause.lean),
FROM rec_core and loc_core (Johnson/Desc/K14/Law/RowsCore.lean) and the library's reading of the
written round (Johnson/Desc/K14/Law/LocRead.lean), UNDER NAMED PREMISES: JOININGS, and the list of
what is left. The pattern is that of Johnson/Desc/K14/Law/LedgerZeta.lean.

  ins3, outs3, ins4, outs4   what the table's rows 3 and 4 name: in front recRow | nearU, behind the
                  rows (rec_gamma) | (loc_x); o_u's pin on both sides.
  rec_clause      **the clause at block 3**, at any piece, at any errors: for certain.
  loc_clause      **the clause at block 4**, at the piece that holds a block at one written round,
                  at the written count that bears e.
THE PREMISES, AND WHOSE EACH IS. hl: a yes of the piece's block is a yes of laysRec | loc at the
chain's own record (the wrap; by quiet_of_blocks | loc_of_blocks) · hd, ho: the written round draws
n positions and no element, and opens no tree (by make) · he: e is at least (2 ^ logN - e' - 1) ^ n
· hid: the table's extractor lays nothing at the block (the table's files) · hRec | hNear, hRows:
THE FILLING: the letter recRow | nearU follows, INSIDE THE PROMISE, from RecAll | NearAt; the letter
row (rec_gamma) | row (loc_x) gives the rows i₀, … on G_u as they lie in the record (this kind's
law's files) · hst, hi₀: the promise in front gives what On4 says and that G_u has just i₀ open rows
(the filling of shape 3 | 4) · hprom: the shared promise goes on at a yes · hback: o_u's pin rides
back · hdet: two witnesses with that pin at one value have the same words on o_u (the pins' files) ·
frames: the other open shared items ride back. What is not claimed. NO MEMBER: no letters are shown
at which the premises hold together. A block that refuses all meets the clause. No soundness
of a verifier.

-/
import Johnson.Desc.K14.Law.RowsCore
import Johnson.Desc.K14.Law.CellsTie
import Johnson.Desc.K14.Law.LedgerZeta

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open _root_.Run.PQ (CK)

/-- What the table's row 3 names in front. -/
theorem ins3 (split : Bool) (i : ItemS) : insSh split 3 i ↔ i = .recRow ∨ i = .pin .oU := by
  have hr : (rowAtS split 3).ins ++ (rowAtS split 3).ctx = [.recRow, .pin .oU] := by
    cases split <;> rfl
  unfold insSh
  rw [hr]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro (rfl | rfl) <;> exact ⟨rfl, by simp⟩

/-- What it names behind. -/
theorem outs3 (split : Bool) (i : ItemS) : outsSh split 3 i ↔ i = .row .recG ∨ i = .pin .oU := by
  have hr : (rowAtS split 3).outs ++ (rowAtS split 3).ctx = [.row .recG, .pin .oU] := by
    cases split <;> rfl
  unfold outsSh
  rw [hr]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro (rfl | rfl) <;> exact ⟨rfl, by simp⟩

/-- What the table's row 4 names in front. -/
theorem ins4 (split : Bool) (i : ItemS) : insSh split 4 i ↔ i = .nearU ∨ i = .pin .oU := by
  have hr : (rowAtS split 4).ins ++ (rowAtS split 4).ctx = [.nearU, .pin .oU] := by
    cases split <;> rfl
  unfold insSh
  rw [hr]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro (rfl | rfl) <;> exact ⟨rfl, by simp⟩

/-- What it names behind. -/
theorem outs4 (split : Bool) (i : ItemS) : outsSh split 4 i ↔ i = .row .loc ∨ i = .pin .oU := by
  have hr : (rowAtS split 4).outs ++ (rowAtS split 4).ctx = [.row .loc, .pin .oU] := by
    cases split <;> rfl
  unfold outsSh
  rw [hr]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro (rfl | rfl) <;> exact ⟨rfl, by simp⟩

variable {P₁ Cl Wt : Type} {Fr : Frame} (N : NumbersS) (Mg : MeaningS St P₁ Wt)
  (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl Wt) (l : List (Piece (ckP .two) Fr (P₁ × St) Cl Wt))
  (e₀ : ∀ k, (actQ N p l k).1 → Wt → Wt)

/-- **"(rec_gamma)" at the ledger.** -/
theorem rec_clause (P : Par) (rg : Wt → Words GE) (x : Piece (ckP .two) Fr (P₁ × St) Cl Wt)
    (ε : Err (uLT (ckP .two) x.ds))
    (hl : ∀ t rs gs t', x.b.decide t rs gs = .ok t' → laysRec P t.2 rs = some t'.2)
    (hid : ∀ v w, e₀ 3 v w = w)
    (hRec : ∀ a w, onQ₂ N Pm Oc split p l 3 a → RecAll OnBytes.Model.Reading.gl P a.1.2 (rg w) →
      Mg.recRow a.1.2 w)
    (i₀ : ℕ)
    (hRows : ∀ s w, Mg.row .recG s w →
      RowsUL OnBytes.Model.Reading.gl i₀ P.S.fold.index.answers s (rg w))
    (hst : ∀ a, onQ₂ N Pm Oc split p l 3 a → P.S.fold.index.ok = true ∧
      ∀ T', Grows a.1.2.st T' → PlacedU T' P.S.fold a.1.2.loc.oU)
    (hi₀ : ∀ a, onQ₂ N Pm Oc split p l 3 a → (rowsOn a.1.2 a.1.2.loc.gU).length = i₀)
    (hprom : ∀ a τ b, onQ₂ N Pm Oc split p l 3 a → x.ior.red.out a τ = some b →
      promQ N Pm split p l 4 ((actQ N p l 4).2 b))
    (hback : ∀ a τ b w, onQ₂ N Pm Oc split p l 3 a → x.ior.red.out a τ = some b →
      muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 b) w →
      muQ N Mg p l (.pin .oU) 3 ((actQ N p l 3).2 a) w)
    (frames : ∀ a τ b w i, onQ₂ N Pm Oc split p l 3 a → x.ior.red.out a τ = some b →
      promQ N Pm split p l 4 ((actQ N p l 4).2 b) → openSh split 3 i → ¬ insSh split 3 i →
      muQ N Mg p l i 4 ((actQ N p l 4).2 b) w → muQ N Mg p l i 3 ((actQ N p l 3).2 a) w) :
    ClauseAt N Mg Pm Oc split p l e₀ 3 x ε := by
  refine clause_of_own N Mg Pm Oc split p l e₀ 3 _ _ ?_ ?_
  · refine goodIn_conseq _ _ _ _ _ _ _
      (rec_core OnBytes.Model.Reading.gl rg (Prod.snd : P₁ × St → St)
        ({ x with ext := fun a _ w => e₀ 3 ((actQ N p l 3).2 a) w, err := ε } :
          Piece (ckP .two) Fr (P₁ × St) Cl Wt) P hl (fun a _ w => hid _ w)
        (onQ₂ N Pm Oc split p l 3) (fun b => promQ N Pm split p l 4 ((actQ N p l 4).2 b))
        (fun a w => muQ N Mg p l (.pin .oU) 3 ((actQ N p l 3).2 a) w)
        (fun b w => muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 b) w) hst i₀ hi₀ hprom hback) ?_ ?_
    · intro b w _ h
      exact ⟨h _ ((outs3 split _).2 (Or.inr rfl)), hRows _ w (h _ ((outs3 split _).2 (Or.inl rfl)))⟩
    · intro a w ha h i hi
      rcases (ins3 split i).1 hi with rfl | rfl
      · exact hRec a w ha h.2
      · exact h.1
  · intro a τ b w i ha hout hpr ho hi hm
    rw [hid]
    exact frames a τ b w i ha hout hpr ho hi hm

/-- **"LOC" at the ledger.** -/
theorem loc_clause (P : Par) (rg : Wt → Words GE) (b : Block (P₁ × St) Cl) (base : ℕ) (d : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wt → Wt)
    (er : Err (uLT (ckP .two) [d])) {ns n : ℕ}
    (hd : SendsDraws (toRD d) ns 0 n P.S.fold.index.code.logN) (ho : d.opens = []) (e' e : ℕ)
    (he : (2 ^ P.S.fold.index.code.logN - e' - 1) ^ n ≤ e)
    (hl : ∀ t rs gs t', b.decide t rs gs = .ok t' → loc P t.2 rs gs = some t'.2)
    (hid : ∀ v w, e₀ 4 v w = w)
    (hNear : ∀ a w, onQ₂ N Pm Oc split p l 4 a →
      NearAt OnBytes.Model.Reading.gl P a.1.2 (rg w)
        (colsOf (strsOfAct Fr ((actQ N p l 4).2 a)).cell) e' →
      Mg.nearU a.1.2 (strsOfAct Fr ((actQ N p l 4).2 a)) w)
    (i₀ : ℕ) (hRows : ∀ s w, Mg.row .loc s w → RowsUL OnBytes.Model.Reading.gl i₀ n s (rg w))
    (hst : ∀ a, onQ₂ N Pm Oc split p l 4 a → P.S.fold.index.ok = true ∧
      ∀ T', Grows a.1.2.st T' → PlacedU T' P.S.fold a.1.2.loc.oU)
    (hi₀ : ∀ a, onQ₂ N Pm Oc split p l 4 a → (rowsOn a.1.2 a.1.2.loc.gU).length = i₀)
    (hprom : ∀ a τ c, onQ₂ N Pm Oc split p l 4 a →
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out a τ = some c →
      promQ N Pm split p l 5 ((actQ N p l 5).2 c))
    (hback : ∀ a τ c w, onQ₂ N Pm Oc split p l 4 a →
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out a τ = some c →
      muQ N Mg p l (.pin .oU) 5 ((actQ N p l 5).2 c) w →
      muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 a) w)
    (hdet : ∀ a w w', onQ₂ N Pm Oc split p l 4 a →
      muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 a) w →
      muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 a) w' →
      AgreeOn a.1.2.loc.oU.oracle (rg w) (rg w'))
    (frames : ∀ a τ c w i, onQ₂ N Pm Oc split p l 4 a →
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out a τ = some c →
      promQ N Pm split p l 5 ((actQ N p l 5).2 c) → openSh split 4 i → ¬ insSh split 4 i →
      muQ N Mg p l i 5 ((actQ N p l 5).2 c) w → muQ N Mg p l i 4 ((actQ N p l 4).2 a) w) :
    ClauseAt N Mg Pm Oc split p l e₀ 4
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt)
      ((posMaps d P.S.fold.index.code.logN n).err ((e, ()) : ℕ × Unit)) := by
  refine clause_of_own N Mg Pm Oc split p l e₀ 4 _ _ ?_ ?_
  · refine goodIn_conseq _ _ _ _ _ _ _
      (loc_core OnBytes.Model.Reading.gl rg (Prod.snd : P₁ × St → St)
        (⟨b, base, [d], [], fun a _ w => e₀ 4 ((actQ N p l 4).2 a) w,
          (posMaps d P.S.fold.index.code.logN n).err ((e, ()) : ℕ × Unit)⟩ :
          Piece (ckP .two) Fr (P₁ × St) Cl Wt) P hl
        (fun a _ w => hid _ w) (onQ₂ N Pm Oc split p l 4)
        (fun c => promQ N Pm split p l 5 ((actQ N p l 5).2 c))
        (fun a w => muQ N Mg p l (.pin .oU) 4 ((actQ N p l 4).2 a) w)
        (fun c w => muQ N Mg p l (.pin .oU) 5 ((actQ N p l 5).2 c) w) hst i₀ hi₀ hprom hback hdet
        tabOf e' n e he
        (fun a τ _ cols _ hg => shown_stored
          (⟨b, base, [d], [], fun a _ w => e₀ 4 ((actQ N p l 4).2 a) w,
            (posMaps d P.S.fold.index.code.logN n).err ((e, ()) : ℕ × Unit)⟩ :
            Piece (ckP .two) Fr (P₁ × St) Cl Wt) d rfl ho a.2 τ _ cols hg)
        (fun _ => (posMaps d P.S.fold.index.code.logN n).carry)
        (fun _ => (posMaps d P.S.fold.index.code.logN n).fits (posMaps_ok hd) _) ?_) ?_ ?_
    · intro a τ c r4 hout hr
      have ht := piece_tests (⟨b, base, [d], [], fun a _ w => e₀ 4 ((actQ N p l 4).2 a) w,
        (posMaps d P.S.fold.index.code.logN n).err ((e, ()) : ℕ × Unit)⟩ :
        Piece (ckP .two) Fr (P₁ × St) Cl Wt) a τ c hout
      simp only [sTests, Bool.and_eq_true] at ht
      have hp : (posMaps d P.S.fold.index.code.logN n).pass τ = true :=
        (posMaps_pass d _ _ τ).trans ht.1.1
      obtain ⟨m, cc, ⟨⟩⟩ := τ
      have hr' : [noDigest (shownAt d m cc)] = [r4] := hr
      obtain rfl := (List.cons.inj hr').1
      exact ⟨gPos P.S.fold.index.code.logN n _ (valsOf (toRD d) cc),
        (posMaps d P.S.fold.index.code.logN n).tr_of_pass (m, cc, ()) hp, poss_shown hd m cc⟩
    · intro c w _ h
      exact ⟨h _ ((outs4 split _).2 (Or.inr rfl)), hRows _ w (h _ ((outs4 split _).2 (Or.inl rfl)))⟩
    · intro a w ha h i hi
      rcases (ins4 split i).1 hi with rfl | rfl
      · have h2 := h.2
        rw [tabOf_cells] at h2
        exact hNear a w ha h2
      · exact h.1
  · intro a τ c w i ha hout hpr ho' hi hm
    rw [hid]
    exact frames a τ c w i ha hout hpr ho' hi hm

end Desc.K14.Law
