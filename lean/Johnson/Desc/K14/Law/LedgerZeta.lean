-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerZeta.lean: "LIN zeta" AT THE LEDGER OF A PROOF FILE's SHARED CHAIN: what
a kind's files owe at block 7 (ClauseAt, Johnson/Desc/Sound/LedgerClause.lean), FROM zeta_core
(Johnson/Desc/K14/Law/GoodFoldAt.lean) and the library's reading of the written round
(Johnson/Desc/K14/Law/ZetaRead.lean), UNDER NAMED PREMISES: A JOINING, and the list of what is left.

  goodIn_conseq   a law between two relations gives the law between a weaker one in front and a
                  stronger one behind, inside the promises.
  ins7, outs7     what the table's row 7 names: omU and the pins of o_u and o_omega in front; the
                  row (fold) and these two pins behind.
  Pins7 k v w     the two pins at border k, at a value of the acting part.
  zeta_clause     **the clause at block 7**, at the piece that holds a block at one written round,
                  at the written count that bears e.
THE PREMISES, AND WHOSE EACH IS. hz: a yes of the piece's block is a yes of linZeta at the chain's
own record (the wrap; by zeta_of_blocks) · hd: the written round draws kRow elements and no position
(by make: zeta_sendsDraws) · he: e is at least kRow |K| ^ (kRow - 1) · hid: the table's extractor
lays nothing at block 7 (the table's files) · hOm, hFold: THE FILLING: INSIDE THE PROMISE in front
the letter omU follows from OmegaCol, inside the promise behind the letter row (fold) gives FoldAt,
at the words rg w (K14's law's files; bare over all records they would be false at a filling that
reads the record through what the promise ties) ·
hprom: the shared promise goes on at a yes (shape 7 to shape 8: the filling; the stored table's
promise and "no collision": they read the strings below the piece's base) · hback: the two pins ride
back · hdet: two witnesses with both pins at one value have the same words on o_omega and o_u (the
pins' files) · frames: the other open shared items ride back.
What is not claimed. NO MEMBER: no letters are shown at which the premises hold together. A
block that refuses all meets the clause. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.ZetaRead
import Johnson.Desc.K14.Law.GoodFoldAt
import Johnson.Desc.Sound.LedgerClause

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block noDigest Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open _root_.Run.PQ (CK)

/-- A law between two relations gives the law between a weaker one in front and a stronger one
behind, inside the promises. -/
theorem goodIn_conseq {T Cl W : Type} {C : CK} {F : Frame} (pc : Piece C F T Cl W)
    (on on' : T × F.E.Str → Prop) (R R' Q Q' : T × F.E.Str → W → Prop)
    (h : pc.GoodIn on on' R R') (hQ' : ∀ b w, on' b → Q' b w → R' b w)
    (hQ : ∀ a w, on a → R a w → Q a w) : pc.GoodIn on on' Q Q' := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b hb =>
    ⟨(hτ b hb).1, fun w hw => hQ a _ ha ((hτ b hb).2 w (hQ' b w (hτ b hb).1 hw))⟩) (h a ha)

/-- What the table's row 7 names in front. -/
theorem ins7 (split : Bool) (i : ItemS) :
    insSh split 7 i ↔ i = .omU ∨ i = .pin .oU ∨ i = .pin .oOmega := by
  have hr : (rowAtS split 7).ins ++ (rowAtS split 7).ctx = [.omU, .pin .oU, .pin .oOmega] := by
    cases split <;> rfl
  unfold insSh
  rw [hr]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro (rfl | rfl | rfl) <;> exact ⟨rfl, by simp⟩

/-- What it names behind. -/
theorem outs7 (split : Bool) (i : ItemS) :
    outsSh split 7 i ↔ i = .row .fold ∨ i = .pin .oU ∨ i = .pin .oOmega := by
  have hr : (rowAtS split 7).outs ++ (rowAtS split 7).ctx =
      [.row .fold, .pin .oU, .pin .oOmega] := by
    cases split <;> rfl
  unfold outsSh
  rw [hr]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro (rfl | rfl | rfl) <;> exact ⟨rfl, by simp⟩

variable {P₁ Cl Wt : Type} {Fr : Frame} (N : NumbersS) (Mg : MeaningS St P₁ Wt)
  (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl Wt) (l : List (Piece (ckP .two) Fr (P₁ × St) Cl Wt))
  (e₀ : ∀ k, (actQ N p l k).1 → Wt → Wt)

/-- The pins of o_u and o_omega at border k, at a value of the acting part. -/
def Pins7 (k : ℕ) (v : (actQ N p l k).1) (w : Wt) : Prop :=
  muQ N Mg p l (.pin .oU) k v w ∧ muQ N Mg p l (.pin .oOmega) k v w

/-- **"LIN zeta" at the ledger.** -/
theorem zeta_clause (S : LinShape) (rg : Wt → Words GE) (b : Block (P₁ × St) Cl) (base : ℕ)
    (d : RDT) (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wt → Wt)
    (er : Err (uLT (ckP .two) [d])) {ns a0 : ℕ} (hd : SendsDraws (toRD d) ns S.kRow 0 a0) (e : ℕ)
    (he : S.kRow * Fintype.card GE ^ (S.kRow - 1) ≤ e)
    (hz : ∀ t rs gs t', b.decide t rs gs = .ok t' → linZeta t.2 rs = some t'.2)
    (hid : ∀ v w, e₀ 7 v w = w)
    (hOm : ∀ x w, onQ₂ N Pm Oc split p l 7 x →
      OmegaCol OnBytes.Model.Reading.gl S x.1.2 (rg w) → Mg.omU x.1.2 w)
    (hFold : ∀ (y : (P₁ × St) × Fr.E.Str) w, promQ N Pm split p l 8 ((actQ N p l 8).2 y) →
      Mg.row .fold y.1.2 w → FoldAt OnBytes.Model.Reading.gl S y.1.2 (rg w))
    (hprom : ∀ x τ y, onQ₂ N Pm Oc split p l 7 x →
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out x τ = some y →
      promQ N Pm split p l 8 ((actQ N p l 8).2 y))
    (hback : ∀ x τ y w, onQ₂ N Pm Oc split p l 7 x →
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out x τ = some y →
      Pins7 N Mg p l 8 ((actQ N p l 8).2 y) w → Pins7 N Mg p l 7 ((actQ N p l 7).2 x) w)
    (hdet : ∀ x w w', onQ₂ N Pm Oc split p l 7 x → Pins7 N Mg p l 7 ((actQ N p l 7).2 x) w →
      Pins7 N Mg p l 7 ((actQ N p l 7).2 x) w' →
      AgreeOn x.1.2.loc.oOmega (rg w) (rg w') ∧ AgreeOn x.1.2.loc.oU.oracle (rg w) (rg w'))
    (frames : ∀ x τ y w i, onQ₂ N Pm Oc split p l 7 x →
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt).ior.red.out x τ = some y →
      promQ N Pm split p l 8 ((actQ N p l 8).2 y) → openSh split 7 i → ¬ insSh split 7 i →
      muQ N Mg p l i 8 ((actQ N p l 8).2 y) w → muQ N Mg p l i 7 ((actQ N p l 7).2 x) w) :
    ClauseAt N Mg Pm Oc split p l e₀ 7
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt)
      ((vecMaps d S.kRow).err ((e, ()) : ℕ × Unit)) := by
  refine clause_of_own N Mg Pm Oc split p l e₀ 7 _ _ ?_ ?_
  · refine goodIn_conseq _ _ _ _ _ _ _
      (zeta_core OnBytes.Model.Reading.gl rg (Prod.snd : P₁ × St → St)
        (⟨b, base, [d], [], fun x _ w => e₀ 7 ((actQ N p l 7).2 x) w,
          (vecMaps d S.kRow).err ((e, ()) : ℕ × Unit)⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt) S hz
        (fun x _ w => hid _ w) (onQ₂ N Pm Oc split p l 7)
        (fun y => promQ N Pm split p l 8 ((actQ N p l 8).2 y))
        (fun x w => Pins7 N Mg p l 7 ((actQ N p l 7).2 x) w)
        (fun y w => Pins7 N Mg p l 8 ((actQ N p l 8).2 y) w) hprom hback hdet e he
        (fun _ => (vecMaps d S.kRow).carry)
        (fun _ => (vecMaps d S.kRow).fits (vecMaps_ok hd) _) ?_) ?_ ?_
    · intro x τ y r7 hout hr
      have ht := piece_tests (⟨b, base, [d], [], fun x _ w => e₀ 7 ((actQ N p l 7).2 x) w,
        (vecMaps d S.kRow).err ((e, ()) : ℕ × Unit)⟩ : Piece (ckP .two) Fr (P₁ × St) Cl Wt) x τ y
        hout
      simp only [sTests, Bool.and_eq_true] at ht
      have hp : (vecMaps d S.kRow).pass τ = true := (vecMaps_pass d _ τ).trans ht.1.1
      obtain ⟨m, c, ⟨⟩⟩ := τ
      have hr' : [noDigest (shownAt d m c)] = [r7] := hr
      obtain rfl := (List.cons.inj hr').1
      exact ⟨gVec S.kRow _ (valsOf (toRD d) c), (vecMaps d S.kRow).tr_of_pass (m, c, ()) hp,
        drawn_shown hd m c⟩
    · intro y w hy h
      exact ⟨⟨h _ ((outs7 split _).2 (Or.inr (Or.inl rfl))),
        h _ ((outs7 split _).2 (Or.inr (Or.inr rfl)))⟩,
        hFold y w hy (h _ ((outs7 split _).2 (Or.inl rfl)))⟩
    · intro x w hx h i hi
      rcases (ins7 split i).1 hi with rfl | rfl | rfl
      · exact hOm x w hx h.2
      · exact h.1.1
      · exact h.1.2
  · intro x τ y w i hx hout hpr ho hi hm
    rw [hid]
    exact frames x τ y w i hx hout hpr ho hi hm

end Desc.K14.Law
