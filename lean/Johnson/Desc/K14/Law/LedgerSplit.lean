-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSplit.lean: "SPLIT" AT THE LEDGER OF A PROOF FILE's SHARED CHAIN: what a
kind's files owe at block 8 (ClauseAt, LedgerClause.lean), at a shape with two codes,
FOR CERTAIN (no draw counts), from foldSaysAt (Johnson/Desc/K14/Law/Carry.lean), UNDER NAMED
PREMISES: A JOINING, and the list of what is left.

  ins8, outs8     what the table's row 8 names at two codes: the row (fold) and o_sp's pin in front;
                  the rows (fold_u), (fold_omega) and that pin behind.
  open9_of_open8  a shared item that is open in front of the block, and is not the row (fold), is
                  open behind it.
  split_clause    **the clause at block 8**, at any piece and at any errors.
THE PREMISES, AND WHOSE EACH IS. hb: a yes of the piece's block is a yes of split at the chain's own
record (the wrap; by decidesBySplit_of_blocks) · hid: the table's extractor lays nothing at block 8
(the table's files) · hst: the promise in front gives OnSplit (GoodFoldAt.lean: two codes; the two
messages have their tables at all that grows out of the statement: onSplit_of_seated pays it from
five plain facts: the filling's shape 8) · hprom: the shared promise goes on at a yes · hAll: THE
FILLING's LEMMA: inside the promise behind, the shared items open behind give that ALL constraints
on G_u and on G_omega, as they lie in the record behind, hold of the words rg w · hFold: inside the
promise in front the letter row (fold) follows from FoldAt · hride: every other open shared item
rides back.
What is not claimed. NO MEMBER: no letters are shown at which the premises hold together. A
block that refuses all meets the clause. Nothing at a shape with one code. No soundness of a
verifier.

-/
import Johnson.Desc.K14.Law.GoodFoldAt
import Johnson.Desc.Sound.LedgerClause

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

/-- What the table's row 8 names in front, at two codes. -/
theorem ins8 (i : ItemS) : insSh true 8 i ↔ i = .row .fold ∨ i = .pin .oSp := by
  have hr : (rowAtS true 8).ins ++ (rowAtS true 8).ctx = [.row .fold, .pin .oSp] := rfl
  unfold insSh
  rw [hr]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro (rfl | rfl) <;> exact ⟨rfl, by simp⟩

/-- What it names behind. -/
theorem outs8 (i : ItemS) :
    outsSh true 8 i ↔ i = .row .foldU ∨ i = .row .foldOmega ∨ i = .pin .oSp := by
  have hr : (rowAtS true 8).outs ++ (rowAtS true 8).ctx =
      [.row .foldU, .row .foldOmega, .pin .oSp] := rfl
  unfold outsSh
  rw [hr]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · rintro (rfl | rfl | rfl) <;> exact ⟨rfl, by simp⟩

/-- A shared item that is open in front of the block, and is not the row (fold), is open behind. -/
theorem open9_of_open8 (i : ItemS) (h : openSh true 8 i) (hn : i ≠ .row .fold) :
    openSh true 9 i := by
  show (openSh true 8 i ∧ ¬ insSh true 8 i) ∨ outsSh true 8 i
  by_cases hI : insSh true 8 i
  · rcases (ins8 i).1 hI with rfl | rfl
    · exact absurd rfl hn
    · exact Or.inr ((outs8 _).2 (Or.inr (Or.inr rfl)))
  · exact Or.inl ⟨h, hI⟩

variable {P₁ Cl Wt : Type} {Fr : Frame} (N : NumbersS) (Mg : MeaningS St P₁ Wt)
  (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl Wt) (l : List (Piece (ckP .two) Fr (P₁ × St) Cl Wt))
  (e₀ : ∀ k, (actQ N p l k).1 → Wt → Wt)
  {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- **"SPLIT" at the ledger.** -/
theorem split_clause (pp : Par) (rg : Wt → Words K) (x : Piece (ckP .two) Fr (P₁ × St) Cl Wt)
    (ε : Err (uLT (ckP .two) x.ds))
    (hb : ∀ t rs gs t', x.b.decide t rs gs = .ok t' → split pp t.2 rs = some t'.2)
    (hid : ∀ v w, e₀ 8 v w = w)
    (hst : ∀ a, onQ₂ N Pm Oc true p l 8 a → OnSplit (F := Fr) pp (a.1.2, a.2))
    (hprom : ∀ a τ b, onQ₂ N Pm Oc true p l 8 a → x.ior.red.out a τ = some b →
      promQ N Pm true p l 9 ((actQ N p l 9).2 b))
    (hAll : ∀ (b : (P₁ × St) × Fr.E.Str) w, promQ N Pm true p l 9 ((actQ N p l 9).2 b) →
      (∀ i, openSh true 9 i → muQ N Mg p l i 9 ((actQ N p l 9).2 b) w) →
      Means.AllSay ρ b.1.2.st (rowsOn b.1.2 b.1.2.loc.gU) (rg w) ∧
        Means.AllSay ρ b.1.2.st (rowsOn b.1.2 b.1.2.loc.gOmega) (rg w))
    (hFold : ∀ a w, onQ₂ N Pm Oc true p l 8 a → FoldAt ρ pp.S a.1.2 (rg w) →
      Mg.row .fold a.1.2 w)
    (hride : ∀ a τ b w i, onQ₂ N Pm Oc true p l 8 a → x.ior.red.out a τ = some b →
      openSh true 8 i → i ≠ .row .fold → muQ N Mg p l i 9 ((actQ N p l 9).2 b) w →
      muQ N Mg p l i 8 ((actQ N p l 8).2 a) w) :
    ClauseAt N Mg Pm Oc true p l e₀ 8 x ε := by
  refine clause_of_sure N Mg Pm Oc true p l e₀ 8 x ε fun a τ b ha hout => ?_
  have hpr := hprom a τ b ha hout
  refine ⟨hpr, fun w hw i hi => ?_⟩
  rw [hid]
  by_cases hn : i = .row .fold
  · subst hn
    obtain ⟨_, gs, hd⟩ := piece_yes x a τ b hout
    obtain ⟨hS, hP⟩ := hst a ha
    have k8 := hb _ _ _ _ hd
    obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k8
    rw [hr] at k8
    obtain ⟨o8, l8⟩ := onward_split pp a.1.2 b.1.2 r8 hS k8
    obtain ⟨sU, sO⟩ := hAll b w hpr hw
    exact hFold a w ha (foldSaysAt ρ pp a.1.2 b.1.2 b.1.2 b.1.2 r8 (rg w) hS
      k8 (Reaches.refl _ _) (Reaches.refl _ _) (by rw [← l8]; exact sO) (by rw [← l8]; exact sU)
      (hP b.1.2.st o8.grows))
  · exact hride a τ b w i ha hout hi hn (hw i (open9_of_open8 i hi hn))

end Desc.K14.Law
