-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Lists/TwShape.lean.
Tools: how a block's list of rounds and its list of errors go through the ways in which blocks are
  joined.

A block here is a reduction with its errors and no honest side (BkK, Cb/Pv/Lookup/Know/KnowAt.lean);
the sumcheck is a
letter SK (PscLtK, Cb/Pv/Lookup/Know/LtK.lean).
Main definitions. LtShape SK, LtErr SK: the letter's two laws: its rounds are round 0, one short
round for each variable, and (in the full form) the round of values; its errors are 1, the degree
for each variable, and 0. RI E b ds: the rounds of b's shape are the entries ds, one by
one. EL b es: b's errors are the numbers es.
Main statements. ri_seq, ri_preM, ri_postM, ri_chain, ri_draw1, ri_drawP and el_seq ..: the two
relations under seq, under maps without a round, under a chain, at a draw. ri_cubes, ri_mix,
ri_dummy, ri_full, el_full: one sumcheck.

-/
import OnBytes.Tie.Pv.Lookup.Port.TwRoundIs
import Cb.Pv.Lookup.Lists.TwErr
import Cb.Pv.Lookup.Know.AsmK
import Cb.G6.Letter

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn OnBytes.G4 Johnson.L5.Layers

section
variable {E : Type} [Field E] [Fintype E]


variable {Ex : ExtSpec}

structure LtShape (SK : PscLtK E Ex) : Prop where
  full : ∀ Y : PscPar E, (SK.full Y).R.shape = pRound0 E :: (sRounds Y.fmt ++ [pRoundV E Y.A])
  core : ∀ Y : PscPar E, (SK.core Y).R.shape = pRound0 E :: sRounds Y.fmt

structure LtErr (SK : PscLtK E Ex) : Prop where
  full : ∀ Y : PscPar E, TWhole.errList (SK.full Y).e = 1 :: (Y.fmt.map PFmt.n ++ [0])
  core : ∀ Y : PscPar E, TWhole.errList (SK.core Y).e = 1 :: Y.fmt.map PFmt.n

/-- the block's rounds are these entries; its errors are these numbers -/
def RI (E : Type) [Zero E] {Ex : ExtSpec} {X Y : Type} (b : BkK X Y Ex) (ds : List Fmt.Entry) : Prop
    :=
  List.Forall₂ (EntryIs E) b.R.shape ds
def EL {X Y : Type} (b : BkK X Y Ex) (es : List Nat) : Prop := TWhole.errList b.e = es

theorem f2_append {α β : Type _} {R : α → β → Prop} : ∀ {a a' : List α} {b b' : List β},
    List.Forall₂ R a b → List.Forall₂ R a' b' → List.Forall₂ R (a ++ a') (b ++ b')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (f2_append t h')

variable {X₁ X₂ X₃ : Type}

theorem ri_seq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} {d₁ d₂ : List Fmt.Entry} (h₁ : RI E a d₁)
    (h₂ : RI E b d₂) :
    RI E (a.seq b) (d₁ ++ d₂) := f2_append h₁ h₂
theorem ri_preM {b : BkK X₂ X₃ Ex} {d : List Fmt.Entry} (h : RI E b d) (φ : X₁ → X₂) : RI E
    (b.preM φ) d := h
theorem ri_postM {b : BkK X₁ X₂ Ex} {d : List Fmt.Entry} (h : RI E b d) (φ : X₂ → X₃) : RI E
    (b.postM φ) d := h

theorem el_seq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} {e₁ e₂ : List Nat} (h₁ : EL a e₁)
    (h₂ : EL b e₂) :
    EL (a.seq b) (e₁ ++ e₂) := (TWhole.errList_app a.e b.e).trans (by rw [h₁, h₂])
theorem el_preM {b : BkK X₂ X₃ Ex} {e : List Nat} (h : EL b e) (φ : X₁ → X₂) : EL (b.preM φ) e := h
theorem el_postM {b : BkK X₁ X₂ Ex} {e : List Nat} (h : EL b e) (φ : X₂ → X₃) : EL (b.postM φ) e :=
  h

theorem ri_chain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (d : ℕ → List Fmt.Entry)
    (h : ∀ l, RI E (b l) (d l)) : ∀ n, RI E (BkK.chain X b n) ((List.range (n + 1)).flatMap d)
  | 0 => by
    have h0 := h 0
    simpa [BkK.chain, List.range_succ] using h0
  | n + 1 => by
    have h1 := ri_seq (ri_chain X b d h n) (h (n + 1))
    rw [List.range_succ (n := n + 1), List.flatMap_append]
    simpa using h1

theorem el_chain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (e : ℕ → List Nat)
    (h : ∀ l, EL (b l) (e l)) : ∀ n, EL (BkK.chain X b n) ((List.range (n + 1)).flatMap e)
  | 0 => by
    have h0 := h 0
    simpa [BkK.chain, List.range_succ] using h0
  | n + 1 => by
    have h1 := el_seq (el_chain X b e h n) (h (n + 1))
    rw [List.range_succ (n := n + 1), List.flatMap_append]
    simpa using h1

/-- a draw of one element -/
theorem ri_draw1 {X X' : Type} (nx : X → E → X') (err wk : Nat) (name : String) :
    RI E (drawK E nx Ex err) [TwPlan.rd wk name 0 1] := .cons (entryIs_draw wk name) .nil
/-- a draw from a set that is a point's, up to an equivalence -/
theorem ri_drawP {X X' D : Type} [Fintype D] [Nonempty D] (nx : X → D → X') (err wk k : Nat)
    (name : String)
    (e : D ≃ (Fin k → E)) : RI E (drawK D nx Ex err) [TwPlan.rd wk name 0 k] :=
  .cons (entryIs_point D wk name k e) .nil
theorem el_draw {X X' D : Type} [Fintype D] [Nonempty D] (nx : X → D → X') (err : Nat) :
    EL (drawK D nx Ex err) [err] := rfl

/-! ### a sumcheck -/

theorem ri_cubes (wk g : Nat) : ∀ k, List.Forall₂ (EntryIs E)
    (sRounds (List.replicate k (pfCube E g)))
    ((List.replicate k g).map fun g => TwPlan.rd wk "PSC round" g 1)
  | 0 => .nil
  | k + 1 => .cons (entryIs_var _ wk g ⟨Equiv.refl _⟩ ⟨Equiv.refl _⟩ inferInstance)
      (ri_cubes wk g k)

theorem ri_mix (wk : Nat) : ∀ (k : ℕ) (dg : Fin k → ℕ),
    List.Forall₂ (EntryIs E) (sRounds (pfMix E k dg))
    ((List.ofFn dg).map fun g => TwPlan.rd wk "PSC round" g 1)
  | 0, _ => by simp [pfMix]
  | k + 1, dg => by
    rw [List.ofFn_succ]
    exact .cons (entryIs_var _ wk (dg 0) ⟨Equiv.refl _⟩ ⟨Equiv.refl _⟩ inferInstance)
        (ri_mix wk k fun i => dg i.succ)

theorem ri_dummy (wk D : Nat) : EntryIs E (sRound (pDummy E D)) (TwPlan.rd wk "PSC Y" D 1 1) :=
  entryIs_Y _ wk D ⟨Equiv.refl _⟩ ⟨Equiv.refl _⟩ inferInstance

/-- One sumcheck with end values, at a record PscOur whose variables are k cubes of degree g. -/
theorem ri_full {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) (T : PscOur E) (k g vals : ℕ)
    (hf : T.fmt = List.replicate k (pfCube E g)) (hA : Fintype.card T.A = vals) :
    RI E (SK.full T.par) (TwPlan.pscN wk (List.replicate k g) true T.DY vals) := by
  unfold RI
  rw [hS.full T.par]
  have hfm : T.par.fmt = List.replicate k (pfCube E g) ++ [pDummy E T.DY] := by
    show T.fmt ++ [pDummy E T.DY] = _
    rw [hf]
  rw [hfm]
  show List.Forall₂ (EntryIs E) ([pRound0 E] ++ (sRounds
      (List.replicate k (pfCube E g) ++ [pDummy E T.DY]) ++ [pRoundV E T.A])) _
  unfold TwPlan.pscN
  rw [if_pos rfl, List.append_assoc]
  refine f2_append (.cons (entryIs_r0 wk) .nil) ?_
  rw [sRounds, List.map_append, List.append_assoc]
  refine f2_append (ri_cubes wk g k) (.cons (ri_dummy wk T.DY) (.cons ?_ .nil))
  rw [← hA]
  exact entryIs_rV T.A

theorem el_full {SK : PscLtK E Ex} (hS : LtErr SK) (T : PscOur E) (k g : ℕ)
    (hf : T.fmt = List.replicate k (pfCube E g)) : EL (SK.full T.par) (TwErr.pscC k g T.DY) := by
  unfold EL
  rw [hS.full T.par]
  have hfm : T.par.fmt = List.replicate k (pfCube E g) ++ [pDummy E T.DY] := by
    show T.fmt ++ [pDummy E T.DY] = _
    rw [hf]
  rw [hfm]
  simp [TwErr.pscC, pDummy]

end
end TwRound
