-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToyDig.lean: a small example instance of one part of the
interactive proof for a request: the lookup argument on the digits of the range check.

Definitions, statement (`Cb.GlJ3.Spec.ldSegRef_toyDig`) and proof. A guard against empty theorems;
no parameter of a protocol. Data before it: Cb/GlVal/GlJ3SegRefToy.lean.
After "read, then the range check" the body has a lookup on the digits. `LdDgP`
(Cb/Req1/LdSegRefDig.lean) is the data of the shift and the lookup claim, `LdDgA`
(Cb/Req1/LdSegRefAsm.lean) the data of the assembled lookup on the digits. This file fills both
records (`Q R`, `X R`).

Main names:
  `sAt`, `rAt`, `dAt`: the places. Every datum is a member of its own, so a place is a name.
  `plL`, `idleAt`: the own masks of the lookup's sumchecks stand at the names `LN` of S (`LkNm2`,
    Cb/Ld/LdLkpStdPlaces2.lean); levels and steps that are never played name the idle entry.
  `Spec.ldSegRef_toyDig` states, for every `R`: the law of the digits' places (`(Q R).Places`);
    sizes of tables and keys; two different tags; ι is injective and its range holds all named
    places (`PlacesIn`); the conditions on numbers (`Adm pK`); the law of the bits' places
    (`(X R).Bits`); the four plain conditions on the places of the own masks (`PlacesOK`). For its
    remaining clauses (`LkAsm2.MaskOK`, Cb/Ld/LdLkpMaskAsm2.lean; three on the reading `tRd R`;
    `(X R).lk.AllB`, on which see Limits; for a nonempty `E₀.Str`, `(X R).link.GoodM ..`:
    `Chain.AllB`, `Link.GoodM`, Ior/KnowCollRulesChain.lean) see the statement.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `toyS`, Cb/GlVal/GlJ3Send.lean, `nu`, Cb/GlVal/GlToySend.lean, the data
of Cb/GlVal/GlJ3SegRefToy.lean (`RPar`, `D`, `p`, `eK`, `mkV`, the types of names), and `pK`,
`ne01`, Cb/GlVal/GlToyNum.lean): the fields are F, the integers modulo 2^64 - 2^32 + 1, and
E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight
points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: the law of the bits' places is asked for table entries Y < 4 and bit positions j < 4.
`bitAt` is total: beyond that range it names places of the range. Nothing is asked there by that law
(`(X R).Bits`). This file does not say that the lookup's masks are fresh when it begins. The sending
of S is not part of the body. This file says nothing on real parameters. The pads of the online
oracle messages lie in E: pads in the subfield F are not exercised. Of the digits' lookup the
statement has `(X R).lk.AllB`: all of the bundle but zero knowledge (`GoodB`, Ior/Masked.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegRefToy
import Cb.Req1.LdSegRefAsmZk

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace RefToy
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

noncomputable
section
variable {Kc : Type} {E₀ : ExtSpec} {Wp : Type} (R : RPar Kc E₀ Wp)

/-- all oracle messages that are open after the digits are sent -/
abbrev T : Sig E := ((D R).S.sum (D R).N).sum (D R).N'

/-- the datum's entry in a member -/
def d0 : toyS.C.J := nu.symm (Sum.inl ())

/-- The places: of a member of S (`sAt`), of the read (`rAt`), of a digit or a bit (`dAt`): the
datum's entry `d0` of that member. -/
def sAt (i : So R.Xn) : (T R).Ent := ⟨.inl (.inl i), d0⟩
def rAt (i : Unit × Unit) : (T R).Ent := ⟨.inl (.inr i), d0⟩
def dAt (i : No') : (T R).Ent := ⟨.inr i, d0⟩
/-- the own masks of the lookup; the idle entry -/
def plL (c : LN) : (T R).Ent := sAt R (.inr (.inr (.inl c)))
def idleAt : (T R).Ent := sAt R (.inr (.inr (.inr (.inr (.inr ())))))

/-- the entries that the lookup's rows and mask form may read: the bits, its own masks, the idle
entry -/
abbrev Nn : Type := Bt ⊕ (LN ⊕ Unit)

/-- The shift and the lookup claim: the data. -/
@[reducible] def Q : LdDgP E Kc E₀ Wp where
  D := D R
  lo := fun r u => dAt R (.inl (false, (r, u)))
  hi := fun r u => dAt R (.inl (true, (r, u)))
  K := 2
  e := eK
  v := 1
  d := 1
  tag := fun f => if f = 0 then 0 else 1
  Nn := Nn

def iota : Nn → (T R).Ent := Sum.elim (fun x => dAt R (.inr x)) (Sum.elim (plL R) fun _ => idleAt R)

/-- where a bit stands -/
def bitAt (Y j : ℕ) : (T R).Ent :=
  dAt R (.inr (decide (Y / 2 ≠ 0),
        (decide (Y % 2 = 1), ⟨min j 3, Nat.lt_succ_of_le (Nat.min_le_right j 3)⟩)))

/-- The assembled lookup on the digits: the data. -/
@[reducible] def X : LdDgA E Kc E₀ Wp where
  Q := Q R
  ι := iota R
  w := 2
  n := 2
  bAt := bitAt R
  wS := LkNm2.wS (plL R)
  cS := LkNm2.cS (plL R)
  wAt := LkNm2.wAt (plL R) (idleAt R)
  cAt := LkNm2.cAt (plL R) (idleAt R)
  wK := LkNm2.wK (plL R) (idleAt R)
  cK := LkNm2.cK (plL R) (idleAt R)
  wT := LkNm2.wT (plL R) (idleAt R)
  cT := LkNm2.cT (plL R) (idleAt R)
  wE := LkNm2.wE (plL R)
  wB := LkNm2.wB (plL R)
  cB := LkNm2.cB (plL R)

/-- What the reading keeps: digits, bits, the lookup's own masks. -/
def tRd (j : (T R).Ent) : Prop := (∃ i, j = dAt R i) ∨ ∃ c, j = plL R c

end

variable {Kc : Type} {E₀ : ExtSpec} {Wp : Type} (R : RPar Kc E₀ Wp)

theorem sAt_inj : Function.Injective (sAt R) := fun _ _ h =>
  Sum.inl_injective (Sum.inl_injective (congrArg Sigma.fst h))
theorem dAt_inj : Function.Injective (dAt R) := fun _ _ h =>
  Sum.inr_injective (congrArg Sigma.fst h)
theorem plL_inj : Function.Injective (plL R) := fun _ _ h =>
  Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (sAt_inj R h)))
theorem s_ne_d (i : So R.Xn) (k : No') : sAt R i ≠ dAt R k := fun h =>
  Sum.inl_ne_inr (congrArg Sigma.fst h)
theorem pl_ne_idle (c : LN) : plL R c ≠ idleAt R := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective (Sum.inr_injective (sAt_inj R h)))

theorem places : (Q R).Places := fun _ => rfl

theorem iota_inj : Function.Injective (iota R) := by
  rintro (a | a | a) (b | b | b) h
  · exact congrArg Sum.inl (Sum.inr_injective (dAt_inj R h))
  · exact absurd h.symm (s_ne_d R _ _)
  · exact absurd h.symm (s_ne_d R _ _)
  · exact absurd h (s_ne_d R _ _)
  · exact congrArg (fun c => Sum.inr (Sum.inl c)) (plL_inj R h)
  · exact absurd h (pl_ne_idle R a)
  · exact absurd h (s_ne_d R _ _)
  · exact absurd h.symm (pl_ne_idle R b)
  · rfl

theorem named : (X R).A.PlacesIn (fun j => j ∈ Set.range (iota R)) := by
  have hp : ∀ c, plL R c ∈ Set.range (iota R) := fun c => ⟨.inr (.inl c), rfl⟩
  have hi : idleAt R ∈ Set.range (iota R) := ⟨.inr (.inr ()), rfl⟩
  exact
  { bAt := fun _ _ => ⟨.inl _, rfl⟩
    wS := fun _ => hp _
    cS := fun _ => hp _
    wAt := LkNm2.in_wAt (plL R) (idleAt R) _ hp hi
    cAt := LkNm2.in_cAt (plL R) (idleAt R) _ hp hi
    wK := LkNm2.in_wK (plL R) (idleAt R) _ hp hi
    cK := LkNm2.in_cK (plL R) (idleAt R) _ hp hi
    wT := LkNm2.in_wT (plL R) (idleAt R) _ hp hi
    cT := LkNm2.in_cT (plL R) (idleAt R) _ hp hi
    wE := fun _ => hp _
    wB := fun _ => hp _
    cB := hp _ }

theorem adm : (X R).A.H.lkb.Adm pK :=
  ⟨show 3 ≤ 2 ^ 2 by decide, show 2 ^ 2 < 2 ^ 3 by decide, show 2 ^ 2 * (2 ^ 3 - 1) < pK by decide⟩

theorem stdAt : (X R).A.StdAt (plL R) where
  s := LkNm2.at_s (plL R)
  t := LkNm2.at_t (plL R) (idleAt R)
  k := LkNm2.at_k (plL R) (idleAt R)
  f := LkNm2.at_f (plL R) (idleAt R)
  e := LkNm2.at_e (plL R)
  b := LkNm2.at_b (plL R)

theorem dt_d (j : (T R).Ent) (h : (X R).Dt j) : ∃ i, j = dAt R i := by
  rcases h with ⟨r, u, rfl⟩ | ⟨r, u, rfl⟩ | ⟨Y, i, rfl⟩
  exacts [⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩]

theorem placesOK : (X R).A.PlacesOK (X R).Dt :=
  ldLkpStd2_places E (X R).A (plL R) (X R).Dt (stdAt R) (plL_inj R) (fun c h => by
      obtain ⟨i, e⟩ := dt_d R _ h
      exact s_ne_d R _ _ e) (fun Y i => Or.inr (Or.inr ⟨Y, i, rfl⟩)) fun st m m' h => by
    have ek : (X R).keyF m = (X R).keyF m' := by
      funext f
      unfold LdDgA.keyF
      by_cases hf : f = 0
      · rw [if_pos hf, if_pos hf]
        congr 1
        funext r u
        exact h _ (Or.inl ⟨r, u, rfl⟩)
      · rw [if_neg hf, if_neg hf]
        congr 1
        funext r u
        exact h _ (Or.inr (Or.inl ⟨r, u, rfl⟩))
    show shKey (X R).Q.v ((X R).keyF m) (X R).Q.tag st.2 =
      shKey (X R).Q.v ((X R).keyF m') (X R).Q.tag st.2
    rw [ek]

theorem rd_keeps (j : (T R).Ent) (h : (X R).A.srAll (X R).Dt j) : tRd R j :=
  h.elim (fun a => Or.inl (dt_d R j a)) fun a =>
    Or.inr ((ldLkpStd2_sw E (X R).A (plL R) (stdAt R) j).1 a)

theorem rd_idle : ¬ tRd R (idleAt R) := fun h =>
  h.elim (fun ⟨_, e⟩ => s_ne_d R _ _ e) fun ⟨c, e⟩ => pl_ne_idle R c e.symm

/-- no pad is kept: every entry that is kept is the datum of its member -/
theorem rd_datum (j : (T R).Ent) (h : tRd R j) : (∃ i, j = sAt R i) ∨ ∃ i, j = dAt R i :=
  h.elim Or.inr fun ⟨_, e⟩ => Or.inl ⟨_, e⟩

theorem hbit_min (key t : ℕ → E) (u j : ℕ) : hbit 1 3 key t u (min j 3) = hbit 1 3 key t u j := by
  by_cases h : j ≤ 3
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]
    unfold hbit
    rw [if_neg fun c => absurd c.1 (lt_irrefl 3), if_neg fun c => h (Nat.le_of_lt c.1)]

/-- The law of the bits' places. -/
theorem bits : (X R).Bits := by
  intro m hv Y _ j _
  have h1 : (T R).ents m (bitAt R Y j) =
      (Q R).vv m
        (decide (Y / 2 ≠ 0),
          (decide (Y % 2 = 1), ⟨min j 3, Nat.lt_succ_of_le (Nat.min_le_right j 3)⟩)) := rfl
  have hv' : (Q R).vv m = mkV ((Q R).dg m) := hv
  have ek : (X R).keyF ((T R).ents m) (Y / 2 ^ 1) =
      rngKeys p eK (if decide (Y / 2 ≠ 0) = true then ((Q R).dg m).2 else ((Q R).dg m).1) := by
    unfold LdDgA.keyF
    by_cases hf : Y / 2 = 0
    · rw [if_pos (show Y / 2 ^ 1 = 0 from hf), if_neg (by simp [hf])]
      rfl
    · rw [if_neg (show ¬ Y / 2 ^ 1 = 0 from hf), if_pos (by simp [hf])]
      rfl
  have et : (X R).tabF (Y / 2 ^ 1) = tabMod 2 := by
    unfold LdDgA.tabF
    split <;> rfl
  have eu : (decide (Y % 2 = 1)).toNat = Y % 2 ^ 1 := by
    rcases Nat.mod_two_eq_zero_or_one Y with h | h <;> simp [h]
  show (T R).ents m (bitAt R Y j) =
    hbit 1 3 ((X R).keyF ((T R).ents m) (Y / 2 ^ 1)) ((X R).tabF (Y / 2 ^ 1)) (Y % 2 ^ 1) j
  rw [h1, hv', ek, et, ← eu, ← hbit_min]
  rfl

end RefToy

namespace Spec
open Iop Prob Hiop IOR RefToy Cb.LdLkp

def ldSegRef_toyDig : Prop :=
  ∀ (Kc : Type) (E₀ : ExtSpec) (Wp : Type) (R : RPar Kc E₀ Wp),
    (Q R).Places ∧ p.q ≤ 2 ^ (Q R).d ∧ p.H ≤ 2 ^ (Q R).d ∧
    (Q R).K ≤ 2 ^ (Q R).v ∧
    (Q R).tag 0 ≠ (Q R).tag 1 ∧
    Function.Injective (X R).ι ∧
    (X R).A.PlacesIn (fun j => j ∈ Set.range (X R).ι) ∧
    (X R).A.H.lkb.Adm pK ∧
    (X R).Bits ∧
    (X R).A.PlacesOK (X R).Dt ∧
    (X R).A.MaskOK (X R).Dt ∧
    ((∀ j, (X R).A.srAll (X R).Dt j → tRd R j) ∧
      ¬ tRd R (idleAt R) ∧
      ∀ j, tRd R j → (∃ i, j = sAt R i) ∨ ∃ i, j = dAt R i) ∧
    (X R).lk.AllB ∧
    ∀ [Nonempty E₀.Str], (X R).link.GoodM ((X R).dm (tRd R))

end Spec

open RefToy in
theorem ldSegRef_toyDig : Spec.ldSegRef_toyDig := fun Kc E₀ Wp R =>
  ⟨places R,
    show 2 ≤ 2 ^ 1 by decide,
    show 2 ≤ 2 ^ 1 by decide,
    show 2 ≤ 2 ^ 1 by decide,
    ne01, iota_inj R, named R, adm R, bits R, placesOK R,
    ldLkpPlaces2_ok E _ _ (placesOK R),
    ⟨rd_keeps R, rd_idle R, rd_datum R⟩,
    ldSegRef_asm_allB E Kc E₀ Wp pK (X R) (iota_inj R) (named R) (adm R),
    ldSegRef_asm_goodM E Kc E₀ Wp pK (X R) (tRd R) (iota_inj R) (named R) (adm R)
      (ldLkpPlaces2_ok E _ _ (placesOK R)) (rd_keeps R)⟩

end Cb.GlJ3
