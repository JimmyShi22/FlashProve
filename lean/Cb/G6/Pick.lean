-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Pick.lean: one pick of the left-out powers for every sumcheck: at every variable the constant
coefficient, with the inverse 1; and the letter of Cb/G6/Letter.lean as a total function of the
parameters.

Definitions, statements and proofs.

Main names:
  `fix0 l`: at every variable of the list the power 0 is left out, with the inverse 1. `fix0_ok`: it
    is lawful (`HFixs.OK`) wherever the "sum" of 1 is 1 at each variable.
  `mon0_eq`, `mon0_dummy`: that is so at a variable with equality weights (`pdEq`: any point, any
    degree) and at the dummy variable (`pDummyD`).
  `Eq0 Y`: every variable's weights sum to 1. `F₀ Y`: the pick for a block's parameters. `F₀_ok`.
  `eq0_cons`: one step, so that every written list of variables with equality weights, of whatever
    degrees, has it. `ldPart_eq0`: so has the library's `ldPartFmt`, `ldPartDat` at the equality
    form. `our_eq0`: for the instance `PscOur`: if its variables have it, so have those of its
    block.
  `V₀ Y Ex : ShortK Y Ex`, `V₀C Y Ex : ShortKC Y Ex`: the carried blocks at `F₀`. `H₀`, `H₀C`: their
    honest halves, under `Eq0 Y`.

Limits: at a Y with a variable whose weights do not sum to 1 the pick is not lawful: `H₀` is not to
be had, and at a state where it is not lawful it is not proved that `V₀ Y` accepts any transcript.
For such blocks take `shortK Y F` at a lawful F. (A variable whose functional is the sum of the
values at 0 and 1 is such a variable; that is not proved in this file.) Which power the programs
leave out is not said here.

-/
import Cb.G6.Value
import Cb.Ld.LdPscVarsProofs
import Cb.Part.LdPartVars

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb Johnson.L5.Layers

section Alg
variable {R : Type} [CommRing R]

/-- At every variable the power 0 is left out, with the inverse 1. -/
def fix0 : (l : List (HVar R)) → HFixs l
  | [] => ()
  | _ :: l => ((0, 1), fix0 l)

theorem fix0_ok : ∀ l : List (HVar R), (∀ v ∈ l, v.mon 0 = 1) → HFixs.OK l (fix0 l)
  | [], _ => trivial
  | v :: l, h =>
    ⟨by
      show (1 : R) * v.mon 0 = 1
      rw [one_mul, h v (List.mem_cons_self ..)],
     fix0_ok l fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

end Alg

variable {E : Type} [Field E] [Fintype E]

theorem mon0_eq (n : ℕ) (z : E) : ((pfCube E n).var (pdEq E n z)).mon 0 = 1 := by
  show ∑ b : Bool,
    (if b then z else 1 - z) * (if b then (1 : E) else 0) ^ (((0 : Fin (n + 1)) : ℕ)) = 1
  rw [Fintype.sum_bool]
  simp

theorem mon0_dummy (D : ℕ) : ((pDummy E D).var (pDummyD E D)).mon 0 = 1 := by
  show ∑ _s : Unit, (1 : E) * (0 : E) ^ (((0 : Fin (D + 1)) : ℕ)) = 1
  simp

/-- Every variable's weights sum to 1. -/
def Eq0 (Y : PscPar E) : Prop := ∀ st, ∀ v ∈ Y.vars st, v.mon 0 = 1

/-- The pick for a block's parameters. -/
def F₀ (Y : PscPar E) : ∀ st, HFixs (Y.vars st) := fun st => fix0 (Y.vars st)

omit [Fintype E] in
theorem F₀_ok (Y : PscPar E) (h : Eq0 Y) : ∀ st, HFixs.OK (Y.vars st) (F₀ Y st) :=
  fun st => fix0_ok _ (h st)

omit [Field E] [Fintype E] in
theorem mem_snoc : ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f) (v : HVar E),
    v ∈ pVars (l ++ [f]) (PDats.snoc l d f e) → v ∈ pVars l d ∨ v = f.var e
  | [], _, _, _, _, h => Or.inr (List.mem_singleton.1 h)
  | _ :: l, d, f, e, v, h => by
    rcases List.mem_cons.1 h with h | h
    · exact Or.inl (List.mem_cons.2 (Or.inl h))
    · rcases mem_snoc l d.2 f e v h with h | h
      · exact Or.inl (List.mem_cons.2 (Or.inr h))
      · exact Or.inr h

omit [Fintype E] in
/-- One step: so for any written list of variables, of whatever degrees. -/
theorem eq0_cons (f : PFmt E) (d : PDat E f) (l : List (PFmt E)) (ds : PDats l)
    (h : (f.var d).mon 0 = 1) (hl : ∀ v ∈ pVars l ds, v.mon 0 = 1) :
    ∀ v ∈ pVars (f :: l) (d, ds), v.mon 0 = 1 := fun v hv => by
  rcases List.mem_cons.1 hv with h1 | h1
  · rw [h1]; exact h
  · exact hl v h1

/-- The library's list of cube variables with a degree each (Cb/Part/LdPartVars.lean), all of the
equality form. -/
theorem ldPart_eq0 : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E),
    ∀ v ∈ pVars (ldPartFmt E k dg) (ldPartDat E k dg fun i => some (z i)), v.mon 0 = 1
  | 0, _, _ => fun _ hv => absurd hv (List.not_mem_nil)
  | k + 1, dg, z =>
    eq0_cons (pfCube E (dg 0)) (pdEq E (dg 0) (z 0)) _ _ (mon0_eq (dg 0) (z 0))
      (ldPart_eq0 k (fun i => dg i.succ) fun i => z i.succ)

/-- The instance with the dummy last variable. -/
theorem our_eq0 (T : PscOur E) (h : ∀ st, ∀ v ∈ T.vars st, v.mon 0 = 1) : Eq0 T.par :=
  fun st v hv => by
    rcases mem_snoc T.fmt (T.dat st) (pDummy E T.DY) (pDummyD E T.DY) v hv with h1 | h1
    · exact h st v h1
    · rw [h1]
      exact mon0_dummy T.DY

/-- The letter as a total function of the parameters: the carried block at `F₀`. -/
noncomputable def V₀ (Y : PscPar E) (Ex : ExtSpec) : ShortK Y Ex := shortK Y (F₀ Y) Ex
/-- The same without the round of values. -/
noncomputable def V₀C (Y : PscPar E) (Ex : ExtSpec) : ShortKC Y Ex := shortKC Y (F₀ Y) Ex
/-- Their honest halves, under `Eq0 Y`. -/
noncomputable def H₀ (Y : PscPar E) (Ex : ExtSpec) (h : Eq0 Y) : ShortH (V₀ Y Ex) :=
  shortH Y (F₀ Y) Ex (F₀_ok Y h)
noncomputable def H₀C (Y : PscPar E) (Ex : ExtSpec) (h : Eq0 Y) : ShortHC (V₀C Y Ex) :=
  shortHC Y (F₀ Y) Ex (F₀_ok Y h)

end TWhole
