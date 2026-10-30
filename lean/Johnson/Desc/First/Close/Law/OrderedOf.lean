-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/OrderedOf.lean: THE PREMISE `OrderedV` OF K10's LAW, PAID FOR THE
CLAIM's ROWS BY THE CHOICE OF THE TYPED ROWS; what is left is said row by row. Definitions, a
statement and its proof.

The typed rows of the claim (their states Sb and forms sl) are letters of the typed block: K10's law
may choose them. Here a typed row's state is a vector V on the whole cube (the program's row, as
`rowVec` lays it), its form is `pull V`, and its further weights are what V has on the free rows
beyond `pull V`, arranged.
  `CornerOnly V`: V is 0 at every kept slot off the corner 0 .. 0. `rowVec_corner`: `rowVec` is so.
  `Pulls R pull`: pull V, arranged, is V off the free rows, for every V with `CornerOnly`. A PREMISE
    on the group's arrangement: asked of its files; shown of no data here.
  `frOf pull frS`: the further weights: of a claim's row as above; of a sample row: frS, a letter.
  `orderedV_of`: `OrderedV` at Sb := vectors, sl := pull, fr := `frOf pull frS`, from: `Pulls`; a
    list ord of all the typed rows' names, each once, as long as the program's list; the powers
    (clause 4); and, number by number: where ord[i] is a row b of the claim: its typed target is the
    reading of the program's row number i's, and its state is `rowVec` of that row; where ord[i] is
    a member's sample row: THE TIE THAT IS LEFT: the answer is the reading of the program's row's
    target; the library's sample row at the seed, arranged, plus frS, is `rowVec` of that row; frS
    is 0 off the free rows.
Limits. `Pulls`, the list and the sample rows' tie are premises. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.BatTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Iop IOR KObj Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)

variable {S : Sig GE} (R : RowsK S)

/-- 0 at every kept slot off the corner 0 .. 0. -/
def CornerOnly (V : R.Sh.Cin.J → GE) : Prop :=
  ∀ b q x, b ≠ (fun _ => false) → V (.inl (b, (some q, x))) = 0

theorem rowVec_corner (N : SlotNames R) (T : Statement) (L : GroupLayout) (r : OnBytes.Row) :
    CornerOnly R (rowVec N T L r) := fun b q x hb => by
  show (if b = fun _ => false then _ else 0) = (0 : GE)
  rw [if_neg hb]

/-- pull V, arranged, is V off the free rows. -/
def Pulls (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) : Prop :=
  ∀ V, CornerOnly R V → ∀ j, ¬ FreeAt R.Sh j → R.Sh.rho.fm (pull V) j = V j

variable {B : Type} (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE)

open Classical in
/-- The further weights. -/
noncomputable def frOf
    (frS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), Slf GE (S.om as.1.1).Z.D R.Sh.Cin.J) :
    ∀ ν : R.G.Row B, Slf GE (R.G.RowSt (fun _ : B => R.Sh.Cin.J → GE) ν) R.Sh.Cin.J
  | .inl _ => fun V j => if FreeAt R.Sh j then V j - R.Sh.rho.fm (pull V) j else 0
  | .inr as => frS as

open Classical in
/-- **`OrderedV` from the choice of the claim's typed rows and the sample rows' tie.** -/
theorem orderedV_of (Z : Evader GE (R.G.Row B)) (N : SlotNames R) (hP : Pulls R pull)
    (frS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), Slf GE (S.om as.1.1).Z.D R.Sh.Cin.J)
    (hfrS : ∀ as s j, ¬ FreeAt R.Sh j → frS as s j = 0)
    (x : (B → GE) × (B → R.Sh.Cin.J → GE)) (σ : S.Smp) (z : Z.D) (e : E) (T : Statement)
    (L : GroupLayout) (rows : List OnBytes.Row) (ord : List (R.G.Row B)) (h1 : ord.Nodup)
    (h2 : ∀ ν, ν ∈ ord) (hl : ord.length = rows.length)
    (h4 : ∀ i (h : i < ord.length), Z.ze z ord[i] = readE e ^ i)
    (hB : ∀ i (h : i < ord.length) b, ord[i] = .inl b →
      x.1 b = readE (rows[i]'(hl ▸ h)).target ∧ x.2 b = rowVec N T L (rows[i]'(hl ▸ h)))
    (hS : ∀ i (h : i < ord.length) as, ord[i] = .inr as →
      (σ as.1.1).2 as.2 = readE (rows[i]'(hl ▸ h)).target ∧
      R.Sh.rho.fm (Slf.atMem (Jf := fun a : R.G.A => (S.om a.1).C.J) as.1
          ((S.om as.1.1).row as.2) (σ as.1.1).1) + frS as (σ as.1.1).1 =
        rowVec N T L (rows[i]'(hl ▸ h))) :
    OrderedV R (fun _ : B => R.Sh.Cin.J → GE) (fun _ V => pull V) Z N (frOf R pull frS) x σ z e T L
      rows := by
  refine ⟨ord, h1, h2, ?_, h4, ?_, ?_⟩
  · refine List.ext_getElem (by simp [hl]) fun i hi _ => ?_
    have hi' : i < ord.length := by simpa using hi
    simp only [List.getElem_map]
    cases hν : ord[i] with
    | inl b => exact (hB i hi' b hν).1
    | inr as => exact (hS i hi' as hν).1
  · refine List.ext_getElem (by simp [hl]) fun i hi _ => ?_
    have hi' : i < ord.length := by simpa using hi
    simp only [List.getElem_map]
    cases hν : ord[i] with
    | inl b =>
      have hv := (hB i hi' b hν).2
      funext j
      show R.Sh.rho.fm (pull (x.2 b)) j +
        (if FreeAt R.Sh j then x.2 b j - R.Sh.rho.fm (pull (x.2 b)) j else 0) = _
      by_cases hj : FreeAt R.Sh j
      · rw [if_pos hj, ← hv]
        ring
      · rw [if_neg hj, add_zero, hP (x.2 b) (hv ▸ rowVec_corner R N T L _) j hj, hv]
    | inr as => exact (hS i hi' as hν).2
  · intro ν s j hj
    cases ν with
    | inl b =>
      show (if FreeAt R.Sh j then _ else 0) = (0 : GE)
      rw [if_neg hj]
    | inr as => exact hfrS as s j hj

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.rowVec_corner
#print axioms VerifiableInference.Desc.First.Close.orderedV_of
