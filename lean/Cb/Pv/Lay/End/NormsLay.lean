-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsLay.lean: a type of late entries for the claims on the norms, with its lay.

Cb/Pv/Lay/End/NormsA.lean takes the late entries of a layers' sub-proof as a letter J₂ with a lay
(LateLay) in which the names that the claims on the norms read are good. This file gives a type that
has one entry for each of these names in range, and its lay. So the premises of tables_true on names
can be met together, at all sizes.

Main definitions: NormsJ2 n B ne nx (the entries), NormsJ2.nm, NormsJ2.at', normsLay. The names in
range are InRange of Cb/Pv/Lay/End/NormsA.lean.
Main theorem: tables_true_lay: tables_true at this lay, with no premise on names or forms. It is
used by no theorem.

Limits. The late message of a sub-proof holds more entries than these, and at places of its own: how
this type lies in it is not said here.


-/
import Cb.Pv.Lay.End.NormsA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Cell)

/-- The late entries that the claims on the norms read: n norms, B blocks, ne routed layers, nx
experts. -/
abbrev NormsJ2 (n B ne nx : ℕ) : Type :=
  (Fin n × Fin 5 × Fin B) ⊕ (Fin n × Fin 99) ⊕ (Fin n × Fin 99) ⊕ (Fin ne × Fin nx)

/-- The name of an entry. -/
def NormsJ2.nm {n B ne nx : ℕ} : NormsJ2 n B ne nx → NormsNm
  | .inl x => .xi x.1 x.2.1 x.2.2
  | .inr (.inl x) => .atP x.1 x.2
  | .inr (.inr (.inl x)) => .atR x.1 x.2
  | .inr (.inr (.inr x)) => .sel x.1 x.2

/-- The entry of a name. d: what stands for a name out of range. -/
def NormsJ2.at' {n B ne nx : ℕ} (d : NormsJ2 n B ne nx) : NormsNm → NormsJ2 n B ne nx
  | .xi ν l kh => if h : ν < n ∧ l < 5 ∧ kh < B then
      .inl (⟨ν, h.1⟩, ⟨l, h.2.1⟩, ⟨kh, h.2.2⟩) else d
  | .atP ν k => if h : ν < n ∧ k < 99 then .inr (.inl (⟨ν, h.1⟩, ⟨k, h.2⟩)) else d
  | .atR ν k => if h : ν < n ∧ k < 99 then .inr (.inr (.inl (⟨ν, h.1⟩, ⟨k, h.2⟩))) else d
  | .sel l x => if h : l < ne ∧ x < nx then .inr (.inr (.inr (⟨l, h.1⟩, ⟨x, h.2⟩))) else d

/-- The lay. -/
def normsLay {n B ne nx : ℕ} (d : NormsJ2 n B ne nx) : LateLay NormsNm (NormsJ2 n B ne nx) where
  nm := NormsJ2.nm
  at' := NormsJ2.at' d
  good := InRange n B ne nx
  ok := fun x hx => by
    cases x with
    | xi ν l kh =>
      show NormsJ2.nm (if h : ν < n ∧ l < 5 ∧ kh < B then _ else d) = _
      rw [dif_pos (show ν < n ∧ l < 5 ∧ kh < B from hx)]
      rfl
    | atP ν k =>
      show NormsJ2.nm (if h : ν < n ∧ k < 99 then _ else d) = _
      rw [dif_pos (show ν < n ∧ k < 99 from hx)]
      rfl
    | atR ν k =>
      show NormsJ2.nm (if h : ν < n ∧ k < 99 then _ else d) = _
      rw [dif_pos (show ν < n ∧ k < 99 from hx)]
      rfl
    | sel l x =>
      show NormsJ2.nm (if h : l < ne ∧ x < nx then _ else d) = _
      rw [dif_pos (show l < ne ∧ x < nx from hx)]
      rfl

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : NormPar0 E) [DecidableEq P.J]

/-- At this lay, with each late entry at the value of its form, the tables are true. -/
theorem tables_true_lay
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (e : NormsE E) (lNI b s B : ℕ) (d : NormsJ2 P.D.nNu B P.D.ne P.D.nx) (m : P.J → E) :
    TablesTrue (namesAt P (readsAt (normsLay d) id)) e P.D (P.rd m) lNI b s B
      (Sum.elim m fun j =>
        (lateA (normsLay d) (fun x => toAff (normsFm P.rd P.D e lNI b s x)) j).val m) :=
  tables_true P hrd (normsLay d) id _ e lNI b s B (fun _ _ => rfl)
    (fun _ _ _ h1 h2 h3 => ⟨h1, h2, h3⟩) (fun _ _ h1 h2 => ⟨h1, h2⟩) (fun _ _ h1 h2 => ⟨h1, h2⟩)
    (fun _ _ h1 h2 => ⟨h1, h2⟩) m

end Cb.Pv.Lay.End
