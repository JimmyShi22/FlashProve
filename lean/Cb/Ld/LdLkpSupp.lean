-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpSupp.lean: the output rows and the mask form of the assembled lookup read only the
multiplicities and the masks.
This file is about the support of linear claims: at which entries of the oracle messages the
coefficients of a lookup's output claims can differ from 0, and how such claims are re-indexed.

Definitions and statements (the statements in `Cb.Spec`). Proofs: Cb/Ld/LdLkpSuppProofs.lean.
The lookup as a sub-protocol ends in: a masked claim on the extension of the keys, and linear rows
with public targets. By type (`Lk.out`, Cb/Ld/LdLkp.lean) the rows and the mask form read `ent m'`
only (ent, m', N: arguments of `Lk.out`): the entries named by N (the multiplicities, masks, what
the lookup itself has sent). In the assembled lookup (Cb/Ld/LdLkpAsm.lean) rows and mask form are
vectors of coefficients on all entries J. Here it is stated, and proved in
Cb/Ld/LdLkpSuppProofs.lean, that every coefficient outside the places that the data A name is 0.

Main names:
  `A.PlacesIn G`: G holds of all places that the data A name: where the bits of the multiplicities
    stand (bAt) and where the own masks of all blocks stand (the other twelve fields). A named
    condition on G, with no content on A: the least such G is the set of the named places.
  `Spec.ldLkpSupp_rows`: under `A.PlacesIn G`, for every last explicit part o: all rows that the
    read-out (`A.rd`) lists are 0 outside G.
  `Spec.ldLkpSupp_form`: .. and so is the mask form of the masked claim on the keys.
  `Spec.ldLkpSupp_sum`: a form that is 0 outside the range of an injective naming ι : N → J has the
    same value on m as its pull-back on m ∘ ι.
  `Spec.ldLkpSupp_row_pull`, `Spec.ldLkpSupp_rows_pull`, `Spec.ldLkpSupp_cl_pull`: so a row, a list
    of rows, a masked claim, whose coefficients are 0 outside the range of the injective ι, pulled
    back along ι, hold of m ∘ ι if and only if the originals hold of m.
  `Spec.ldLkpSupp_out`: the corollary for callers: ι injective, with all named places in the range
    of ι, what the read-out states on J is what its pull-back states on N.

Limits: this file does not say that the named places are pairwise different, or differ from what the
keys read: these are conditions of the masked item (`LkAsm.PlacesOK`, Cb/Ld/LdLkpMaskPlaces.lean).
Targets and points are public by type.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

section
variable {E J N : Type}

/-- the coefficients are 0 outside G -/
def SuppIn [Zero E] (G : J → Prop) (c : J → E) : Prop := ∀ j, ¬ G j → c j = 0
def RowsSupp [Zero E] (G : J → Prop) (rs : List (Row E J)) : Prop := ∀ r ∈ rs, SuppIn G r.cf

/-- a row, a masked claim, in another naming of the entries -/
def Row.pull (ι : N → J) (r : Row E J) : Row E N := ⟨fun n => r.cf (ι n), r.tg⟩
def MCl.pull (ι : N → J) (c : MCl E J) : MCl E N := ⟨c.pt, fun n => c.mf (ι n), c.tg⟩

end

/-- G holds of all places that the data name. -/
structure LkAsm.PlacesIn {E : Type} [Field E] [Fintype E] (A : LkAsm E) (G : A.J → Prop) :
    Prop where
  bAt : ∀ u j, G (A.bAt u j)
  wS  : ∀ i, G (A.wS i)
  cS  : ∀ b, G (A.cS b)
  wAt : ∀ l i, G (A.wAt l i)
  cAt : ∀ l b, G (A.cAt l b)
  wK  : ∀ l i, G (A.wK l i)
  cK  : ∀ l b, G (A.cK l b)
  wT  : ∀ l i, G (A.wT l i)
  cT  : ∀ l b, G (A.cT l b)
  wE  : ∀ i, G (A.wE i)
  cE  : G A.cE
  wB  : ∀ i, G (A.wB i)
  cB  : G A.cB

end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- All rows of the read-out are 0 outside the named places. -/
def ldLkpSupp_rows : Prop :=
  ∀ (A : LkAsm E) (G : A.J → Prop), A.PlacesIn G → ∀ o, RowsSupp G (A.rd o).2.2
/-- So is the mask form of the masked claim on the keys. -/
def ldLkpSupp_form : Prop :=
  ∀ (A : LkAsm E) (G : A.J → Prop), A.PlacesIn G → ∀ o, SuppIn G (A.rd o).2.1.mf

/-- The corollary for callers. -/
def ldLkpSupp_out : Prop :=
  ∀ (A : LkAsm E) (N : Type) [Fintype N] (ι : N → A.J), Function.Injective ι →
    A.PlacesIn (fun j => j ∈ Set.range ι) →
    ∀ (o : A.Q.XB) (k : ℕ) (f : ℕ → E) (m : A.J → E),
      (((A.rd o).2.1.pull ι).Holds k f (fun n => m (ι n)) ↔ (A.rd o).2.1.Holds k f m) ∧
      (RowsHold ((A.rd o).2.2.map (Row.pull ι)) (fun n => m (ι n)) ↔ RowsHold (A.rd o).2.2 m)

end

section
variable (E : Type) [Field E]

def ldLkpSupp_sum : Prop :=
  ∀ (J N : Type) [Fintype J] [Fintype N] (ι : N → J), Function.Injective ι →
    ∀ c : J → E,
      SuppIn (fun j => j ∈ Set.range ι) c → ∀ m : J → E, ∑ n, c (ι n) * m (ι n) = ∑ j, c j * m j
def ldLkpSupp_row_pull : Prop :=
  ∀ (J N : Type) [Fintype J] [Fintype N] (ι : N → J), Function.Injective ι →
    ∀ r : Row E J, SuppIn (fun j => j ∈ Set.range ι) r.cf →
      ∀ m : J → E, (r.pull ι).Holds (fun n => m (ι n)) ↔ r.Holds m
def ldLkpSupp_rows_pull : Prop :=
  ∀ (J N : Type) [Fintype J] [Fintype N] (ι : N → J), Function.Injective ι →
    ∀ rs : List (Row E J), RowsSupp (fun j => j ∈ Set.range ι) rs →
      ∀ m : J → E, RowsHold (rs.map (Row.pull ι)) (fun n => m (ι n)) ↔ RowsHold rs m
def ldLkpSupp_cl_pull : Prop :=
  ∀ (J N : Type) [Fintype J] [Fintype N] (ι : N → J), Function.Injective ι →
    ∀ c : MCl E J, SuppIn (fun j => j ∈ Set.range ι) c.mf →
      ∀ (k : ℕ) (f : ℕ → E) (m : J → E), (c.pull ι).Holds k f (fun n => m (ι n)) ↔ c.Holds k f m

end
end Cb.Spec
