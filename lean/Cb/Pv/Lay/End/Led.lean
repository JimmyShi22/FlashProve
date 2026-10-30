-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/Led.lean: a list of forms of Blocks/Form.lean as a ledger of claims
(Cb/G6/Led.lean).

The files of this folder write the verifier's claims as forms of Blocks/Form.lean, in which the
library has the norms' identities. The link of a sub-proof takes the claims as a ledger of
Cb/G6/Led.lean: coefficients and a target. This file carries the one to the other.

Main definitions: toClaim, ledOf. Main theorems: toClaim_holds, ledOf_holds, ledOf_length.
normsLed: the claims on the norms as a ledger; norms_led_last: on entries with true tables, if that
ledger holds, then NormsLast.

Limits: as Cb/Pv/Lay/End/NormsCl.lean.


-/
import Cb.G6.Led
import Cb.Pv.Lay.End.NormsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell lDd)

variable {E J : Type} [Field E] [Fintype J]

/-- The claim "the form is worth 0". -/
def toClaim (f : Blocks.Form J E) : TWhole.Form E J := ⟨fun j => f (some j), -f none⟩

theorem toClaim_holds (f : Blocks.Form J E) (y : J → E) :
    (toClaim f).Holds y ↔ Blocks.Form.val y f = 0 := by
  unfold TWhole.Form.Holds TWhole.Form.gap toClaim
  rw [Blocks.Form.val_apply, sub_neg_eq_add, add_comm]

/-- The ledger of the claims "f is worth 0", f in l. -/
def ledOf (l : List (Blocks.Form J E)) : TWhole.Ledger E J := l.map toClaim

theorem ledOf_holds (l : List (Blocks.Form J E)) (y : J → E) :
    TWhole.Ledger.Holds (ledOf l) y ↔ ∀ f ∈ l, Blocks.Form.val y f = 0 := by
  unfold TWhole.Ledger.Holds ledOf
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun f _ => toClaim_holds f y

omit [Field E] [Fintype J] in
theorem ledOf_length [Field E] (l : List (Blocks.Form J E)) : (ledOf l).length = l.length :=
  List.length_map _

variable [DecidableEq J]

/-- The claims on the norms as a ledger. -/
def normsLed [Scl] (N : NormsNames J) (e : NormsE E) (u1 u2 : Blocks.Form J E) (D : Dim)
    (lNI b B : ℕ) : TWhole.Ledger E J :=
  ledOf (normsCl N e u1 u2 D lNI b B)

/-- On entries with true tables, if the ledger of the claims on the norms holds, then NormsLast. -/
theorem norms_led_last [Scl] (N : NormsNames J) (e : NormsE E) (u1 u2 : Blocks.Form J E)
    (D : Dim) (t : Cell → E) (lNI b s B : ℕ) (y : J → E) (hn : D.nNu = 2 ^ lNI) (hl : lDd D = b + s)
    (hd : D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b) (T : TablesTrue N e D t lNI b s B y)
    (h : TWhole.Ledger.Holds (normsLed N e u1 u2 D lNI b B) y) : NormsLast N e D t lNI b s y :=
  norms_last N e u1 u2 D t lNI b s B y hn hl hd hB T ((ledOf_holds _ y).1 h)

omit [Fintype J] in
/-- The number of the claims on the norms. -/
theorem normsLed_length [Scl] (N : NormsNames J) (e : NormsE E) (u1 u2 : Blocks.Form J E)
    (D : Dim) (lNI b B : ℕ) :
    (normsLed N e u1 u2 D lNI b B).length = 5 + 21 * D.nNu + D.ne := by
  unfold normsLed
  rw [ledOf_length]
  simp only [normsCl, clNorms, clLedger, clHot, List.length_append, List.length_cons,
    List.length_nil, List.length_map, List.length_range]
  omega

end Cb.Pv.Lay.End
