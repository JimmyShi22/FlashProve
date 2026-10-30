-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Sub/SeatPsc.lean: a kind of block seated on the joint for a sub-proof: the short hiding sumcheck,
at any parameters and any filling, as a block that appends its output claims to the ledger. A
pattern for other blocks.

Definitions, statements and their proofs.
The block: `TWhole.ShortK Y Ex` (Cb/G6/Letter.lean), any filling: a sumcheck with the parameters Y
(`PscPar`, Cb/Ld/LdPsc.lean), from the sum claim (`Y.baseIn`) to its output claims (`Y.baseOut`):
one row on the hiding polynomial's coefficients (`UHolds`), and for each shown map "the map's value
at the point is the value shown" (`EHolds`). The library gives these claims as linear rows with
public targets where the maps are linear in the entries (`psc_row_U`, `psc_row_E`,
Cb/Ld/LdPscProofsIor.lean). The seating is `led_knowAt` (Cb/Sub/Joint.lean), twice:
  (i) all maps are linear: every output claim goes into the ledger; beside it the rider A0 alone is
    left (`led_close`, `led_batch` of Cb/Sub/Joint.lean apply only where A0 says nothing);
  (ii) the shown maps are anything: the first row alone goes into the ledger; the claims on the
    shown values STAY OPEN, for later blocks.

Main names:
  `formU Y rowB o`, `formE Y rowA a o`: the rows as `TWhole.Form`.
  `formU_holds`, `formE_holds`: they hold iff `UHolds`, `EHolds` do.
  `clAll Y rowA rowB o`, `clU Y rowB o`: the claims appended in (i), in (ii).
  `restJ Y A0 msg`, `openJ Y A0 msg`: what is left beside the ledger: the rider A0 alone; the rider
    and the open claims on the shown values.
  `psc_led_all`, `psc_led_open`: the two seatings: `KnowAt` of `K.R.led ..` between `ledJ`s, with
    the block's own errors; the ledger grows by 1 + the number of shown maps, or by 1.

  `psc_led_all_short`, `psc_led_open_short`: the two at the block `TWhole.V₀ Y Ex`
    (Cb/G6/Pick.lean): every round leaves out the constant coefficient.

Limits: nothing on an honest prover or on zero knowledge. K is ANY filling of `ShortK`, whose field
`know` IS the soundness: a filling whose verifier rejects everything has it too. The three
conditions on Y (`VarsOK`, `DegOK`, `ValInj`) and the linearity of the maps are premises. No
parameters Y are given.
Terms: lean/GLOSSARY.md.
-/
import Cb.Sub.Joint
import Cb.G6.Pick
import Cb.Ld.LdPscProofsIor

set_option autoImplicit false

namespace Cb.Sub
open Iop Prob Hiop TWhole IOR

variable {E : Type} [Field E] (Y : PscPar E)

/-- The first row as a form. -/
noncomputable def formU (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) :
    Form E Y.J := ⟨Y.slU rowB o, Y.tU o⟩

/-- The row on the value of the shown map a as a form. -/
def formE (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E) (a : Y.A) (o : Y.Out) :
    Form E Y.J := ⟨Y.slE rowA a o, o.vals a⟩

theorem formU_holds (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (hB : Y.LinB rowB)
    (o : Y.Out) (m : Y.J → E) : (formU Y rowB o).Holds m ↔ Y.UHolds o m :=
  sub_eq_zero.trans (psc_row_U E Y rowB hB o m).symm

theorem formE_holds (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E) (hA : Y.LinA rowA)
    (o : Y.Out) (m : Y.J → E) (a : Y.A) : (formE Y rowA a o).Holds m ↔ Y.EHolds o m a :=
  sub_eq_zero.trans (psc_row_E E Y rowA hA o m a).symm

/-- All output claims. -/
noncomputable def clAll (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E)
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) : Ledger E Y.J :=
  formU Y rowB o :: (Finset.univ : Finset Y.A).toList.map fun a => formE Y rowA a o

/-- The first row alone. -/
noncomputable def clU (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) :
    Ledger E Y.J := [formU Y rowB o]

theorem clAll_holds (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E)
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (hA : Y.LinA rowA) (hB : Y.LinB rowB)
    (o : Y.Out) (m : Y.J → E) : Ledger.Holds (clAll Y rowA rowB o) m ↔ Y.OutHolds o m := by
  unfold Ledger.Holds clAll PscPar.OutHolds
  simp only [List.mem_cons, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_eq_or_imp, forall_exists_index, forall_apply_eq_imp_iff]
  exact and_congr (formU_holds Y rowB hB o m) (forall_congr' fun a => formE_holds Y rowA hA o m a)

theorem clAll_length (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E)
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) :
    (clAll Y rowA rowB o).length = 1 + Fintype.card Y.A := by
  unfold clAll
  rw [List.length_cons, List.length_map, Finset.length_toList, Finset.card_univ, Nat.add_comm]

section Joints
variable {Kc M Wp : Type} {Ex : ExtSpec}

/-- What is left beside the ledger in (i): the rider alone. -/
def restJ (A0 : Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) : Rels Kc Y.Out Ex (M × Wp) :=
  Y.baseRels A0 (fun w => msg w.1) PscPar.Out.st fun _ _ => True

/-- What is left beside the ledger in (ii): the rider, and the open claims on the shown values. -/
def openJ (A0 : Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) : Rels Kc Y.Out Ex (M × Wp) :=
  Y.baseRels A0 (fun w => msg w.1) PscPar.Out.st fun o m => ∀ a, Y.EHolds o m a

end Joints

variable [Fintype E]

/-- (i) All maps linear: every output claim goes into the ledger. -/
theorem psc_led_all {Kc M Wp : Type} {Ex : ExtSpec} (K : ShortK Y Ex) (hV : Y.VarsOK)
    (hD : Y.DegOK) (hI : Y.ValInj) (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E)
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (hA : Y.LinA rowA) (hB : Y.LinB rowB)
    (A0 : Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (n : ℕ) :
    KnowAt (K.R.led (clAll Y rowA rowB)) (ledJ (Y.baseIn A0 fun w => msg w.1) msg n)
      (ledJ (restJ Y A0 msg) msg (n + (1 + Fintype.card Y.A))) idW K.ε :=
  led_knowAt msg (clAll Y rowA rowB) n (1 + Fintype.card Y.A) (K.know hV hD hI M Wp Kc A0 msg)
    (fun o => le_of_eq (clAll_length Y rowA rowB o)) (fun _ h => h)
    fun o _ w _ h0 hc => ⟨h0.1, (clAll_holds Y rowA rowB hA hB o (msg w.1)).1 hc⟩

/-- (ii) The first row goes into the ledger; the claims on the shown values stay open. -/
theorem psc_led_open {Kc M Wp : Type} {Ex : ExtSpec} (K : ShortK Y Ex) (hV : Y.VarsOK)
    (hD : Y.DegOK) (hI : Y.ValInj) (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E)
    (hB : Y.LinB rowB) (A0 : Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (n : ℕ) :
    KnowAt (K.R.led (clU Y rowB)) (ledJ (Y.baseIn A0 fun w => msg w.1) msg n)
      (ledJ (openJ Y A0 msg) msg (n + 1)) idW K.ε :=
  led_knowAt msg (clU Y rowB) n 1 (K.know hV hD hI M Wp Kc A0 msg) (fun _ => le_refl 1)
    (fun _ h => h)
    fun o _ w _ h0 hc =>
      ⟨h0.1, (formU_holds Y rowB hB o (msg w.1)).1 (hc _ (List.mem_singleton.2 rfl)), h0.2⟩

/-- (i) at the block `TWhole.V₀ Y Ex`. -/
theorem psc_led_all_short {Kc M Wp : Type} {Ex : ExtSpec} (hV : Y.VarsOK) (hD : Y.DegOK)
    (hI : Y.ValInj) (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E)
    (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (hA : Y.LinA rowA) (hB : Y.LinB rowB)
    (A0 : Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (n : ℕ) :
    KnowAt ((V₀ Y Ex).R.led (clAll Y rowA rowB)) (ledJ (Y.baseIn A0 fun w => msg w.1) msg n)
      (ledJ (restJ Y A0 msg) msg (n + (1 + Fintype.card Y.A))) idW (V₀ Y Ex).ε :=
  psc_led_all Y (V₀ Y Ex) hV hD hI rowA rowB hA hB A0 msg n

/-- (ii) at the block `TWhole.V₀ Y Ex`. -/
theorem psc_led_open_short {Kc M Wp : Type} {Ex : ExtSpec} (hV : Y.VarsOK) (hD : Y.DegOK)
    (hI : Y.ValInj) (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (hB : Y.LinB rowB)
    (A0 : Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) (n : ℕ) :
    KnowAt ((V₀ Y Ex).R.led (clU Y rowB)) (ledJ (Y.baseIn A0 fun w => msg w.1) msg n)
      (ledJ (openJ Y A0 msg) msg (n + 1)) idW (V₀ Y Ex).ε :=
  psc_led_open Y (V₀ Y Ex) hV hD hI rowB hB A0 msg n

end Cb.Sub
