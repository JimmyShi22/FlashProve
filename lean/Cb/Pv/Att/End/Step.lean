-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Step.lean: the claims that the verifier of an attention sub-proof keeps of one
sumcheck, as a ledger on early and late entries; their pull-back gives the block's output claims.

Definitions, statements and proofs. Of a sumcheck the verifier keeps one claim on the row of the
hiding polynomial's coefficients and one claim on each end value that it ties to the tables. The
first reads early entries alone. The others read the tables of the late message.

Main names:
  rdOf cellJ m: the cells' content, read off the early entries m at the places cellJ.
  rowF T o: the claim on the row, from the library's own row (formU in Cb/Sub/SeatPsc.lean).
  plainCl T o l r: the ledger: the row, then for each end value a of the list l the claim on a with
    the reading form r a.
  plainCl_length: it has 1 + the length of l claims.
  plainCl_out: if each reading form, with the late entries at their meant values, is worth its map
    at o's point, and the ledger's pull-back holds of m, then the block's claim on the row and its
    claims on the end values of l hold of m.
  plainCl_in: the other way round.
  pairs nb: the end values of a sumcheck of products, in the order A_0, B_0, A_1, B_1, ..;
    mem_pairs. pick rA rB: the reading forms of a sumcheck of products.
  stepCl_out: for a sumcheck of products all output claims hold. stepCl_iff: and the other way
    round.

Limits: the reading forms are letters here. That the ledger is the programs' is not said here.
Nothing on an honest prover or on hiding.


-/
import Cb.Pv.Att.End.Forms
import Cb.Pv.Att.Sc3
import Cb.Sub.SeatPsc
import Inst.Model.Att.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset
open Inst.Model

variable {E : Type} [Field E] [Fintype E]

/-- The cells' content, read off the early entries at the places cellJ. -/
def rdOf {J₁ : Type} (cellJ : AttSeg.Raw → J₁) (m : J₁ → E) : AttSeg.Raw → E := fun c => m (cellJ c)

section Plain
variable (T : PlainSc E) {J₂ : Type} [Fintype J₂]

/-- The claim on the row of the hiding polynomial's coefficients. -/
noncomputable def rowF (o : T.our.par.Out) : Form E (T.J ⊕ J₂) :=
  liftF (formU T.our.par (fun _ b _ _ => b.elim) o)

/-- Its pull-back is the block's first output claim. -/
theorem rowF_pull (al : J₂ → Aff E T.J) (o : T.our.par.Out) (m : T.J → E) :
    (pullF al (rowF T o)).Holds m ↔ T.our.par.UHolds o m := by
  unfold rowF
  rw [liftF_pull]
  exact formU_holds T.our.par _ (fun _ _ b _ => b.elim) o m

variable [DecidableEq T.J] [DecidableEq J₂]

/-- The verifier's claims of one sumcheck: the row, and the end values of the list l. -/
noncomputable def plainCl (o : T.our.par.Out) (l : List T.A) (r : T.A → Aff E (T.J ⊕ J₂)) :
    Ledger E (T.J ⊕ J₂) :=
  rowF T o :: l.map fun a => endF T o a (r a)

omit [Fintype J₂] in
theorem plainCl_length (o : T.our.par.Out) (l : List T.A) (r : T.A → Aff E (T.J ⊕ J₂)) :
    (plainCl T o l r).length = 1 + l.length := by
  unfold plainCl
  rw [List.length_cons, List.length_map, Nat.add_comm]

/-- The ledger's pull-back gives the block's claim on the row and its claims on the end values of
the list. -/
theorem plainCl_out (al : J₂ → Aff E T.J) (o : T.our.par.Out) (l : List T.A)
    (r : T.A → Aff E (T.J ⊕ J₂)) (m : T.J → E)
    (hr : ∀ a ∈ l, (r a).val (late al m) = T.map o.st m a (pointAt T o))
    (h : ∀ f ∈ plainCl T o l r, (pullF al f).Holds m) :
    T.our.par.UHolds o m ∧ ∀ a ∈ l, T.our.par.EHolds o m a :=
  ⟨(rowF_pull T al o m).mp (h _ List.mem_cons_self), fun a ha =>
    (endF_pull T al o a (r a) m (hr a ha)).mp
      (h _ (List.mem_cons_of_mem _ (List.mem_map_of_mem ha)))⟩

/-- And the other way round: so the ledger's pull-back says no more than these claims. -/
theorem plainCl_in (al : J₂ → Aff E T.J) (o : T.our.par.Out) (l : List T.A)
    (r : T.A → Aff E (T.J ⊕ J₂)) (m : T.J → E)
    (hr : ∀ a ∈ l, (r a).val (late al m) = T.map o.st m a (pointAt T o))
    (h : T.our.par.UHolds o m ∧ ∀ a ∈ l, T.our.par.EHolds o m a) :
    ∀ f ∈ plainCl T o l r, (pullF al f).Holds m := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact (rowF_pull T al o m).mpr h.1
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
    exact (endF_pull T al o a (r a) m (hr a ha)).mpr (h.2 a ha)

end Plain

/-! ### A sumcheck of products -/

/-- The end values of a sumcheck of products: A_0, B_0, A_1, B_1 and so on. -/
def pairs (nb : ℕ) : List (Fin nb × Bool) :=
  (List.finRange nb).flatMap fun b => [(b, false), (b, true)]

theorem mem_pairs {nb : ℕ} (a : Fin nb × Bool) : a ∈ pairs nb := by
  obtain ⟨b, x⟩ := a
  refine List.mem_flatMap.mpr ⟨b, List.mem_finRange b, ?_⟩
  cases x <;> simp

theorem pairs_length (nb : ℕ) : (pairs nb).length = 2 * nb := by
  unfold pairs
  rw [List.length_flatMap]
  simp
  ring

/-- The reading forms of a sumcheck of products, from those of the maps A_b and of the maps B_b. -/
def pick {nb : ℕ} {F : Type} (rA rB : ℕ → F) (a : Fin nb × Bool) : F :=
  if a.2 then rB a.1.val else rA a.1.val

section Sc
variable (T : Sc3 E) {J₂ : Type} [Fintype J₂] [DecidableEq T.plain.J] [DecidableEq J₂]

/-- For a sumcheck of products the ledger's pull-back gives all output claims of the block. -/
theorem stepCl_out (al : J₂ → Aff E T.plain.J) (o : T.plain.our.par.Out)
    (rA rB : ℕ → Aff E (T.plain.J ⊕ J₂)) (m : T.plain.J → E)
    (hA : ∀ b : Fin T.nb,
      (rA b.val).val (late al m) = T.plain.map o.st m (b, false) (pointAt T.plain o))
    (hB : ∀ b : Fin T.nb,
      (rB b.val).val (late al m) = T.plain.map o.st m (b, true) (pointAt T.plain o))
    (h : ∀ f ∈ plainCl T.plain o (pairs T.nb) (pick rA rB), (pullF al f).Holds m) :
    T.plain.our.par.OutHolds o m := by
  obtain ⟨h1, h2⟩ := plainCl_out T.plain al o (pairs T.nb) (pick rA rB) m
    (by
      rintro ⟨b, x⟩ _
      cases x with
      | false => exact hA b
      | true => exact hB b) h
  exact ⟨h1, fun a => h2 a (mem_pairs a)⟩

/-- The ledger's pull-back says what the block's output claims say. -/
theorem stepCl_iff (al : J₂ → Aff E T.plain.J) (o : T.plain.our.par.Out)
    (rA rB : ℕ → Aff E (T.plain.J ⊕ J₂)) (m : T.plain.J → E)
    (hA : ∀ b : Fin T.nb,
      (rA b.val).val (late al m) = T.plain.map o.st m (b, false) (pointAt T.plain o))
    (hB : ∀ b : Fin T.nb,
      (rB b.val).val (late al m) = T.plain.map o.st m (b, true) (pointAt T.plain o)) :
    (∀ f ∈ plainCl T.plain o (pairs T.nb) (pick rA rB), (pullF al f).Holds m) ↔
      T.plain.our.par.OutHolds o m :=
  ⟨stepCl_out T al o rA rB m hA hB, fun h =>
    plainCl_in T.plain al o (pairs T.nb) (pick rA rB) m
      (by
        rintro ⟨b, x⟩ _
        cases x with
        | false => exact hA b
        | true => exact hB b) ⟨h.1, fun a _ => h.2 a⟩⟩

end Sc

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.plainCl_out
#print axioms Cb.Pv.Att.End.stepCl_out
