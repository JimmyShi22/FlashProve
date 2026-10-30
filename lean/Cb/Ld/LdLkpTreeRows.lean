-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTreeRows.lean: what rides along through the product tree, as a list of linear rows with
public targets.

Definitions, statements (in `Cb.Spec`) and proofs.
In a product tree (`TreeP`, Cb/Ld/LdLkpTreeP.lean) the levels are functions of a state and of the
entries m : D.J → E of the oracle messages; level l has a sumcheck for the product of the two halves
of level l + 1. A joint (`Rels`, Ior/Chain.lean) is what a chain says of the statements between two
blocks. A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and
of witness: the honest relation; a second relation, called relaxed, of which round-by-round
knowledge soundness speaks; the set of statements of which that soundness speaks; and a map from a
witness to its core. The joint at level l (`TreeP.jtAt`) is the sum claim of the level's sumcheck,
and what rides along.
In Cb/Ld/LdLkpTreeP.lean the states of the levels are nested, and what rides along at level l
(`TreeP.ride`) contains, beside the joint A0 with which the tree was entered, the row on the hiding
polynomial's coefficients of every level below l. Here these rows are read off the nested state, as
rows in the sense of Cb/Ld/LdLkpTree.lean (`Row`: coefficients on the entries, public target), so
that whoever ends a chain can list them.

Main names:
  `Spec.ldLkpP_push`: the value of a pushed form: `pushJ f c` at the entries m is c at the entries
    j' ↦ m (f j').
  `Spec.ldLkpP_rowU`: the row `TreeP.rowU` holds if and only if the sumcheck's own claim on the
    hiding polynomial's coefficients (`PscPar.UHolds`) holds.
  `Spec.ldLkpP_ride`: the main statement: `TreeP.ride` written out as A0 at `TreeP.root` and the
    rows of `TreeP.rowsAt`, field by field of the joint; see its docstring.

Limits: this file says nothing on which entries a row reads (by the sumcheck's form: the places
`wAt` of its level, and the places that the incoming form `slS` reads). It says nothing on soundness
or zero knowledge.
-/
import Cb.Ld.LdLkpTree
import Cb.Ld.LdLkpTreePProofs
import Cb.Ld.LdPscProofsIor

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section
variable {E : Type} [Field E] [Fintype E]

open Classical in
/-- The push-forward of a linear form c on entries named by J' along a map f : J' → J of names. -/
def pushJ {J' J : Type} [Fintype J'] (f : J' → J) (c : J' → E) : J → E := fun j =>
  ∑ j', if f j' = j then c j' else 0

namespace TreeP
variable (D : TreeP E)

/-- No map of a level stays unrevealed (`PscPar.B`, Cb/Ld/LdPsc.lean). -/
theorem emB (l : ℕ) : IsEmpty (D.lv l).T.par.B := by
  cases l with
  | zero => exact inferInstanceAs (IsEmpty Empty)
  | succ l => exact inferInstanceAs (IsEmpty Empty)

/-- The row of level l, read off the output `o` of its sumcheck. (`slU` takes a row for each map in
`B`; by `emB` there is none.) -/
def rowU (l : ℕ) (o : (D.lv l).T.par.Out) : Row E D.J :=
  ⟨pushJ (D.lv l).toJ ((D.lv l).T.par.slU (fun _ b _ _ => ((D.emB l).false b).elim) o),
    (D.lv l).T.par.tU o⟩

/-- The state with which the tree was entered, read off the state of level l. -/
def root : (l : ℕ) → (D.lv l).T.St → (D.lv 0).T.St
  | 0, s => s
  | l + 1, s => root l s.1.st

/-- The rows of all levels below l, the newest first. -/
def rowsAt : (l : ℕ) → (D.lv l).T.St → List (Row E D.J)
  | 0, _ => []
  | l + 1, s => D.rowU l s.1 :: rowsAt l s.1.st

end TreeP
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpP_push : Prop :=
  ∀ (J' J : Type) [Fintype J'] [Fintype J] (f : J' → J) (c : J' → E) (m : J → E),
    ∑ j, pushJ f c j * m j = ∑ j', c j' * m (f j')

def ldLkpP_rowU : Prop :=
  ∀ (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E),
    (D.rowU l o).Holds m ↔ (D.lv l).T.par.UHolds o fun j => m ((D.lv l).toJ j)

/-- What rides along, as a list of rows. States: in the exact relation (`rel`) and in the relaxed
one (`relR`), `D.ride msg A0 l` holds if and only if `A0` holds at the state with which the tree was
entered (`D.root l st`) and all rows of `D.rowsAt l st` hold of the entries `msg w.1`. Its condition
(`on`) is that of `A0` at `D.root l st`; its core is that of `A0`. -/
def ldLkpP_ride : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) (l : ℕ),
    (∀ st y w,
      (D.ride msg A0 l).rel st y w ↔
      A0.rel (D.root l st) y w ∧ RowsHold (D.rowsAt l st) (msg w.1)) ∧
    (∀ st y w,
      (D.ride msg A0 l).relR (st, y) w ↔
      A0.relR (D.root l st, y) w ∧ RowsHold (D.rowsAt l st) (msg w.1)) ∧
    (∀ st y, (D.ride msg A0 l).on (st, y) ↔ A0.on (D.root l st, y)) ∧
    (D.ride msg A0 l).core = A0.core

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

omit [Fintype E] in
theorem ldLkpP_push : Spec.ldLkpP_push E := by
  classical
  intro J' J _ _ f c m
  unfold pushJ
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem ldLkpP_rowU : Spec.ldLkpP_rowU E := by
  intro D l o m
  rw [psc_row_U E (D.lv l).T.par (fun _ b _ _ => ((D.emB l).false b).elim)
      (fun _ _ b _ => ((D.emB l).false b).elim) o]
  unfold Row.Holds Slf.Holds TreeP.rowU
  rw [ldLkpP_push]
  exact Iff.rfl

theorem ldLkpP_ride : Spec.ldLkpP_ride E := by
  intro D Ex M Wp Kc msg A0 l
  induction l with
  | zero =>
    exact ⟨fun st y w => ⟨fun h => ⟨h, fun r hr => absurd hr (List.not_mem_nil)⟩, fun h => h.1⟩,
      fun st y w => ⟨fun h => ⟨h, fun r hr => absurd hr (List.not_mem_nil)⟩, fun h => h.1⟩,
      fun _ _ => Iff.rfl, rfl⟩
  | succ l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have hcons : ∀ (s : (D.lv (l + 1)).T.St) (μ : D.J → E) (P : Prop),
        ((P ∧ RowsHold (D.rowsAt l s.1.st) μ) ∧
          (D.lv l).T.par.UHolds s.1 (fun j => μ ((D.lv l).toJ j))) ↔
        (P ∧ RowsHold (D.rowsAt (l + 1) s) μ) := fun s μ P => by
      rw [← ldLkpP_rowU E D l s.1 μ]
      constructor
      · rintro ⟨⟨hP, hr⟩, hu⟩
        refine ⟨hP, fun r hr' => ?_⟩
        rcases List.mem_cons.mp hr' with rfl | h
        · exact hu
        · exact hr r h
      · rintro ⟨hP, hr⟩
        exact ⟨⟨hP, fun r h => hr r (List.mem_cons_of_mem _ h)⟩, hr _ (List.mem_cons_self)⟩
    refine ⟨fun st y w => ?_, fun st y w => ?_, fun st y => h3 st.1.st y, h4⟩
    · refine Iff.trans ?_ (hcons st (msg w.1) (A0.rel (D.root l st.1.st) y w))
      exact and_congr_left fun _ => h1 st.1.st y w
    · refine Iff.trans ?_ (hcons st (msg w.1) (A0.relR (D.root l st.1.st, y) w))
      exact and_congr_left fun _ => h2 st.1.st y w

end
end Cb
