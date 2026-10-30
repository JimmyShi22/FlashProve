-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/AtStdPlaces.lean: at the standard places the course over the
field, read, IS the plain function that the described lookup's verifier puts out; no premise on
places is left. The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean); that the program's run, read in the field, is this
course is not shown in this file.

Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean shows that equation under the premise that each of
the eight stretches keeps the reading `Sim` (`Sims`). Here the record of places is the value
`Pl.std` (Cb/Pv/KeyLookup/PlStd.lean) at the two numberings «the n-th mask entry that either ledger
gives out behind those taken before the lookup».

  `plAt A sl D own idx` that value: `Pl.std A (fun n => sl (D.ms (own + n))) fun n => sl (D.ix (idx
    + n))`.
  `StdC A D st p` the conditions that are left: the course has the description's public record; that
    record is admissible (`Pub.Adm p`: public numbers and shapes); the course's public factor and
    table are the description's.
  `tie_std`, `parts_std`, `lev_std` the tie's and the parts' places are the course's; the levels'
    record of places is the one of Johnson/Desc/First/Look/KeyLaw/Mid/LevSimG.lean.
  `sims_std` `StdC` ⇒ `Sims` at `A.runD (plAt A sl D own idx)`.
  `course_std` under `StdC`, on every flat list whose first rounds fit: `A.lamRun (plAt …)` on these
    rounds = (the state; for each part the course's claim on its leaves, read as a claim on the
    keys; the course's rows, read), and the course leaves the rounds behind them.
Not claimed: anything on the program's blocks: the course is over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean); that the entries which the ledgers give out
differ.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.AllStretches
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimG
import Johnson.Desc.First.Look.KeyLaw.Mid.CloseStd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev Cb Cb.LdLkp

variable (A : Dat GE) (sl : Slot → A.J) (D : Dt) (own idx : ℕ)

/-- The standard places, at the entries that the ledgers give out behind own and idx. -/
def plAt : Pl A := Pl.std A (fun n => sl (D.ms (own + n))) fun n => sl (D.ix (idx + n))

/-- The conditions that are left. -/
structure StdC (st : A.St) (p : ℕ) : Prop where
  pub : D.S = A.toPub
  adm : A.toPub.Adm p
  fac : ∀ al, D.fac al = A.fac st al
  tab : ∀ q : Fin A.d → GE,
    D.tabAt (List.ofFn q) = Alg.mle (fun r : Fin A.d → Bool => A.tab st (numLE r)) q

theorem tieBase_succ (l : ℕ) : tieBase (l + 1) = 7 + 6 * l := by
  simp [tieBase]

theorem tie_std : TieSim.Places A sl (plAt A sl D own idx).tie D own where
  w00 := rfl
  w01 := rfl
  w02 := rfl
  w03 := rfl
  cZ := rfl
  c0f := rfl
  c0t := rfl
  w0 := fun l => by
    show sl (D.ms (own + tieBase (l + 1))) = _
    rw [tieBase_succ]
    rfl
  w1 := fun l => by
    show sl (D.ms (own + (tieBase (l + 1) + 1 + 0))) = _
    rw [tieBase_succ]
    rfl
  w2 := fun l => by
    show sl (D.ms (own + (tieBase (l + 1) + 1 + 1))) = _
    rw [tieBase_succ]
    rfl
  w3 := fun l => by
    show sl (D.ms (own + (tieBase (l + 1) + 1 + 2))) = _
    rw [tieBase_succ]
    rfl
  cf := fun l => by
    show sl (D.ms (own + (tieBase (l + 1) + 4))) = _
    rw [tieBase_succ]
    rfl
  ct := fun l => by
    show sl (D.ms (own + (tieBase (l + 1) + 5))) = _
    rw [tieBase_succ]
    rfl

theorem parts_std :
    PlacesAt A sl D (plAt A sl D own idx).wP (plAt A sl D own idx).cP (own + ownAt A.toPub 1) := by
  intro l _
  have e : A.toPub.bParts = ownAt A.toPub 1 := Clo.bParts_own _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show sl (D.ms (own + (A.toPub.bParts + 5 * l))) = _
    rw [e, Nat.add_assoc]
  · show sl (D.ms (own + (A.toPub.bParts + 5 * l + 1 + 0))) = _
    rw [e]
    exact congrArg (fun k => sl (D.ms k)) (by omega)
  · show sl (D.ms (own + (A.toPub.bParts + 5 * l + 1 + 1))) = _
    rw [e]
    exact congrArg (fun k => sl (D.ms k)) (by omega)
  · show sl (D.ms (own + (A.toPub.bParts + 5 * l + 3))) = _
    rw [e]
    exact congrArg (fun k => sl (D.ms k)) (by omega)
  · show sl (D.ms (own + (A.toPub.bParts + 5 * l + 4))) = _
    rw [e]
    exact congrArg (fun k => sl (D.ms k)) (by omega)

/-- The levels' record of places, in the numbering from 0. -/
theorem lev_std : (plAt A sl D own idx).lev =
    LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) (own + ownAt A.toPub 3)
      (idx + idxAt A.toPub 3) (own + ownAt A.toPub 4) := by
  have e3 : A.toPub.bKeys = ownAt A.toPub 3 := (Clo.bKeys_own _).trans (Clo.ownAt_3 _).symm
  have e4 : A.toPub.bTable = ownAt A.toPub 4 := Clo.bTable_own _
  have e0 : idxAt A.toPub 3 = 0 := rfl
  show LevPl.std A (fun n => sl (D.ms (own + n))) (fun n => sl (D.ix (idx + n))) A.toPub.bKeys 0
    A.toPub.bTable = _
  rw [e3, e4, e0]
  unfold LevPl.std
  congr 1
  · funext i l n
    exact congrArg (fun k => sl (D.ms k)) (by omega)
  · funext i l b
    split
    · exact congrArg (fun k => sl (D.ix k)) (by omega)
    · exact congrArg (fun k => sl (D.ms k)) (by omega)
  · funext l n
    exact congrArg (fun k => sl (D.ms k)) (by omega)
  · funext l b
    exact congrArg (fun k => sl (D.ms k)) (by omega)

variable {A sl D}

/-- Each of the eight stretches keeps the reading, at the standard places. -/
theorem sims_std {st : A.St} {p : ℕ} (h : StdC A D st p) :
    Sims A (A.runD (plAt A sl D own idx)) D (Sim A sl st own idx) st own idx where
  head := TieSim.head_field (plAt A sl D own idx) st idx (by rw [h.pub]) h.adm.planes h.fac
    (tie_std A sl D own idx)
  parts := parts_goes A sl D _ _ st own idx h.pub (parts_std A sl D own idx)
  join := Clo.join_goes A sl st own idx D h.pub
  keys := by
    show Goes _ _ _ (A.keysRun (plAt A sl D own idx).lev) (A.keysFm (plAt A sl D own idx).lev)
    rw [lev_std]
    exact keys_std A sl D st own idx _ h.pub h.adm.some (fun i hi => (h.adm.bits i hi).1)
      h.adm.order
  table := by
    show Goes _ _ _ (A.tableRun (plAt A sl D own idx).lev) _
    rw [lev_std]
    exact table_std A sl D st own idx _ _ h.pub h.adm.tabs
  clo := Clo.clo_goes_std A sl st own idx _ D h.pub (by have := h.adm.tabs; omega) h.adm.room h.tab
    fun _ => rfl
  zero := Clo.zero_goes A sl st own idx D h.pub
  bits := Clo.bits_goes_std A sl st own idx _ D h.pub h.adm.room fun _ => rfl

/-- The course over the field, read, is the described verifier's plain function. -/
theorem course_std {st : A.St} {p : ℕ} (h : StdC A D st p) (f : List (RV GE))
    (hf : fitsAll (A.runD (plAt A sl D own idx)).fm
      (f.take (A.runD (plAt A sl D own idx)).fm.length) = true) :
    A.lamRun (plAt A sl D own idx) st (f.take (A.runD (plAt A sl D own idx)).fm.length) =
      ((st, fun i : Fin A.m =>
          rdCl A sl (course D f own idx).alpha (A.v i) ((course D f own idx).leaves i),
        (course D f own idx).rows.map (rdRow A sl)) : A.Out) ∧
      (course D f own idx).rounds = f.drop (A.runD (plAt A sl D own idx)).fm.length :=
  course_lamRun A sl _ D st own idx (sims_std own idx h) (numRow_eq A sl D h.pub h.adm.room) f hf

end Lk6.Mid

#print axioms Lk6.Mid.sims_std
#print axioms Lk6.Mid.course_std
