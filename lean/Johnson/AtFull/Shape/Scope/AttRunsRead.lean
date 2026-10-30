-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttRunsRead.lean: WHAT A RETURN OF AN ATTENTION ROW's OWN RUN SAYS: the runs' reader P.inOf
returns at the state in front of it, the state stands in an attention link, and so the two tests on values pass:
the pre of the rows first, keys, join, second and planes, with no coin and no J.

Limits. Implications from a run's return. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.ValsTOfRun
import Johnson.Desc.K5.Honest.Law.RunsJoin
import Johnson.AtFull.Shape.BatchCellsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (named need Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.K3 (seatCalls planesRun joinRun)
open H2K5.Honest (valsTS joinRunA)

section
variable {c : ParC} {u : S}

theorem inOf_of_firstK (h : (P.firstK (P.seatCO c) c u).isSome = true) :
    (P.inOf (P.seatCO c) c u).isSome = true := by
  unfold P.firstK at h
  cases hi : P.inOf (P.seatCO c) c u with
  | none => simp [hi] at h
  | some _ => rfl

theorem inOf_of_keysOfK (h : (P.keysOfK (P.seatCO c) c u).isSome = true) :
    (P.inOf (P.seatCO c) c u).isSome = true := by
  unfold P.keysOfK at h
  cases hi : P.inOf (P.seatCO c) c u with
  | none => simp [hi] at h
  | some _ => rfl

theorem inOf_of_secondK (h : (P.secondK (P.seatCO c) c u).isSome = true) :
    (P.inOf (P.seatCO c) c u).isSome = true := by
  unfold P.secondK at h
  cases hi : P.inOf (P.seatCO c) c u with
  | none => simp [hi] at h
  | some _ => rfl

theorem inOf_of_readers (h : (P.readersOfK (P.seatCO c) c u).isSome = true) :
    (P.inOf (P.seatCO c) c u).isSome = true := by
  unfold P.readersOfK at h
  cases hi : P.inOf (P.seatCO c) c u with
  | none => simp [hi] at h
  | some _ => rfl

theorem some_of_named_map {α β : Type} {w : String} {o : Option α} {f : α → β} {y : β}
    (h : (named w o).map f = (.ok y : Except String β)) : o.isSome = true := by
  cases o with
  | none => cases h
  | some _ => rfl

end

variable {n : Nat} {u : S} {y : List Claim × S}

theorem inOf_of_first {c : ParC} (h : K5Law.runFirst c n u = .ok y) :
    (P.inOf (P.seatCO c) c u).isSome = true :=
  inOf_of_firstK (some_of_named_map (f := fun y => (y.1.map _, y.2)) h)

theorem inOf_of_keys {c : ParC} (h : K5Law.runKeys c n u = .ok y) :
    (P.inOf (P.seatCO c) c u).isSome = true := by
  have k : (P.keysK (P.seatCO c) c u).isSome = true :=
    some_of_named_map (f := fun y => (y.1.map _, y.2)) h
  unfold P.keysK at k
  exact inOf_of_keysOfK (by simpa using k)

theorem inOf_of_second {c : ParC} (h : K5Law.runSecond c n u = .ok y) :
    (P.inOf (P.seatCO c) c u).isSome = true :=
  inOf_of_secondK (some_of_named_map (f := fun y => (y.1.map _, y.2)) h)

theorem keys_of_join {A : Attention.Plan} (h : joinRunA A n u = .ok y) :
    (P.keysOfO A u).isSome = true := by
  cases hk : P.keysOfO A u with
  | some _ => rfl
  | none =>
    exfalso
    change joinRun (seatCalls K3Lot.ofForm) (P.keysOfO A) n u = .ok y at h
    unfold joinRun at h
    rw [hk] at h
    cases hF : (seatCalls K3Lot.ofForm).fork u <;> cases hg : (seatCalls K3Lot.ofForm).heard u <;>
      simp only [named, hF, hg, need, bind, Except.bind] at h <;> (try split at h) <;>
      first | cases h | simp at h

theorem inOf_of_join {A : Attention.Plan} (h : joinRunA A n u = .ok y) :
    (P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) u).isSome = true :=
  inOf_of_keysOfK (keys_of_join h)

theorem readers_of_planes {A : Attention.Plan} {lm : Nat}
    (h : planesRun (seatCalls K3Lot.ofForm) lm (P.readersOfO A) n u = .ok y) :
    (P.readersOfO A u).isSome = true := by
  cases hk : P.readersOfO A u with
  | some _ => rfl
  | none =>
    exfalso
    unfold planesRun at h
    rw [hk] at h
    cases hF : (seatCalls K3Lot.ofForm).fork u <;> cases hg : (seatCalls K3Lot.ofForm).heard u <;>
      simp only [named, hF, hg, need, bind, Except.bind] at h <;> (try split at h) <;>
      first | cases h | simp at h

theorem inOf_of_planes {A : Attention.Plan} {lm : Nat}
    (h : planesRun (seatCalls K3Lot.ofForm) lm (P.readersOfO A) n u = .ok y) :
    (P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) u).isSome = true :=
  inOf_of_readers (readers_of_planes h)

/-- **The tests on values off the reader's return.** -/
theorem valsTS_of_read {A : Attention.Plan}
    (h : (P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) u).isSome = true) : valsTS A u = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨a, ha⟩ := K5Law.att_of_inOf hx
  exact valsTS_of_inOf A ha h

theorem pre_of_first {A : Attention.Plan} (h : K5Law.runFirst (P.parCOf A) n u = .ok y) :
    valsTS A u = true := valsTS_of_read (inOf_of_first h)
theorem pre_of_keys {A : Attention.Plan} (h : K5Law.runKeys (P.parCOf A) n u = .ok y) :
    valsTS A u = true := valsTS_of_read (inOf_of_keys h)
theorem pre_of_second {A : Attention.Plan} (h : K5Law.runSecond (P.parCOf A) n u = .ok y) :
    valsTS A u = true := valsTS_of_read (inOf_of_second h)
theorem pre_of_join {A : Attention.Plan} (h : joinRunA A n u = .ok y) :
    valsTS A u = true := valsTS_of_read (inOf_of_join h)
theorem pre_of_planes {A : Attention.Plan} {lm : Nat}
    (h : planesRun (seatCalls K3Lot.ofForm) lm (P.readersOfO A) n u = .ok y) :
    valsTS A u = true := valsTS_of_read (inOf_of_planes h)

/-- **At the table's own spelling: the five rows whose pre is the two tests.** -/
theorem pre_of_row {A : Attention.Plan} {lm : Nat} {o : Nat × String}
    (ho : o = (2, "first") ∨ o = (2, "keys") ∨ o = (2, "join") ∨ o = (2, "second") ∨
      o = (1, "planes"))
    (h : (tabOf (rowsAtt A lm) o).run n u = .ok y) : (tabOf (rowsAtt A lm) o).pre n u = true := by
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · exact pre_of_first h
  · exact pre_of_keys h
  · exact pre_of_join (n := n) h
  · exact pre_of_second h
  · exact pre_of_planes (n := n) h

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.pre_of_first
#print axioms Johnson.AtFull.Shape.Scope.pre_of_keys
#print axioms Johnson.AtFull.Shape.Scope.pre_of_second
#print axioms Johnson.AtFull.Shape.Scope.pre_of_join
#print axioms Johnson.AtFull.Shape.Scope.pre_of_planes
#print axioms Johnson.AtFull.Shape.Scope.pre_of_row
