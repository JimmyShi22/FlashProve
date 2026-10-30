-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsAtS.lean: the run "K8.equations" at the record that the proof
file's first chain carries (Johnson/Desc/First/State.lean: S) CARRIES: what was heard stands, at both
readings of "heard", and where the ledger in front has its sizes, the ledger behind is a later one with
its sizes (CarriesFo, Johnson/Desc/First/LedgerAtFo.lean).

Definitions, statements and proofs.
No routine of `verify-on-bytes` is named. USED: carriesFoOfLater, CarriesFo
(Johnson/Desc/First/LedgerAtFo.lean), S.fork_putFork, S.fork_putTl, S.look_putFork, S.look_putTl;
the two small laws tl_putFork and tl_putTl are typed after tl_putFork'
(Johnson/Desc/First/K9x/ReadingsAtK9.lean) and a tl_putTl whose file is not in this library: they
lay above files that this one does not import; of the files under OnBytes/, on records alone:
PscRun.Later, Forest.Heard.
Main names:
  carries_shape_look, carries_shape_digits: for ANY run whose yes has the shape: the ledger F, the record
    tl and the tables funs are read off s; equations … tl funs F = .ok (tl', F1, cl); the record behind
    is (s.putTl tl').putFork F1.
  equationsAtS: that run, written out; equationsAtS_ok; atS_carries_look, atS_carries_digits.
Limits: from a yes alone. That k8Equations (Johnson/Desc/First/Batch/ObjectsAtS.lean) is
equationsAtS is not shown here (its file is not imported): its yes has the shape, by its text.

-/
import Johnson.Desc.First.TailClaims.EquationsLater
import Johnson.Desc.First.LedgerAtFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First (S)

/-- The digits' seat's reading of "heard": off the smallness test's record. -/
def heardAtTl (s : S) : Option Forest.Heard := s.tl?.bind (·.heard)

theorem tl_putFork (s : S) (F : Fork) : (s.putFork F).tl? = s.tl? := by
  unfold S.putFork
  split
  · rename_i a hh
    simp [S.tl?, hh]
  · rename_i a hh
    simp [S.tl?, hh]
  · rename_i a hh
    split
    · rename_i ho
      simp [S.tl?, hh, ho]
    · rfl
  · rfl

theorem tl_putTl (s : S) (tl tl' : HTailF2) (h : s.tl? = some tl) : (s.putTl tl').tl? = some tl' := by
  unfold S.putTl
  unfold S.tl? at h
  split
  · simp [S.tl?]
  · simp [S.tl?]
  · rename_i a hh
    rw [hh] at h
    split
    · rename_i ho
      simp [S.tl?, ho]
    · rename_i ho
      simp [ho] at h
  · rename_i h₁ h₂ h₃
    cases hh : s.here <;> simp_all

section
variable {front : Nat} {s s' : S} {F F1 : Fork} {tl tl' : HTailF2} {funs : Array HFun}
  {cl : List Claim}

theorem shape_fork (hF : s.fork? = some F) (he : s' = (s.putTl tl').putFork F1)
    (hx : equations front tl funs F = .ok (tl', F1, cl)) :
    ∀ F', s.fork? = some F' → ∃ G, s'.fork? = some G ∧ OnBytes.PscRun.Later F' G := by
  intro F' hF'
  obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
  refine ⟨F1, ?_, eq_later hx⟩
  rw [he]
  exact S.fork_putFork _ F _ (by rw [S.fork_putTl]; exact hF)

/-- At the reading S.lookHeard?. -/
theorem carries_shape_look (hF : s.fork? = some F) (he : s' = (s.putTl tl').putFork F1)
    (hx : equations front tl funs F = .ok (tl', F1, cl)) :
    CarriesFo S.fork? S.lookHeard? s s' :=
  carriesFoOfLater _ _ _ _
    (fun g hg => by rw [he, S.look_putFork, S.look_putTl]; exact hg) (shape_fork hF he hx)

/-- At the digits' seat's reading. -/
theorem carries_shape_digits (hF : s.fork? = some F) (ht : s.tl? = some tl)
    (he : s' = (s.putTl tl').putFork F1)
    (hx : equations front tl funs F = .ok (tl', F1, cl)) :
    CarriesFo S.fork? heardAtTl s s' :=
  carriesFoOfLater _ _ _ _
    (fun g hg => by
      unfold heardAtTl at hg ⊢
      rw [ht] at hg
      rw [he, tl_putFork, tl_putTl s tl tl' ht]
      show tl'.heard = some g
      rw [eq_same (fun t => t.heard) hx (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ _ _ => rfl)]
      exact hg) (shape_fork hF he hx)

end

/-- "K8.equations" at S, written out. After k8Equations
(Johnson/Desc/First/Batch/ObjectsAtS.lean). -/
def equationsAtS (front : Nat) (s : S) : Except String (List Claim × S) :=
  match s.fork?, s.tl?, s.funs? with
  | some F, some tl, some funs =>
    (equations (F.nClaim + front) tl funs F).map fun x => (x.2.2, (s.putTl x.1).putFork x.2.1)
  | _, _, _ => .error "K9.in-a-segment"

theorem equationsAtS_ok {front : Nat} {s s' : S} {cl : List Claim}
    (h : equationsAtS front s = .ok (cl, s')) :
    ∃ (F F1 : Fork) (tl tl' : HTailF2) (funs : Array HFun), s.fork? = some F ∧ s.tl? = some tl ∧
      s.funs? = some funs ∧ equations (F.nClaim + front) tl funs F = .ok (tl', F1, cl) ∧
      s' = (s.putTl tl').putFork F1 := by
  unfold equationsAtS at h
  split at h
  · rename_i F tl funs hF ht hf
    cases hx : equations (F.nClaim + front) tl funs F with
    | error e => rw [hx] at h; cases h
    | ok x =>
      rw [hx] at h
      obtain ⟨tl', F1, cls⟩ := x
      have e := Except.ok.inj h
      obtain rfl : cls = cl := congrArg Prod.fst e
      exact ⟨F, F1, tl, tl', funs, hF, ht, hf, hx, (congrArg Prod.snd e).symm⟩
  · cases h

theorem atS_carries_look {front : Nat} {s s' : S} {cl : List Claim}
    (h : equationsAtS front s = .ok (cl, s')) : CarriesFo S.fork? S.lookHeard? s s' := by
  obtain ⟨F, F1, tl, tl', funs, hF, -, -, hx, he⟩ := equationsAtS_ok h
  exact carries_shape_look hF he hx

theorem atS_carries_digits {front : Nat} {s s' : S} {cl : List Claim}
    (h : equationsAtS front s = .ok (cl, s')) : CarriesFo S.fork? heardAtTl s s' := by
  obtain ⟨F, F1, tl, tl', funs, hF, ht, -, hx, he⟩ := equationsAtS_ok h
  exact carries_shape_digits hF ht he hx

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.carries_shape_look
#print axioms VerifiableInference.Desc.First.TailClaims.Law.carries_shape_digits
#print axioms VerifiableInference.Desc.First.TailClaims.Law.atS_carries_look
#print axioms VerifiableInference.Desc.First.TailClaims.Law.atS_carries_digits
