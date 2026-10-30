-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/Atoms.lean: the shape of the ledger behind one run of
`hideRun` (values set under slots), one owed claim, one masked sumcheck: each as an equation on the
whole of `ledSh`. Conditional, from a return, but at the owed claim, which needs none. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there ledger, slot, hearing, sumcheck, face and shape (of the
ledger). In this file: the shape of the ledger is `ledSh F` (`LedSh`,
Johnson/Desc/First/Shape/Parts.lean): it holds no field element: counts, sizes, marks. `Sized F`
says that the ledger's three arrays have their size. The steps `Op.owe`, `Op.left` and `Op.sum` are
those of Honest/K3/Shape/Ops.lean.

What is shown.
  `hideRun_sh`: a run of `hideRun` that returned: the marks of just these slots are set; all else
    stays.
  `owe_sh`: a claim more is owed.
  `ownSlots_blind`: a sumcheck's number of own slots depends on its variables' degrees alone.
  `hear_sh`: the hearing of a masked sumcheck that returned.
  `left_sh`: the same without end values: `Op.left`.
  `whole_sh`: hearing and row at once: `Op.sum`.
Helper: `fillB_zero`. `hideRun_sh`, `hear_sh`, `left_sh` and `whole_sh` also give `Sized` of the
ledger behind. `owe_sh` says nothing of `Sized`.

Hypotheses that remain.
  `h`, `hh`, `hw`: the return. (In `ownSlots_blind` `h` is another thing: the two lists of variables
    have the same degrees.)
  `hS`: the ledger in front has its three arrays at their size (`Sized`): `hideRun` itself tests one
    of the three sizes alone.

Follows. The proofs rest on `hide_of_free` (Johnson/Desc/First/Shape/Parts.lean),
and on the library's `hideRun_ok`, `hear_spec`, `whole_parts`, `row_write`, `heard_lenK`
and `readAll_values_len`.

Users. Honest/K3/Shape/Walk.lean imports this file.

Limits. All statements are implications, but `owe_sh` and `fillB_zero`, which are plain equations.
No statement of this file says that anything returns.
No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Ops
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First.Shape (LedSh ledSh fillB hide_of_free)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Var Heard ownSlots)

theorem fillB_zero (got : List Bool) (first : Nat) : fillB got first 0 = got := by
  simp [fillB]

/-- **A run of `hideRun` that returned.** Conditional on the return and on `Sized` in front. -/
theorem hideRun_sh {F G : Fork} {first : Nat} {v : Array E} {x : E} (hS : Sized F)
    (h : F.hideRun first v x = some G) :
    Sized G ∧ ledSh G = (ledSh F).setGot (fillB (ledSh F).got first v.size) := by
  obtain ⟨_, a2, a3, _⟩ := OnBytes.PscRun.hideRun_ok F G first v x hS h
  refine ⟨a2, ?_⟩
  by_cases hz : v.size = 0
  · have hv : v = #[] := Array.eq_empty_of_size_eq_zero hz
    subst hv
    rw [MaskedSum.hideRun_nil] at h
    obtain rfl := Option.some.inj h
    show ledSh F = (ledSh F).setGot (fillB (ledSh F).got first 0)
    rw [fillB_zero]
    rfl
  · have hn : first + v.size ≤ F.ns := by
      have := (a3 (v.size - 1) (by omega)).1
      omega
    obtain ⟨H, hH, _, _, e⟩ := hide_of_free hS hn (fun i hi => (a3 i hi).2.1) x
    obtain rfl : H = G := Option.some.inj (hH.symm.trans h)
    exact e

/-- **A claim more is owed.** No hypothesis. -/
theorem owe_sh (F : Fork) (w : String) : ledSh (F.owe w).2 = Op.owe.on (ledSh F) := by
  have e : (F.owe w).2.owed.toList.map (·.added) = F.owed.toList.map (·.added) ++ [false] := by
    simp [Fork.owe]
  show LedSh.mk F.ns F.vp.size F.mf.size F.gotF.toList ((F.owe w).2.owed.toList.map (·.added))
      F.planClaimsF (F.trees.toList.map VerifiableInference.Desc.First.Shape.treeSh) F.next
      F.LS.size F.nClaim F.thetaDrawnF F.kapMapF.toList F.doorShutF = _
  rw [e]
  rfl

/-- A sumcheck's number of own slots depends on its variables' degrees alone. -/
theorem ownSlots_blind {vs ws : List Var} (h : vs.map Var.d = ws.map Var.d) :
    ownSlots vs = ownSlots ws := by
  rw [MaskedSum.ownSlots_one_add, MaskedSum.ownSlots_one_add]
  have e : (vs.map fun v => v.d - 1) = ws.map fun v => v.d - 1 := by
    have := congrArg (List.map (· - 1)) h
    simpa [List.map_map, Function.comp_def] using this
  rw [e]

/-- **The hearing of a masked sumcheck that returned.** Conditional on the return and on `Sized`. -/
theorem hear_sh {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} (hS : Sized F)
    (hh : MaskedSum.hear C k F rs = some (h, G)) :
    Sized G ∧ ledSh G = (setNext (ledSh F) (F.next + ownSlots k.all + k.endsN)).setGot
      (fillB (ledSh F).got (F.next + ownSlots k.all) k.endsN) := by
  obtain ⟨_, T, R, _, hR, _, hw⟩ := MaskedSum.hear_spec hh
  have hn := MaskedSum.readAll_values_len hR
  have hS' : Sized ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork) := hS
  obtain ⟨s, e⟩ := hideRun_sh hS' hw
  refine ⟨s, ?_⟩
  rw [e, List.size_toArray, hn]
  rfl

/-- **Without end values: the count goes on; nothing is filled.** Conditional on the same. -/
theorem left_sh {C : Aff} {vs : List Var} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hS : Sized F)
    (hh : MaskedSum.hear C { lead := 0, vs := vs, ends := none } F rs = some (h, G)) :
    Sized G ∧ ledSh G = (Op.left (ownSlots vs)).on (ledSh F) := by
  obtain ⟨s, e⟩ := hear_sh hS hh
  refine ⟨s, ?_⟩
  rw [e]
  show (setNext (ledSh F) (F.next + ownSlots vs + 0)).setGot
      (fillB (ledSh F).got (F.next + ownSlots vs) 0) = _
  rw [fillB_zero]
  rfl

/-- **Hearing and row at once.** Conditional on the same. -/
theorem whole_sh {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} (hS : Sized F)
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) :
    Sized G ∧ ledSh G = (sumOp k).on (ledSh F) := by
  obtain ⟨_, Gm, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  obtain ⟨s1, e1⟩ := hear_sh hS hh
  obtain ⟨a1, _, a3⟩ := MaskedSum.heard_lenK hh
  obtain ⟨s2, e2⟩ := hideRun_sh s1 (MaskedSum.row_write hr)
  refine ⟨s2, ?_⟩
  rw [e2, e1, Array.size_replicate, a3, a1]
  rfl

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.fillB_zero
#print axioms ProofFile.Honest.K3.Shape.hideRun_sh
#print axioms ProofFile.Honest.K3.Shape.owe_sh
#print axioms ProofFile.Honest.K3.Shape.ownSlots_blind
#print axioms ProofFile.Honest.K3.Shape.hear_sh
#print axioms ProofFile.Honest.K3.Shape.left_sh
#print axioms ProofFile.Honest.K3.Shape.whole_sh
