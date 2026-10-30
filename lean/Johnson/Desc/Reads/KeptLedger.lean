-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/KeptLedger.lean: what is left of `KeptAll` (Reads/RowAtSeat.lean) at the lookup's
texts between the fifth place of the output head's segment and the run "policy" is one law on the
ledger each: the text's routine leaves the number of columns of the reads' array.

What is shown. Steps: they speak of the lookup's two written seats at the first chain's state
(`K3.seatCalls`, `K3.seatDigits`, Johnson/Desc/First/Look/K3Seat.lean) and of its run "join"
(`K3.joinRun`, Johnson/Desc/First/Look/K3Runs.lean).
  `cols_of_frame`: a tool: two ledgers whose arrays agree in all but the weights' values
    (`treesFrame`, OnBytes/Model/HideLaws.lean) have as many columns in each array.
  `keptAll_putFork`: writing a ledger gives `KeptAll`, where the new ledger has as many columns in
    the array as the old one.
  `keptAll_mark`: so does the mark that a run of the lookup leaves, at either seat.
  `keptAll_join`: **where the run "join" accepts, `KeptAll` holds**, if the routine that makes the
    claim leaves the array's number of columns.
  `keptAll_digits`: so does what the lookup on the digits lays behind its rounds: it writes four
    fields of the approximate range proof's part of the state, none of which `KeptAll` names, and
    the ledger.

Limits. The law on the ledger is a premise in each: it is shown of no routine of the lookup here.
The runs "objects" and "guests", the decision of the lookup on the digits as a whole, and the merge
are not reached. Nothing on soundness.


-/
import Johnson.Desc.Reads.KeptSmall
import Johnson.Desc.First.Look.K3Seat
import Johnson.Desc.First.Look.K3Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model (Fork Aff treesFrame)
open VerifiableInference.Desc (K3.seatCalls K3.seatDigits K3.joinRun)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.bind_ok ReadsQuiet.named_ok)

/-- Ledgers whose arrays agree in all but the weights' values. -/
theorem cols_of_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees) (i : ℕ) :
    colsAt G i = colsAt F i := by
  have e := congrArg (fun a => (a[i]?).map fun p => p.1.K) h
  simp only [treesFrame, Array.getElem?_map, Option.map_map] at e
  exact e

/-- Writing a ledger. -/
theorem keptAll_putFork (i : ℕ) (s : S) (G : Fork)
    (h : ∀ F, s.fork? = some F → colsAt G i = colsAt F i) : KeptAll i s (s.putFork G) := by
  refine ⟨?_, ?_, fun o ho => ?_⟩
  · unfold S.putFork
    split <;> (try split) <;> rfl
  · unfold S.putFork
    split <;> (try split) <;> rfl
  · by_cases hop : o.opened = true
    · have hF : s.fork? = some o.F := by
        unfold S.fork?
        rw [ho]
        simp [hop]
      refine ⟨{ o with F := G }, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h o.F hF⟩
      unfold S.putFork
      simp [ho, hop]
    · refine ⟨o, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      unfold S.putFork
      simp [ho, hop]

/-- The mark that a run of the lookup leaves, at either seat. -/
theorem keptAll_mark {Cl : Type} (claim : Aff → Cl) (i : ℕ) (s : S) (G : Fork)
    (h : ∀ F, s.fork? = some F → colsAt G i = colsAt F i) :
    KeptAll i s ((K3.seatCalls claim).mark s G) ∧ KeptAll i s ((K3.seatDigits claim).mark s G) :=
  ⟨keptAll_putFork i s G h, keptAll_putFork i s G h⟩

/-- **Where the run "join" accepts.** -/
theorem keptAll_join {Cl : Type} (claim : Aff → Cl) (keys : S → Option (Array Aff)) (i : ℕ)
    {n : ℕ} {s : S} {y : List Cl × S} (hr : K3.joinRun (K3.seatCalls claim) keys n s = .ok y)
    (hlaw : ∀ g KF F x, VerifiableInference.Desc.First.Look.joinF g KF F [] = some x →
      colsAt x.2.1 i = colsAt F i) : KeptAll i s y.2 := by
  unfold VerifiableInference.Desc.K3.joinRun at hr
  obtain ⟨F, h1, hr⟩ := ReadsQuiet.bind_ok hr
  obtain ⟨g, _, hr⟩ := ReadsQuiet.bind_ok hr
  obtain ⟨_, _, hr⟩ := ReadsQuiet.bind_ok hr
  obtain ⟨KF, _, hr⟩ := ReadsQuiet.bind_ok hr
  obtain ⟨x, h5, hr⟩ := ReadsQuiet.bind_ok hr
  have e := congrArg Prod.snd (Except.ok.inj hr)
  rw [← e]
  refine keptAll_putFork i s x.2.1 fun F' hF' => ?_
  have hF : s.fork? = some F := ReadsQuiet.named_ok h1
  rw [hF] at hF'
  rw [← Option.some.inj hF']
  exact hlaw g KF F x (ReadsQuiet.named_ok h5)

/-- What the lookup on the digits lays behind its rounds. -/
theorem keptAll_digits {Cl : Type} (claim : Aff → Cl) (i : ℕ) (s : S)
    (g : OnBytes.Model.Forest.Heard) (G : Fork) {tl : OnBytes.Model.HTailF2} {F : Fork}
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (h : colsAt G i = colsAt F i) :
    KeptAll i s ((K3.seatDigits claim).put s g G) := by
  have e : (K3.seatDigits claim).put s g G =
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G := by
    show (match s.tl?, s.fork? with
      | some tl, some F =>
        (s.putTl { tl with
          foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
          heard := some g }).putFork G
      | _, _ => s.mark "K3 seat: no record of the smallness test") = _
    rw [ht, hF]
  rw [e]
  have k1 := keptAll_putTl i s tl { tl with
    foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some g } ht rfl rfl
    rfl
  refine keptAll_trans k1 (keptAll_putFork i _ G fun F' hF' => ?_)
  have e2 : (s.putTl { tl with
      foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
      heard := some g }).fork? = s.fork? := by
    unfold S.putTl S.fork?
    cases hh : s.here with
    | head a => by_cases ho : a.opened <;> simp [hh, ho]
    | _ => simp [hh]
  rw [e2, hF] at hF'
  rw [← Option.some.inj hF']
  exact h

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.cols_of_frame
#print axioms VerifiableInference.Reads.AtSeat.keptAll_putFork
#print axioms VerifiableInference.Reads.AtSeat.keptAll_mark
#print axioms VerifiableInference.Reads.AtSeat.keptAll_join
#print axioms VerifiableInference.Reads.AtSeat.keptAll_digits
