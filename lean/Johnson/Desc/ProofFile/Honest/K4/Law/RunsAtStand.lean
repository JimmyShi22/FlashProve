-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/RunsAtStand.lean: CONDITIONAL. Statements with their proofs.

Not shown here. No property is claimed. THAT THE PREMISES CAN BE MET: no example is known. THAT THE
RUNS RETURN IS NOT SHOWN OUTRIGHT: it is drawn from the library's `KeptAsks`
(Johnson/Road/K4/Total/AtKept.lean), seven premises on the verifier's state in front of the step and
on the listing of the claims, which stay premises here. It says that the runs return, not what a
form is worth. No statement here calls `K4Seated.fits`.

What is here: at a stand (`K4Stand`, Law/SlotsTrue.lean) of the layers' own rounds (the sub-protocol
K4): the run "front" returns from the ledger that the step leaves; the values that it reads under
the row products' sumcheck's end slots are shown there; the run "back" returns from the ledger that
"front" leaves, and from the one that the step leaves. In the letters in which the statements on the
own claims ask these returns (Law/OwnAtStand.lean: `rows_stand`, `merge_stand`, `ownFront_stand`,
`ownBack_stand`; Law/WoAtStand.lean). WHO HOLDS `KeptAsks`: the clause asks of the hypothesis
`K4FrontAt` (Law/Kept.lean; `K4Front` is that structure at every step), which the statements on K4's
own share ask in any case; at the thread with the library's own values `asks_head`
(Law/FrontHead.lean) has it. Calls: `runs_return_behind` (Johnson/Road/K4/Total/RunsReturnLaw.lean)
at the hearing's own return (`step_tape`, Law/RowBatch.lean); `formsFrontWith_some`
(OnBytes/Desc/First/K4/ClaimsLaws.lean); `formsFrontWith_later`, `formsBack_later`
(Johnson/Desc/First/K4/LedgerKeeps.lean).

OF THE SEVEN, AT A STAND: `sized` is the stand's own field; `skel`, `y₀`, `rd₀` hold at what the
step itself has heard and the place's own public data. THREE ARE LEFT (`keptAsks_own`): free: in
front of the step the ledger is free from its next free slot on; leaves: the lookup's leaves'
sumcheck has its four marks, and its window lies below that slot, there and free; member: THE
LISTING "front" RETURNS AT WHAT THE STEP HAS HEARD. For the last no statement is known; the first
two are the lookup's and the promise's in front.

  `skel_refl`   a structure has its own skeleton
  `keptAsks_own`   **`KeptAsks` at what the step itself has heard, from the three that are left**
  `stand_runs`   **BOTH RUNS RETURN, "back" BEHIND "front", with what "front" reads as shown and the
      ledgers' order**
  `stand_back`   "back" returns from the ledger that the step leaves

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Road.K4.Total.AtKept
import Johnson.Desc.First.K4.LedgerKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Model (Aff Fork)
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later Filled)
open OnBytes.Desc.First.K4 (Par front formsFrontWith formsBack)
open OnBytes.Desc.First.K4.Total (KeptAsks Skel WinFree)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- A structure has its own skeleton. -/
theorem skel_refl (o : Own) : Skel o o := by
  exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- **THE LIBRARY's SEVEN AT WHAT THE STEP ITSELF HAS HEARD, FROM THE THREE THAT ARE LEFT.** hfree,
hleaves: `KeptAsks`' own clauses free and leaves, to the letter. hmem: the listing "front" returns
at what the step has heard, at some two forms. CONDITIONAL on the stand and on the three. -/
theorem keptAsks_own
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hfree : ∀ a, s.here = .lay a → ∀ j, a.F.next ≤ j → ¬ Filled a.F j)
    (hleaves : ∀ a fo, s.here = .lay a → a.fo = some fo →
      OnBytes.Desc.First.K4.Total.Ready fo.leaves ∧
      fo.leaves.first + fo.leaves.walk.1.length ≤ a.F.next ∧ WinFree fo.leaves a.F)
    (hmem : ∃ a b, (front (!p.k3Runs) p.P p.g o a b).isSome = true) :
    KeptAsks p s s' p.P o := by
  refine ⟨Z.sized, hfree, hleaves, fun o' ho' => ?_, rfl, rfl, hmem⟩
  have e : o' = o := Option.some.inj (ho'.symm.trans Z.heard)
  rw [e]
  exact skel_refl o

/-- **BOTH RUNS RETURN AT A STAND.** fs₁, F₁: what "front" leaves, run from the ledger that the step
leaves. sh: what that ledger shows under the slots of the row products' sumcheck's end values. fs₂,
F₂: what "back" leaves, run from F₁. CONDITIONAL on the stand and on the library's seven. -/
theorem stand_runs
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    {P₀ : OnBytes.Model.Layer.Pub} {o₀ : Own} (Ak : KeptAsks p s s' P₀ o₀) :
    ∃ (fs₁ : Array Aff) (F₁ : Fork) (fs₂ : Array Aff) (F₂ : Fork) (sh : Array OnBytes.E),
      formsFrontWith (!p.k3Runs) Q.P Q.g o A.F = some (fs₁, F₁) ∧
      ((Array.range (4 * Q.P.y.NI)).mapM fun i => A.F.shown (o.H.tV.sEnd + i)) = some sh ∧
      Later A.F F₁ ∧ formsBack o F₁ = some (fs₂, F₂) ∧ Later F₁ F₂ := by
  obtain ⟨a, a₀, fo, _, ha0, haF, hfo, hh, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  obtain ⟨eP, _, eg, _, _⟩ := Z.seat.own
  obtain ⟨l1, l2, l3⟩ := Ak.leaves a₀ fo ha0 hfo
  rw [haF] at hh
  obtain ⟨⟨fs₁, F₁, hf, fs₂, F₂, hb⟩, _⟩ :=
    OnBytes.Desc.First.K4.Total.runs_return_behind (rows := !p.k3Runs) (Pr := Q.P) (P₀ := P₀)
      (o₀ := o₀) hh rfl rfl
      ⟨Ak.sized a₀ ha0, l1, l2, Ak.skel o Z.heard, by rw [Ak.y₀, eP], by rw [Ak.rd₀, eP],
        by rw [← eg]; exact Ak.member⟩ (Ak.free a₀ ha0) l3
  obtain ⟨sh, _, _, _, _, hsh, _⟩ := OnBytes.Desc.First.K4.formsFrontWith_some hf
  exact ⟨fs₁, F₁, fs₂, F₂, sh, hf, hsh, OnBytes.Desc.First.K4.formsFrontWith_later hf, hb,
    OnBytes.Desc.First.K4.formsBack_later hb⟩

/-- **"back" returns from the ledger that the step leaves.** CONDITIONAL as `stand_runs`. -/
theorem stand_back
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    {P₀ : OnBytes.Model.Layer.Pub} {o₀ : Own} (Ak : KeptAsks p s s' P₀ o₀) :
    ∃ (fs₂ : Array Aff) (F₂ : Fork), formsBack o A.F = some (fs₂, F₂) ∧ Later A.F F₂ := by
  obtain ⟨a, a₀, fo, _, ha0, haF, hfo, hh, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  obtain ⟨eP, _, eg, _, _⟩ := Z.seat.own
  obtain ⟨l1, l2, l3⟩ := Ak.leaves a₀ fo ha0 hfo
  rw [haF] at hh
  obtain ⟨_, fs₂, F₂, hb⟩ :=
    OnBytes.Desc.First.K4.Total.runs_return_behind (rows := !p.k3Runs) (Pr := Q.P) (P₀ := P₀)
      (o₀ := o₀) hh rfl rfl
      ⟨Ak.sized a₀ ha0, l1, l2, Ak.skel o Z.heard, by rw [Ak.y₀, eP], by rw [Ak.rd₀, eP],
        by rw [← eg]; exact Ak.member⟩ (Ak.free a₀ ha0) l3
  exact ⟨fs₂, F₂, hb, OnBytes.Desc.First.K4.formsBack_later hb⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.skel_refl
#print axioms ProofFile.Honest.K4.keptAsks_own
#print axioms ProofFile.Honest.K4.stand_runs
#print axioms ProofFile.Honest.K4.stand_back
