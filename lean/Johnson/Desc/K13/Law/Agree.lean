-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Agree.lean: the law of the batching's text with a pin that fixes no more than
was committed in front of the draws: the matrix, and the mask entries of ONE message, the ledger.
Statements with their proofs.

`SoundAt` (Johnson/Desc/K13/Law/Law.lean) asks that the pin fixes all that the reader takes from a
witness, a value at every mask entry of every message among it. Messages that are sent behind the
batching's draws have mask entries too, and nothing in front of the draws fixes these: so at a
reader that takes all mask entries from one world that premise cannot be met. Here it is asked only
of what the rows read.
Main names:
  `AgreeAt idx w w'`: the same matrix, and the same mask entries of the message idx.
  `formVal_congr`, `holds_congr`: a row reads the mask entries at its own slots alone.
  `OnLedger idx r`: every mask entry that the row names is of the message idx.
  `rowOf_onLedger`: the row handed on names the ledger's entries alone, if the pile's rows do.
  `SoundAt2`, `batt_sound2`: the form of the law, and the batching's text has it.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/Law.lean names.

What is not claimed. That the pile's rows name the ledger's entries alone is a premise here: the
front of the kind tests it (Johnson/Desc/K13/Text.lean: `front`), and no theorem here hands that on.
That a pin of the protocol fixes the matrix and the ledger's entries is not shown. The number nR of
the matrix's rows is a free letter: that it is the plan's is said nowhere here. `SoundAt2` is tried
against no text but the batching's here. Nothing on the written rounds of a file, on an honest
prover or on hiding.

-/
import Johnson.Desc.K13.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.Ground (takeMasksP)

variable {K : Type} [Field K] (ρ : Reading K) {nR k : ℕ}

/-- The same matrix, and the same mask entries of the message idx. -/
def AgreeAt (idx : ℕ) (w w' : Wit K nR k) : Prop :=
  w.mat = w'.mat ∧ ∀ i, w.mask ⟨idx, i⟩ = w'.mask ⟨idx, i⟩

/-- It goes both ways. -/
theorem AgreeAt.symm {idx : ℕ} {w w' : Wit K nR k} (h : AgreeAt idx w w') : AgreeAt idx w' w :=
  ⟨h.1.symm, fun i => (h.2 i).symm⟩

/-- And on. -/
theorem AgreeAt.trans {idx : ℕ} {w w' w'' : Wit K nR k} (h : AgreeAt idx w w')
    (h' : AgreeAt idx w' w'') : AgreeAt idx w w'' :=
  ⟨h.1.trans h'.1, fun i => (h.2 i).trans (h'.2 i)⟩

/-- Every mask entry that the row names is of the message idx. -/
def OnLedger (idx : ℕ) (r : TensorRow) : Prop := ∀ t ∈ r.masks, t.1.oracle = idx

/-- A mask form reads the mask entries at its own slots alone. -/
theorem formVal_congr {idx : ℕ} {mask mask' : Slot → K} {m : MaskForm}
    (hm : ∀ t ∈ m, t.1.oracle = idx) (h : ∀ i, mask ⟨idx, i⟩ = mask' ⟨idx, i⟩) :
    formVal ρ mask m = formVal ρ mask' m := by
  unfold formVal
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have e : t.1 = ⟨idx, t.1.index⟩ := by
    rw [← hm t ht]
  rw [e, h]

/-- **A row reads the matrix, and the mask entries at its own slots alone.** -/
theorem holds_congr {idx : ℕ} {w w' : Wit K nR k} {r : TensorRow} (hr : OnLedger idx r)
    (h : AgreeAt idx w w') : Holds ρ w r ↔ Holds ρ w' r := by
  unfold Holds lhs colOf
  rw [h.1, formVal_congr ρ hr h.2]

/-- **The row handed on names the ledger's entries alone**, if the pile's rows do. -/
theorem rowOf_onLedger {idx : ℕ} {pile : List TensorRow} {x : E} {ns : List ℕ} {h : Psc.Heard}
    {o : Psc.Out} (hf : Batt.fits k pile = true) (hp : ∀ r ∈ pile, OnLedger idx r)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) (ns.map fun i => ⟨idx, i⟩) h =
      some o) : OnLedger idx (Batt.rowOf pile o) := by
  obtain ⟨_, _, _, _, hmk, _, _⟩ := run_fields hf hr
  intro t ht
  have ht' : t ∈ o.rowMasks := ht
  rw [hmk] at ht'
  rcases List.mem_append.1 ht' with h1 | h1
  · obtain ⟨i, _, hi⟩ := List.mem_map.1 (List.of_mem_zip h1).1
    rw [← hi]
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h1
    have hu' : u ∈ (zipT (Psc.powers oneE x pile.length) pile).flatMap
        fun p => Psc.scaleForm p.1 p.2.masks := hu
    obtain ⟨p, hpm, hup⟩ := List.mem_flatMap.1 hu'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hup
    rw [zipT_eq] at hpm
    exact hp p.2 (List.of_mem_zip hpm).2 v hv

variable [Fintype K] (nR k)

/-- **The form of the law**, of any text f in the batching's place. As `SoundAt`, but the pin fixes
the matrix and the ledger's mask entries alone, and the pile's rows name the ledger's entries alone.
-/
def SoundAt2 (f : RowsOwed → ℕ → ℕ → List TensorRow → ℕ → St → List Fmt.RoundView → Ans (TensorRow × St)) :
    Prop :=
  ∀ (W : Type) (rw : W → Wit K nR k) (Pin : W → Prop) (ledger : ℕ),
    (∀ w w', Pin w → Pin w' → AgreeAt ledger (rw w) (rw w')) →
    ∀ (owed : RowsOwed) (n : ℕ) (pile : List TensorRow) (d : St) (Ex : ExtSpec) (_ : Ex.Str),
    (∀ r ∈ pile, OnLedger ledger r) →
    Doomed (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape
      (Cb.Pv.BattShort.eps (parOf ρ nR k pile) Ex)
      fun τ => ∀ (r : Fmt.RoundView) (rs' : List Fmt.RoundView) (x : E) (hd : Psc.Heard) (out : TensorRow × St),
        oneDrawn "K13.sigma-one-drawn" r = .ok x → heard rs' = .ok hd →
        trOf ρ nR pile Ex x hd = τ → f owed k n pile ledger d (r :: rs') = .ok out →
        ∀ w, Pin w → Holds ρ (rw w) out.1 → ∀ r' ∈ pile, Holds ρ (rw w) r'

/-- **The batching's text has it.** -/
theorem batt_sound2 : SoundAt2 ρ nR k batt := by
  intro W rw Pin ledger hdet owed n pile d Ex y hpile
  by_cases hw : ∃ w0, Pin w0
  · obtain ⟨w0, hw0⟩ := hw
    by_cases hf : Batt.fits k pile = true
    · cases ht : takeMasksP d ledger (Batt.masksOf k) with
      | none =>
        refine Doomed.of_forall _ _ fun τ r rs' x hd out _ _ _ hb => ?_
        obtain ⟨_, _, _, t, _, _, _, _, _, _, _, ht', _⟩ := batt_ok hb
        rw [ht] at ht'
        cases ht'
      | some t =>
        refine Doomed.mono _ _ ?_
          (batt_doomed K ρ nR k (rw w0) pile (t.1.map fun i => ⟨ledger, i⟩) Ex y hf)
        intro τ hτ r rs' x hd out hx hh htr hb w hp hrow r' hr'
        obtain ⟨r1, rs1, x1, t1, hd1, o, e, _, _, hx1, _, ht1, hh1, ho, _, rfl⟩ := batt_ok hb
        obtain ⟨rfl, rfl⟩ := List.cons.inj e
        rw [hx] at hx1
        rw [hh] at hh1
        rw [ht] at ht1
        obtain rfl := Except.ok.inj hx1
        obtain rfl := Except.ok.inj hh1
        obtain rfl := Option.some.inj ht1
        have hA := hdet w w0 hp hw0
        exact (holds_congr ρ (hpile r' hr') hA).2
          (hτ x hd o htr ho ((holds_congr ρ (rowOf_onLedger hf hpile ho) hA).1 hrow) r' hr')
    · refine Doomed.of_forall _ _ fun τ r rs' x hd out _ _ _ hb => ?_
      obtain ⟨_, _, _, _, _, _, _, _, hf', _⟩ := batt_ok hb
      exact absurd hf' hf
  · exact Doomed.of_forall _ _ fun τ r rs' x hd out _ _ _ _ w hp => absurd ⟨w, hp⟩ hw

end VerifiableInference.Desc.K13.Law
