-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BatchTest.lean: a test that the further reads in the exact form of honest-verifier zero
knowledge bite, for one IOR (Ior/Honest.lean) and for sets of slots of a batch IOP (Ior/Batch.lean).

An example and theorems on it, all proved here.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction. A slot is one of the N places of a
batch, each with one instance or empty, with its own local transcript.
The example: one round: the prover sends one blinded oracle of one symbol, a bit; the verifier sends
nothing, reads nothing and accepts. The honest prover writes its witness, a bit, into the oracle.
This protocol plainly tells its witness to whoever reads the oracle.

Main names ("simulated exactly" in this sense: `Honest.Exact`, Ior/Honest.lean; for the batch IOP:
`BIOP.Honest.Exact`, Ior/Batch.lean):
  `exact_empty`: at the budget "no further reads" it is simulated exactly: nothing of the oracle is
    shown.
  `one_read_tells`: the view with the one further position shows the witness.
  `not_exact_one`: at every budget that bears the one position, at some ρ, it is not simulated
    exactly, by any simulator, in this sense: `¬ H.Exact (fun _ _ _ => True) bud`.
  `exactB_empty`, `not_exactB_one`: the same for the batch IOP with this protocol in every slot, for
    every number N of slots and every slot j0.
So a parameter list that asks for exact simulation only at "T = ∅" is met by a protocol that hides
nothing in its unread oracles (shown here of the list's item on exact simulation alone:
`exact_empty`, `exactB_empty`; this file builds no parameter list); one that asks for a budget which
bears a position of each blinded oracle is not (shown here of this one protocol, at the relation
`fun _ _ _ => True`: `not_exact_one`, `not_exactB_one`).

Limits: this file says nothing on which budget a list should ask.
Terms: lean/GLOSSARY.md.
-/
import Ior.OnlineHon

set_option autoImplicit false

namespace Iop.BatchTest
open Prob IOR

/-- one round: the prover sends one oracle of one symbol (a bit), no plain part; the verifier sends
nothing -/
abbrev r : Round :=
  { Orc := Bool, Pos := Unit, Sym := fun _ => Bool, rd := fun o _ => o, Plain := Unit, Chal := Unit,
    dOrc := false, dPlain := () }

theorem pure_inj {α : Type} {a b : α} (h : PMF.pure a = PMF.pure b) : a = b := by
  have h1 : a ∈ (PMF.pure b).support := by
    rw [← h, PMF.support_pure]
    exact Set.mem_singleton a
  rw [PMF.support_pure] at h1
  exact h1

/-! ## 1. One IOR -/

/-- an "IOPP" whose verifier reads nothing and accepts; E is any kind of external oracles -/
abbrev Q (E : ExtSpec) : IOR Unit E Unit extNone where
  shape := [r]
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun _ _ _ => some ()
  imp := fun _ _ => ()
  srcE := fun _ _ => ∅
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- the honest prover writes its witness (a bit) into the oracle, in clear -/
abbrev H : (Q extNone).Honest Bool Unit where
  Coin := Unit
  strat := fun w _ _ => ((w, ()), fun _ => ((), ()))
  Bad := ∅
  Hid := fun _ _ => ∅

/-- the one position -/
abbrev pos : OPos [r] := Sum.inl ()

theorem output_eq (w : Bool) (ρ : Rho [r]) (T : Finset (OPos [r])) :
    H.output w () ρ T = PMF.pure (some ((Q extNone).view T ((w, ()), ρ.1, ()))) := by
  have hm : ρ ∉ H.withheld w () := fun h => h.elim id id
  have hr : ∀ ρ : Rho [r],
    (fun c : Unit => some ((Q extNone).view T (Strat.run (H.strat w () c) ρ).1)) =
      fun _ => some ((Q extNone).view T ((w, ()), ρ.1, ()))
    | (_, _) => rfl
  unfold IOR.Honest.output
  rw [if_neg hm]
  exact (congrArg (fun φ => PMF.map φ _) (hr ρ)).trans (PMF.map_const _ _)

/-- At the budget "no further reads" the protocol is simulated exactly (in this sense:
`H.Exact (fun _ _ _ => True) (fun _ T => T = ∅)`; `Honest.Exact`, Ior/Honest.lean). -/
theorem exact_empty : H.Exact (fun _ _ _ => True) (fun _ T => T = ∅) := by
  classical
  refine ⟨fun _ _ _ _ => PMF.pure (some ⟨((), ()), fun _ => none⟩), ?_⟩
  intro x y w _ ρ _ T hT
  subst hT
  rw [output_eq]
  refine congrArg (fun v => PMF.pure (some v)) ?_
  have ho : ((Q extNone).view ∅ ((w, ()), ρ.1, ())).orc = fun _ => none := by
    funext p
    have hn : ¬ (p ∈ (∅ : Finset (OPos [r])) ∨ p ∈ (∅ : Finset (OPos [r])) ∨ true = false) := by
      rintro (h | h | h)
      · exact Finset.notMem_empty _ h
      · exact Finset.notMem_empty _ h
      · exact Bool.noConfusion h
    simp only [IOR.view]
    exact if_neg hn
  exact congrArg (fun o => (⟨((), ()), o⟩ : View (Q extNone))) ho

/-- One further read shows the witness. -/
theorem one_read_tells (w : Bool) (c : Unit) (T : Finset (OPos [r])) (hT : pos ∈ T) :
    ((Q extNone).view T ((w, ()), c, ())).orc pos = some w := by
  classical
  exact if_pos (Or.inr (Or.inl hT))

/-- At every budget that bears the one position the protocol is not simulated exactly (in this
sense: `¬ H.Exact (fun _ _ _ => True) bud`; `Honest.Exact`, Ior/Honest.lean). -/
theorem not_exact_one (bud : Rho [r] → Finset (OPos [r]) → Prop) (h : ∃ ρ T, bud ρ T ∧ pos ∈ T) :
    ¬ H.Exact (fun _ _ _ => True) bud := by
  rintro ⟨S, hS⟩
  obtain ⟨ρ, T, hb, hT⟩ := h
  have h1 := hS () () true trivial ρ (fun h => h) T hb
  have h2 := hS () () false trivial ρ (fun h => h) T hb
  have h3 :=
    pure_inj (((output_eq true ρ T).symm.trans h1).trans (h2.symm.trans (output_eq false ρ T)))
  have h4 := congrArg (fun v : View (Q extNone) => v.orc pos) (Option.some.inj h3)
  have h5 : some true = some false :=
    (one_read_tells true ρ.1 T hT).symm.trans (h4.trans (one_read_tells false ρ.1 T hT))
  cases h5

/-! ## 2. Sets of slots of a batch IOP -/

/-- the protocol in every slot: a local round in which only the slot speaks -/
abbrev QB : BIOP Unit (extNone.prod extNone) := ⟨Q (extNone.prod extNone), RoundSplits.allLocal [r]⟩

/-- the honest prover of a slot writes the slot's witness into the oracle -/
abbrev HB : QB.Honest Unit Bool where
  Coin0 := Unit
  Coin := Unit
  strat0 := fun _ _ => ((), fun _ => ())
  strat := fun _ _ _ w _ => ((w, ()), fun _ => ())
  Bad := ∅
  stop0 := fun _ => false

theorem not_withheld (ρ : Rho [r]) : ρ ∉ HB.withheld := fun h =>
  h.elim id fun h => Bool.noConfusion h

theorem run_eq (w : Bool) (c : Unit × Unit) :
    ∀ ρ : Rho [r], (Strat.run (HB.one () () w c) ρ).1 = ((w, ()), ρ.1, ())
  | (_, _) => rfl

open Classical in
/-- The output for J, when slot j holds the witness ws j. -/
theorem outputB_eq {N : ℕ} (ws : Fin N → Bool) (ρ : BRho N [r] (RoundSplits.allLocal [r]))
    (J : Finset (Fin N)) (Ts : J → Finset (OPos [r])) :
    HB.output () () (fun j => some ((), (), ws j)) ρ J Ts =
      PMF.pure fun j =>
        some (QB.ior.dviewT (Ts j) ((), ()) ((ws j.1, ()), (ρ.slot j.1).1, ())) := by
  rw [OnlineHon.outputQ_eq HB () () (fun j => some ((), (), ws j)) ρ J Ts
      (fun j => ((), (), ws j.1)) fun _ => rfl]
  have : (fun (c : HB.Coin0 × (Fin N → HB.Coin)) (j : J) =>
        if ρ.slot j.1 ∈ HB.withheld then none
        else
          some (QB.ior.dviewT (Ts j) ((), ())
              (Strat.run (HB.one () () (ws j.1) (c.1, c.2 j)) (ρ.slot j.1)).1)) =
      fun _ j => some (QB.ior.dviewT (Ts j) ((), ()) ((ws j.1, ()), (ρ.slot j.1).1, ())) := by
    funext c j
    rw [if_neg (not_withheld _), run_eq]
    rfl
  exact (congrArg (fun φ => PMF.map φ _) this).trans (PMF.map_const _ _)

/-- At the budget "no further reads" the batch IOP is simulated exactly, for every set of non-empty
slots (in this sense: `HB.Exact N (fun _ _ _ => True) (fun _ _ Ts => ∀ j, Ts j = ∅)`;
`BIOP.Honest.Exact`, Ior/Batch.lean). -/
theorem exactB_empty (N : ℕ) : HB.Exact N (fun _ _ _ => True) (fun _ _ Ts => ∀ j, Ts j = ∅) := by
  classical
  refine ⟨fun J _ _ _ ans => PMF.pure fun j => some ⟨((), ()), ans j, fun _ => none⟩, ?_⟩
  intro w0 y0 a _ J as has ρ Ts hT
  rw [OnlineHon.outputQ_eq HB w0 y0 a ρ J Ts as has]
  refine Eq.trans (congrArg (fun φ => PMF.map φ _) (funext fun c => funext fun j => ?_))
    (PMF.map_const _ _)
  rw [if_neg (not_withheld _)]
  refine congrArg some (OnlineHon.dview_ext rfl ?_ (funext fun p => if_neg ?_))
  · show (extNone.prod extNone).ans (QB.ior.given (Tr.rho _) (Ts j)) _ = _
    rw [Strat.rho_run]
  · rw [hT j]
    rintro (h | h | h)
    · exact Finset.notMem_empty _ h
    · exact Finset.notMem_empty _ h
    · exact Bool.noConfusion h

/-- At every budget that bears the one position in one slot the batch IOP is not simulated exactly
(in this sense: `¬ HB.Exact N (fun _ _ _ => True) bud`; `BIOP.Honest.Exact`, Ior/Batch.lean). -/
theorem not_exactB_one (N : ℕ) (bud : BudB [r] N)
    (h : ∃ (ρ : BRho N [r] (RoundSplits.allLocal [r]))
          (J : Finset (Fin N)) (Ts : J → Finset (OPos [r])) (j0 : J),
        bud J (fun j => ρ.slot j.1) Ts ∧ pos ∈ Ts j0) :
    ¬ HB.Exact N (fun _ _ _ => True) bud := by
  classical
  rintro ⟨S, hS⟩
  obtain ⟨ρ, J, Ts, j0, hb, hT⟩ := h
  have h1 := hS () () (fun _ => some ((), (), true)) (fun _ _ _ => trivial) J
    (fun _ => ((), (), true)) (fun _ => rfl) ρ Ts hb
  have h2 := hS () () (fun _ => some ((), (), false)) (fun _ _ _ => trivial) J
    (fun _ => ((), (), false)) (fun _ => rfl) ρ Ts hb
  have h3 := pure_inj
    (((outputB_eq (fun _ => true) ρ J Ts).symm.trans h1).trans
      (h2.symm.trans (outputB_eq (fun _ => false) ρ J Ts)))
  have h4 := congrArg (fun v : DView QB.ior.toInteractiveOracleProof => v.orc pos) (Option.some.inj (congrFun h3 j0))
  have e : ∀ w : Bool,
      (QB.ior.dviewT (Ts j0) ((), ()) ((w, ()), (ρ.slot j0.1).1, ())).orc pos = some w :=
    fun w => if_pos (Or.inr (Or.inl hT))
  have h5 : some true = some false := (e true).symm.trans (h4.trans (e false))
  cases h5

end Iop.BatchTest
