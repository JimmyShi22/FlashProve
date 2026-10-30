-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FibreOf.lean: from a count of sampled values to a count of challenges, general
in the entry: few bad typed values of a round give few bad strings of hash blocks and few bad
written verifier messages. Statements and proofs.

The factor is the bound `w` on the fibres of the round's block sampler (`bsRound f e k`,
Run/PlanDraws.lean). Every statement is a corollary of lemmas of this library: `cnt_comp_le`
(Prob/Bias.lean), `BS.Good.fib` from `planDraws_law`, `GChal.cnt_pass`, `valsOf`, `vals_inj` and
`evE_inj` (OnBytes/Slice/Draws.lean), `gOne` (OnBytes/Slice/RoundsMaps.lean).
Main names:
  `cnt_blocks_le`: `e.logN ≤ 64` gives `cnt (fun u => Q ((bsRound f e k).φ u)) ≤ cnt Q * (bsRound f
    e k).w`, at any field, entry and kind and any set `Q` of typed values.
  `cnt_chal_le`: the same at a written round's verifier messages that pass the round's test of work.
  `cnt_chal_inj`: the same through any injective reading `g` of the typed values: `cnt (pass ∧ P (g
    (valsOf d c))) ≤ cnt P * w`.
  `cnt_chal_all`: without the test of work: the factor `2 ^ work` more (over `cnt_old`).
  `pass_of_zero`: where the entry asks no bits of work every verifier message passes.
  `OneElem d`: the round draws one element of the extension field and nothing else (`Fmt.dsOf
    d.entry d.kind = [.elem, .trits 0]`; decidable).
  `gOne_inj`, `cnt_chal_one`: at such a round: `cnt (pass ∧ P (the drawn element, read in the
    field)) ≤ cnt P * w`.
Limits: It does not say how large `w` is against the number of challenges (`BS.Good.ratio` and
`RoundBelow` say that). It says nothing of a round that draws more than its reading `g` sees: there
`g` is not injective, and the number of the other values is a further factor. No soundness is
claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import OnBytes.Slice.RoundsMaps
import Prob.Bias

set_option autoImplicit false
namespace H2K.Fibre
open Prob Iop Run OnBytes.Slice

theorem cnt_blocks_le (f : Fmt.Fld) (e : Fmt.Entry) (k : Fmt.Kind) (h : e.logN ≤ 64)
    (Q : Ch f e k → Prop) :
    cnt (fun u : Fin (bsRound f e k).b → Dig 256 => Q ((bsRound f e k).φ u)) ≤
      cnt Q * (bsRound f e k).w := by
  haveI : Finite (Ch f e k) := finite_Vals f _
  haveI : Fintype (Ch f e k) := Fintype.ofFinite _
  exact cnt_comp_le _ (planDraws_law f e k h).1.fib Q

theorem cnt_chal_le (d : PQ.RD) (h : d.entry.logN ≤ 64)
    (Q : Vals .two (Fmt.dsOf d.entry d.kind) → Prop) :
    cnt (fun c : (wRound d).Chal =>
      GChal.pass (b := d.entry.work) c = true ∧ Q (valsOf d c)) ≤
      cnt Q * (bsRound .two d.entry d.kind).w := by
  have h1 := GChal.cnt_pass d.entry.work
    (fun u : Fin (bsRound .two d.entry d.kind).b → Dig 256 =>
      Q ((bsRound .two d.entry d.kind).φ u))
  exact (le_of_eq h1).trans (cnt_blocks_le .two d.entry d.kind h Q)

theorem cnt_chal_inj {C' : Type} [Finite C'] (d : PQ.RD)
    (g : Vals .two (Fmt.dsOf d.entry d.kind) → C') (hg : Function.Injective g)
    (h : d.entry.logN ≤ 64) (P : C' → Prop) :
    cnt (fun c : (wRound d).Chal =>
      GChal.pass (b := d.entry.work) c = true ∧ P (g (valsOf d c))) ≤
      cnt P * (bsRound .two d.entry d.kind).w := by
  haveI : Finite (Vals .two (Fmt.dsOf d.entry d.kind)) := finite_Vals .two _
  haveI : Fintype (Vals .two (Fmt.dsOf d.entry d.kind)) := Fintype.ofFinite _
  haveI : Fintype C' := Fintype.ofFinite _
  have h1 : cnt (fun v => P (g v)) ≤ cnt P * 1 :=
    cnt_comp_le g (fun c => cnt_le_one fun a b ha hb => hg (ha.trans hb.symm)) P
  rw [Nat.mul_one] at h1
  exact (cnt_chal_le d h fun v => P (g v)).trans (Nat.mul_le_mul_right _ h1)

theorem cnt_old {C : Type} [Fintype C] : ∀ (b : ℕ) (R : C → Prop),
    cnt (fun c : GChal b C => R (GChal.old c)) = cnt R * 2 ^ b
  | 0, R => by
    rw [pow_zero, Nat.mul_one]
    rfl
  | b + 1, R => by
    have h := cnt_fst (D := Fin (b + 1) → Bool) R
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    exact h

theorem cnt_chal_all (d : PQ.RD) (h : d.entry.logN ≤ 64)
    (Q : Vals .two (Fmt.dsOf d.entry d.kind) → Prop) :
    cnt (fun c : (wRound d).Chal => Q (valsOf d c)) ≤
      cnt Q * (bsRound .two d.entry d.kind).w * 2 ^ d.entry.work := by
  have h1 := cnt_old d.entry.work
    (fun u : Fin (bsRound .two d.entry d.kind).b → Dig 256 =>
      Q ((bsRound .two d.entry d.kind).φ u))
  exact (le_of_eq h1).trans (Nat.mul_le_mul_right _ (cnt_blocks_le .two d.entry d.kind h Q))

/-- A round without bits of work: every verifier message passes its test of work. -/
theorem pass_of_zero {C : Type} : ∀ (b : ℕ), b = 0 → ∀ c : GChal b C, GChal.pass c = true
  | 0, _, _ => decide_eq_true fun i => i.elim0

/-- The round draws one element of the extension field and nothing else. -/
def OneElem (d : PQ.RD) : Prop := Fmt.dsOf d.entry d.kind = [.elem, .trits 0]

instance (d : PQ.RD) : Decidable (OneElem d) := inferInstanceAs (Decidable (_ = _))

theorem gOne_inj (ds : List Fmt.Draw) (h : ds = [.elem, .trits 0]) :
    Function.Injective (gOne ds) := by
  subst h
  intro v w hvw
  exact vals_inj [.elem, .trits 0] ⟨rfl, trivial⟩ v w (congrArg (fun x => [x]) hvw) rfl

theorem cnt_chal_one (d : PQ.RD) (h1 : OneElem d) (h : d.entry.logN ≤ 64) (P : GE → Prop) :
    cnt (fun c : (wRound d).Chal =>
      GChal.pass (b := d.entry.work) c = true ∧ P (gOne _ (valsOf d c))) ≤
      cnt P * (bsRound .two d.entry d.kind).w :=
  cnt_chal_inj d (gOne _) (gOne_inj _ h1) h P

end H2K.Fibre

#print axioms H2K.Fibre.cnt_blocks_le
#print axioms H2K.Fibre.cnt_chal_le
#print axioms H2K.Fibre.cnt_chal_inj
#print axioms H2K.Fibre.cnt_old
#print axioms H2K.Fibre.cnt_chal_all
#print axioms H2K.Fibre.pass_of_zero
#print axioms H2K.Fibre.gOne_inj
#print axioms H2K.Fibre.cnt_chal_one
