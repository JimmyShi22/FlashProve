-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/FirstRows.lean: the first stage of a proximity test on a group of sent oracle
messages, as a value of the data of a test, and the whole test on that group.

The group and its shape are those of Johnson/Top/H/GroupRows.lean. The first fold stands on a
super-row of one base row (`GShape.par`, Cb/Ld/LdGroupFold.lean), so the names of what it hands on
differ from those of a later stage by an idle component. The code switch behind it is that of
OnBytes/Slice/CsData.lean under the renaming that drops this component. The data of a test are
`TowR`, the test on a group is `testRide` (Cb/Pv/Tower/Test.lean). Definitions, statements and
proofs.
Main names:
  `oneRow X`: a pair of the one name of a base row and x is x.
  `kap s`, `rowMap t`, `rowMap_inj`: the renaming of the folded rows' entries and tails; of the
    rows that the switch batches; it is injective.
  `Rows.sw R Sb sl Z hf`: the switch from the group's stage to the stage s', behind the first
    fold.
  `Rows.sw_hypK`, `Rows.sw_reads`: its conditions, and what locality asks.
  `Rows.step`, `Rows.step_hypK`, `Rows.step_reads`: the first stage, then a remainder; the
    conditions of the whole from those of the remainder, `Rows.Good`, `InJ` and `CountsAt`.
  `Rows.test`, `Rows.test_know`: the arrangement and the whole test on the group; it is knowledge
    sound under the conditions of its blocks and `Rows.Good`.
Limits: the limits of Johnson/Top/H/GroupRows.lean and Johnson/Top/H/StageValues.lean hold here. A
first stage whose switch bears the masking word of the last step is not laid. `CountsAt` is asked
and not proved here.

-/
import Johnson.Top.H.GroupRows
import Johnson.Top.H.StageValues
import OnBytes.Slice.SampleOK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Cb.Pv.Tower

/-- A pair of the one name of a base row and x is x. -/
def oneRow (X : Type) : Option Empty × X ≃ X where
  toFun := Prod.snd
  invFun := fun x => (none, x)
  left_inv := fun p => by
    obtain ⟨o, x⟩ := p
    cases o with
    | none => rfl
    | some e => exact e.elim
  right_inv := fun _ => rfl

/-- The entries and tails of the three folded rows, the idle component dropped. -/
def kap (s : Sg) :
    (((Option Empty × s.cM.J) ⊕ (s.cZ.J ⊕ s.cZ.J)) ⊕
      ((Option Empty × s.cM.Q) ⊕ (s.cZ.Q ⊕ s.cZ.Q))) ≃ CsK s :=
  Equiv.sumCongr (Equiv.sumCongr (oneRow _) (Equiv.refl _))
    (Equiv.sumCongr (oneRow _) (Equiv.refl _))

/-- The rows that the switch batches, the idle component dropped. -/
def rowMap (t : ℕ) :
    LdRow Unit t ((Option Empty × Unit) ⊕ (Unit ⊕ Unit)) → LdRow Unit t (Unit ⊕ (Unit ⊕ Unit)) :=
  Sum.map id (Sum.map id (Prod.map id (Sum.map Prod.snd id)))

theorem rowMap_inj (t : ℕ) : Function.Injective (rowMap t) :=
  Function.Injective.sumMap Function.injective_id
    (Function.Injective.sumMap Function.injective_id
      (Function.Injective.prodMap Function.injective_id
        (Function.Injective.sumMap (oneRow Unit).injective Function.injective_id)))

namespace Rows
variable {S : Sig GE} (R : Rows S) {s' : Sg} {B : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))

/-- The switch from the group's stage to s', behind the first fold. -/
noncomputable def sw (hf : CsFit R.s s') : LdSwD (R.Sh.fold Sb sl Z) s'.Ps where
  finAa := inferInstanceAs (Fintype ((Option Empty × Unit) ⊕ (Unit ⊕ Unit)))
  Cnew := s'.cIn
  Qo := CsFree hf
  finQo := Fintype.ofFinite _
  decQo := Classical.decEq _
  place := (Equiv.sumCongr (kap R.s) (Equiv.refl _)).trans (csPlace hf)
  Zo := reix (csSample hf) (Equiv.sumCongr (kap R.s) (Equiv.refl _))
  ts := R.s.t
  Zb := (Evader.powers GE (2 + 3 * R.s.t)).comap (csRowNo R.s ∘ rowMap R.s.t)

theorem sw_hypK (hf : CsFit R.s s') (e : ℕ) (hs : R.s.Sized) (hs' : s'.Sized) {e' : ℕ}
    (hj : InJ s' e') : ((R.sw Sb sl Z hf).D e).HypK e' (lstJ s' e') := by
  letI : Fintype (CsFree hf) := Fintype.ofFinite _
  exact LdSw.HypK.mk
    ((((Sg.fit_cM hs).il (Option Empty)).pair ((Sg.fit_cZ hs).pair (Sg.fit_cZ hs))).laws)
    (listJ_of (Sg.fit_cIn hs') hj)
    (ok_reix (csSample hf) (Equiv.sumCongr (kap R.s) (Equiv.refl _)) (csSample_ok hf))
    (ok_powers_comap _ _ ((csRowNo_inj R.s).comp (rowMap_inj R.s.t)))

theorem sw_reads (hf : CsFit R.s s') (e : ℕ) (hs' : s'.Sized) :
    ((R.sw Sb sl Z hf).D e).Cout.Reads := (Sg.fit_cIn hs').laws.loc

/-- The first stage, then the remainder. -/
noncomputable def step (hf : CsFit R.s s') (e' bC bZ : ℕ)
    (rest : TowR (((R.sw Sb sl Z hf).D R.G.e).jOut e') (s'.par s'.Z.l).Cw.nat) :
    TowR (wholeJ R.Sh.par (R.Sh.form Sb sl Z) R.G.e) R.Sh.par.Cw.nat :=
  TowR.step R.Sh.par (R.Sh.form Sb sl Z) R.G.e (1, 1) (R.sw Sb sl Z hf) (s'.par s'.Z.l).Cw s'.Ps
    (Sum.elim id id) id R.s.d (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ)
    e' (lstJ s' e') rest

theorem step_hypK (hf : CsFit R.s s') {e' bC bZ : ℕ}
    (rest : TowR (((R.sw Sb sl Z hf).D R.G.e).jOut e') (s'.par s'.Z.l).Cw.nat)
    (h : R.Good) (hs' : s'.Sized) (hj : InJ R.s R.e) (hj' : InJ s' e')
    (hc : CountsAt R.s R.e bC bZ) (hr : rest.HypK) :
    (R.step Sb sl Z hf e' bC bZ rest).HypK :=
  And.intro (R.hypK Sb sl Z h hj hc) (And.intro (R.sw_hypK Sb sl Z hf _ h.sized hs' hj') hr)

theorem step_reads (hf : CsFit R.s s') (e' bC bZ : ℕ)
    (rest : TowR (((R.sw Sb sl Z hf).D R.G.e).jOut e') (s'.par s'.Z.l).Cw.nat)
    (hs' : s'.Sized) (hr : rest.Reads) : (R.step Sb sl Z hf e' bC bZ rest).Reads :=
  And.intro (R.sw_reads Sb sl Z hf _ hs') hr

/-- The arrangement and the whole test on the group. -/
noncomputable def test (T : TowR (wholeJ R.Sh.par (R.Sh.form Sb sl Z) R.G.e) R.Sh.par.Cw.nat) :
    EndR (R.G.joint Sb sl Z) R.Sh.par.Cw.nat :=
  testRide R.Sh Sb sl Z T

theorem test_know (T : TowR (wholeJ R.Sh.par (R.Sh.form Sb sl Z) R.G.e) R.Sh.par.Cw.nat)
    (h : R.Good) (hT : T.HypK) : (R.test Sb sl Z T).Know :=
  testRide_know R.Sh Sb sl Z T (R.sh_ok h) hT

end Rows

end Johnson.Top.H

#print axioms Johnson.Top.H.Rows.sw_hypK
#print axioms Johnson.Top.H.Rows.step_hypK
#print axioms Johnson.Top.H.Rows.test_know
