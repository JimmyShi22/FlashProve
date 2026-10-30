-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Mean.lean: the law of kind K5: the bill, cut into what the kind's own
claims pay and
what later kinds pay. General in the readers' forms.

A stage's debt (its row is worth 0; each end value's typed claim), where the slot of end value
number j is
worth the reader's form number j (what the kind's claims say), becomes: the row is worth 0, and
EndsMean:
the typed map, at the output's point, is what the reader's form is worth. EndsMean says what an
entry of a
committed table means for the message; it is no claim of this kind's, and is not shown in this file
or in what it imports.

Main names:
  `EndsMean`, `paid_iff_mean`.
  `TailLin`, `TailPaid`, `tailBill_iff`; `UnitsLin`, `UnitsPaid`, `unitsBill_iff`: the bill,
    regrouped.
  `owF_iff`: at the library's form of the letters (Cb/Pv/Att/Gaps.lean: TailG.toTail): owF holds
    exactly if
    the row of the score at the index is worth 0 and each end value's claim holds, but those that
      are the
    next sumcheck's start.

Limit: TailLin holds the letters' seven linear claims and the letter owF; at bare letters owF is
free and
cannot be unfolded.
Sources: what Att/K5Data.lean names; Cb/Pv/Att/Gaps.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.Gaps
import Johnson.Desc.First.Att.K5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- The typed map a, at the output's point, is what the reader's form number num a is worth. -/
def EndsMean {X : Type} (S : SumL K M X) (D : SumH ρ S) (a : Add S) (reader : ℕ → Aff) (W : World K) (m : M) : Prop :=
  ∀ x, S.T.map D.st (S.msg m) x (ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt) = (reader (a.num x)).value ρ W

/-- **A stage's debt, where K5's claims on its end values hold.** -/
theorem paid_iff_mean {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf) (a : Add S)
    (hv : ValsOf D a) (n : ℕ) (hn : ∀ x, a.num x < n) (hl : n ≤ H.v.length) (m : M) (mask : Nat → K)
    (entry : Nat → Nat → Nat → K) (hm : ∀ x, S.msg m (S.T.cAt x) = mask (hh.sEnd + a.num x)) (f : Aff)
    (reader : ℕ → Aff)
    (hs : ∀ j < n, (Gf.worldOf ρ mask entry).slot (hh.sEnd + j) = (reader j).value ρ (Gf.worldOf ρ mask entry)) :
    Paid S D f (Gf.worldOf ρ mask entry) m ↔
      f.value ρ (Gf.worldOf ρ mask entry) = 0 ∧ EndsMean S D a reader (Gf.worldOf ρ mask entry) m := by
  rw [paid_slots S D hD h a hv (fun x => lt_of_lt_of_le (hn x) hl) m mask entry hm f]
  refine and_congr_right' (forall_congr' fun x => ?_)
  rw [hs _ (hn x)]

/-! ## The bill, regrouped -/

/-- The tail's linear claims, and what the score at the index owes. -/
def TailLin {X : Type} {T : Tail K M X} (D : TailH ρ T) (x : X) (m : M) : Prop :=
  T.sE.L x D.dE.rd m ∧ T.sVM.L (D.x2 x) D.dVM.rd m ∧ T.sVD.L (D.x3 x) D.dVD.rd m ∧
  T.lF (D.x5 x) (Johnson.L5.Layers.rd ρ T.np D.mx) m ∧ T.sF.L (D.x6 x) D.dF.rd m ∧ T.owF (D.dF.nx (D.x6 x)) m ∧
  T.sD.L (D.x8 x) D.dD.rd m ∧ T.sH.L (D.x10 x) D.dH.rd m

/-- The five stages' debts. -/
def TailPaid {X : Type} {T : Tail K M X} (D : TailH ρ T) (l : Left) (W : World K) (m : M) : Prop :=
  Paid T.sE D.dE l.division W m ∧ Paid T.sVM D.dVM l.below W m ∧ Paid T.sVD D.dVD l.on W m ∧
  Paid T.sD D.dD l.key W m ∧ Paid T.sH D.dH l.cells W m

theorem tailBill_iff {X : Type} {T : Tail K M X} (D : TailH ρ T) (x : X) (l : Left) (W : World K) (m : M) :
    TailBill D x l W m ↔ TailLin D x m ∧ TailPaid D l W m := by
  unfold TailBill TailLin TailPaid
  tauto

def UnitsLin {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → Seen K X → M → Prop
  | [], _, _, _ => True
  | u :: us, d, s, m => u.L s d.1.rd m ∧ UnitsLin us d.2 (s.1, s.2 ++ [List.ofFn d.1.rd]) m

def UnitsPaid {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → List Aff → World K → M → Prop
  | [], _, [], _, _ => True
  | u :: us, d, f :: fs, W, m => Paid u d.1 f W m ∧ UnitsPaid us d.2 fs W m
  | _, _, _, _, _ => False

theorem unitsBill_iff {X : Type} {W : World K} {m : M} : ∀ (us : List (SumL K M (Seen K X))) (d : UnitsH ρ us)
    (s : Seen K X) (fs : List Aff), UnitsBill us d s fs W m ↔ UnitsLin us d s m ∧ UnitsPaid us d fs W m
  | [], _, _, [] => by simp [UnitsBill, UnitsLin, UnitsPaid]
  | [], _, _, _ :: _ => by simp [UnitsBill, UnitsPaid]
  | _ :: _, _, _, [] => by simp [UnitsBill, UnitsPaid]
  | u :: us, d, s, f :: fs => by
    have ih := unitsBill_iff (W := W) (m := m) us d.2 (s.1, s.2 ++ [List.ofFn d.1.rd]) fs
    simp only [UnitsBill, UnitsLin, UnitsPaid, ih]
    tauto

/-- **What the score at the index owes, at the library's form of the letters.** -/
theorem owF_iff (law : MaskedSum.PartRowLaw) {X : Type} (TG : TailG K M X) (D : SumH ρ TG.toTail.sF) {C : Aff}
    {st : Stage} {riders : List E} {H : PscH} {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP TG.toTail.sF st)
    (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf) {W : World K} {m : M} {f : Aff}
    (p : RowPrem TG.toTail.sF D C hh f W m)
    (x : ((TG.toTail.sVD.Nx × (Fin TG.toTail.nz → K)) × (Fin TG.toTail.np → K)) × K) :
    TG.toTail.owF (D.nx x) m ↔ f.value ρ W = 0 ∧
      ∀ a, (∀ i, a ≠ TG.iB i) → TG.toTail.sF.T.our.par.EHolds D.out (TG.toTail.sF.msg m) a := by
  obtain ⟨S0, e, D1, D2, D4⟩ := p
  subst e
  exact and_congr_left' (row_uholds law TG.toTail.sF D hs hD h W S0 m D1 D2 D4).symm

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.owF_iff
#print axioms VerifiableInference.Desc.First.Att.P.paid_iff_mean
#print axioms VerifiableInference.Desc.First.Att.P.tailBill_iff
#print axioms VerifiableInference.Desc.First.Att.P.unitsBill_iff
