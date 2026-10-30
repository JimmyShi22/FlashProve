-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SmpReads.lean: WHAT THE SAMPLE's READER MAY READ OF THE RECORD, SO THAT IT
GIVES THE SAME OVER A STEP OF KIND K13's BLOCK. One definition and statements with their proofs. It
names no table of joints.
Why. The table's letters "no collision" and "pin" are filled by other files over a letter smp: a
member's sample, read off the pair of the public part and the chain's record
(Johnson/Desc/Sound/MeaningSig.lean). The reading that is meant
(`smpOf forms ans`, Johnson/Desc/Sound/Seed.lean) reads the member's sample ROWS, as linear forms:
every coefficient. SO IT IS NO FUNCTION OF `smpSeed` (Johnson/Desc/SmpRows.lean), which picks a few
coefficients of the first row: a premise "one `smpSeed`, one smp" is false of it at records whose
first row differs elsewhere.
  `SmpReads smp`: THE PREMISE ON smp: of the pair it reads no more than: the public part; the book;
    the code table; of each oracle message its shape, its mark "sampled", its sample rows and its
    pad (`SameAll`, Johnson/Desc/K13/Law/PinDec.lean).
  `smpReads_of_form`: ITS MEMBERS: every smp that is made of a function of just these.
  `smp_same_M3`: **over a step of kind K13's block such an smp gives the same**, at every member.
What is not claimed. That the filling of record lays an smp of that form. Nothing at W's commitment,
which sends a message: there the form by tenant is wanted. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Sending Mem)

section
variable {Pp : Type} {cs : Codes}

/-- **The premise on smp**: what it may read of the pair. -/
def SmpReads
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) :
    Prop :=
  ∀ (x x' : Pp × S) (m : Mem), x'.1 = x.1 → x'.2.book = x.2.book → SameAll x.2.st x'.2.st →
    smp x' m.1 m.2 = smp x m.1 m.2

/-- Its members: every smp that is made of a function of the public part, the book, the code table
and each message's shape, mark, sample rows and pad. -/
theorem smpReads_of_form
    (f : Pp → TreeBook → Codes →
      (ℕ → Option (OracleShape × Bool × Array OnBytes.Row × List (OnBytes.Part × ℕ))) →
      (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) :
    SmpReads (cs := cs) fun (a : Pp × S) s i =>
      f a.1 a.2.book a.2.st.codes (fun o => sampleOf a.2.st o) s i := by
  intro x x' m e1 e2 e3
  have e4 : (fun o => sampleOf x'.2.st o) = fun o => sampleOf x.2.st o := funext e3.2
  show f x'.1 x'.2.book x'.2.st.codes (fun o => sampleOf x'.2.st o) m.1 m.2 =
    f x.1 x.2.book x.2.st.codes (fun o => sampleOf x.2.st o) m.1 m.2
  rw [e1, e2, e3.1, e4]

/-- **Over a step of kind K13's block such an smp gives the same.** -/
theorem smp_same_M3 {Cl : Type} {P : Where}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    (h : SmpReads smp) {x x' : Pp × S} (hs : StepM3 Cl P x x') (m : Mem) :
    smp x' m.1 m.2 = smp x m.1 m.2 := by
  obtain ⟨rs, gs, hd⟩ := hs.2
  obtain ⟨_, _, _, _, e⟩ := atM3_rec hd
  exact h x x' m hs.1 (by rw [e]) (atM3_same hd)

end

end VerifiableInference.Desc.K13.Law
