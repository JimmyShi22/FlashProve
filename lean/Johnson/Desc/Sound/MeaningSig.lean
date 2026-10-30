-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MeaningSig.lean: THE LETTERS OF THE TABLE OF JOINTS ON THE READING OF THE
ORACLES, FILLED BY THE LIBRARY's OWN NOTIONS, by tree and tenant. Definitions, and two small lemmas.

The table of joints (Johnson/Desc/First/Borders.lean: `Meaning`) speaks of a tenant t of a tree j,
over the chain's record, plain strings and a witness. MsgSig.lean, World.lean and WordsLaw.lean
speak of a member of a sending. Here the one is said by the other: a tenant is the member that sits
at that seat.
  THE SECOND READING (`smp`) is meant as `smpOf forms ans` (Seed.lean): the seed under its own
  "there is", tied to the record by the rows.
  `SitsAt x j t`: the member x sits at tenant t of tree j.
  `pinJT` · `noCollJT` · `shownJT` · `pinWOf` · `decodesOf`: five letters.
    THERE IS A MEMBER AT THE SEAT stands in pinJT and shownJT: at a seat where nobody sits
    they are false, not free. noCollJT is `CfAt` at the members that sit there: THAT THE RECORD
    HOLDS THE SAMPLE STANDS IN IT, as a proposition. A sixth letter, `held`, is a test with code
    for a run and lies in the plain storey (`smpHeld`, SmpRows.lean): NO PROOF GETS ANYTHING OF IT.
  `pinAt_one` (proved): A PIN IS FUNCTIONAL: two witnesses that are pinned at one member, at one
    statement, name one message there. `longOf_eq` (proved): SeatRun.lean's plain `longOf` is the
    library's `aOf`.
Limits. `smp` (so `forms`, `ans`), `decT`, the sendings and `arr` are letters still: functions of
the plan and of the record.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsLaw
import Johnson.Desc.Sound.Seed
import Johnson.Desc.SeatRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice

section
variable (cs : OnBytes.Codes)

variable {A : Type}

variable {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- The member x sits at tenant t of tree j. -/
def SitsAt (x : Mem) (j t : ℕ) : Prop := x.1.seat x.2 = (j, t)

/-- **pin**: a member of ms sits there, and every member of ms that sits there is pinned. -/
def pinJT (ms : List Mem) (j t : ℕ) (a : A) (y : Strs) (w : Wit Cells Tok MsgT) : Prop :=
  (∃ x ∈ ms, SitsAt x j t) ∧
    ∀ x ∈ ms, SitsAt x j t → PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w

/-- **A PIN IS FUNCTIONAL**: two witnesses that are pinned at one member, at one statement, name one
message there: the library's decoder is a function of the word and the sample. (No promise is needed
for that. The promise, no collision, is what makes the decoder's value THE candidate: the library's
`sig_dec_good`.) -/
theorem pinAt_one (x : Mem) (a : A) (y : Strs) (w w' : Wit Cells Tok MsgT)
    (h : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w)
    (h' : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w') :
    msgsOf cs x.1.l x.1.seat arr w x.2 = msgsOf cs x.1.l x.1.seat arr w' x.2 := by
  obtain ⟨z, hz, -, hd⟩ := h
  obtain ⟨z', hz', -, hd'⟩ := h'
  have e : z' = z := Option.some.inj (hz'.symm.trans hz)
  subst e
  exact Option.some.inj (hd.symm.trans hd')

/-- The plain twin of the library's log-length of a shape's code as read is that. -/
theorem longOf_eq (s : OnBytes.OracleShape) : longOf cs s = aOf cs s := rfl

/-- **noColl**: the promise: at every member of ms that sits there `CfAt`: THE RECORD HOLDS ITS
SAMPLE (so the promise is not free where it does not), every leaf is shown, and no two members of
the word's list have one answer at the seed. At smp := `smpOf forms ans` (Seed.lean) that is
`cfAt_iff`'s right side. -/
def noCollJT (ms : List Mem) (j t : ℕ) (a : A) (y : Strs) : Prop :=
  ∀ x ∈ ms, SitsAt x j t → CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a y

/-- **shown**: the promise: a member of ms sits there, and every leaf shows its symbol. -/
def shownJT (ms : List Mem) (j t : ℕ) (y : Strs) : Prop :=
  (∃ x ∈ ms, SitsAt x j t) ∧ ∀ x ∈ ms, SitsAt x j t → ShownAt G cs x.1.l x.1.seat y x.2

variable (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells)

/-- **pinW**: the witness's cells are what the stored table decodes to, with the record. -/
def pinWOf (a : A) (y : Strs) (w : Wit Cells Tok MsgT) : Prop := decT y.cell a = some w.cells

/-- **decodes**: the promise: the stored table decodes with the record. -/
def decodesOf (a : A) (y : Strs) : Prop := (decT y.cell a).isSome = true

end

end VerifiableInference.Desc.Sound
