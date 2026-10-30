-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/M3K.lean: the law of the batching's joined block, typed at the plan's own
number of column variables: so that it meets the law of the block behind W's commitment without a
cast. A statement with its proof.
Main name: `atM3_goodIn_k`, and at k := P.lin.kCol `atM3_goodIn_plan`.
Used of `verify-on-bytes`: nothing beside what Johnson/Desc/K13/Law/Good.lean names.

What is not claimed. What Johnson/Desc/K13/Law/Good.lean and Johnson/Desc/K13/Law/M3Fits.lean say is
not claimed. At a reader that takes all mask entries from one world the premise on the pin cannot be
met by a real run (it fixes a value at every mask entry of every message, and messages are sent
behind these draws): there the law is true and idle. The law to carry on is that of
Johnson/Desc/K13/Law/Good2.lean. `Declared` is a test on a plan's written rounds: an evaluation at
two stored sets' public files, a small and a full-size one, said yes, and five controls said no;
no theorem says it of a plan. `Local` asks only that the decoder reads the stored table and the
earlier trees: every such function meets it. A decoder that reads the oracles alone singles out one
member of a list whatever the samples in the record say: so the laws at such a decoder are idle for
the witness that the samples pin. The form to carry on is that of Johnson/Desc/K13/Law/PinA.lean.

-/
import Johnson.Desc.K13.Law.M3Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Maker (RDT)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- The law at any number k that is the number of the variables' written rounds. -/
theorem atM3_goodIn_k (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (k : ℕ) (hk : ds.length = k) (rw : W → Wit GE nR k)
    (dec : F.E.Str → Wit GE nR k) (hloc : Local base dec) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun _ => True) (FrontOk P)
      (RowsHold rw (pinOf rw dec)) (RowsHold rw (pinOf rw dec)) := by
  subst hk
  exact atM3_goodIn_front F P base dZ d0 ds hD rw dec hloc

/-- **The law at the plan's own number of column variables.** -/
theorem atM3_goodIn_plan (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (rw : W → Wit GE nR P.lin.kCol)
    (dec : F.E.Str → Wit GE nR P.lin.kCol) (hloc : Local base dec) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun _ => True) (FrontOk P)
      (RowsHold rw (pinOf rw dec)) (RowsHold rw (pinOf rw dec)) :=
  atM3_goodIn_k F P base dZ d0 ds hD P.lin.kCol hD.len.symm rw dec hloc

end VerifiableInference.Desc.K13.Law
