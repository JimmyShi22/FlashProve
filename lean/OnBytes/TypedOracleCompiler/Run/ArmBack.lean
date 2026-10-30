-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmBack.lean: the total code behind the escape over a second interface L2, which the
encoding of OnBytes/TypedOracleCompiler/Run/ArmDirect.lean takes as a letter (`back`).

A page writes whatever the format does not write behind an escape byte, by a total one-to-one code
of all typed points with a parser. `backP` (OnBytes/TypedOracleCompiler/Run/SerThin.lean) makes such a code over ANY
interface from three serialisers (`SerP`): of an instance, of a leaf's body, and of a plain part of
some round for each of the three tags. So nothing has to be cut out of the entry's own code
(`backE`, OnBytes/TypedOracleCompiler/Run/PageEBack.lean, which is `backP` at that interface's serialisers). Here
`backP` is said at L2, and the serialisers are made from those of an entry's interface where the
types correspond.

Main definitions.
 `backL2 L2 sx sb pb K`   `backP` at L2, from the three serialisers as letters.
 `serAlong`       the serialisers over L2: the body's and the link's plain parts' are those of the
                  entry's interface (`serTie B sg sb`; `pbE … .link`), carried along the two
                  one-to-one correspondences bd and pbF of OnBytes/TypedOracleCompiler/Run/ArmRounds.lean; the
                  instance's and the other two tags' plain parts' stay letters.
 `backAlong`      `backP` at these.

Not claimed. What the strings behind the escape are. For an encoding to be one to one, any total
one-to-one code serves; but the answer that an encoding reads out of an oracle at a query that is
written behind the escape hangs on this code, and of such answers nothing is said here or in
OnBytes/TypedOracleCompiler/Run/ArmRounds.lean. That a leaf query on a stored symbol is written behind the escape as
another page writes it (OnBytes/TypedOracleCompiler/Run/SerTie.lean). Serialisers of X2 and of the plain parts under
the other two tags are given at no L2. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.PageEBack

set_option autoImplicit false

namespace TypedOracleCompiler.Run.ArmBack
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageEBack
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)

/-- **The total code behind the escape over L2**, from serialisers of an instance, of a body and of
a plain part for each tag. -/
def backL2 (sx : Ser X2) (sb : Ser L2.Bd)
    (pb : ∀ t : Tag, Ser (PlainPart (shapeOf L2 t) (annOf L2 t))) (K : ℕ) : StrCode (AllPts 256 K L2) :=
  backP (fun _ : Unit => L2) ⟨sx, sb, pb⟩ K

variable {X Bd : Type} (D : TypedOracleCompiler.Run.PQ.XD) (early : X → X) (e : _root_.Fmt.Entry)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (LE (Bd := Bd) D early e) .link) (annOf (LE (Bd := Bd) D early e) .link))
  (bd : L2.Bd ≃ Bd)

/-- The serialisers over L2, from those of the entry's interface where the types correspond. -/
def serAlong (sx : Ser X2) (B : TypedOracleCompiler.Run.PQ.BodyD Bd) (sg : Ser SgX) (sb : Ser Bd)
    (pT : Ser (PlainPart (shapeOf L2 .test) (annOf L2 .test)))
    (pO : Ser (PlainPart (shapeOf L2 .onl) (annOf L2 .onl))) : SerP (fun _ : Unit => L2) where
  x := sx
  bd := Ser.ofEquiv bd (TypedOracleCompiler.Run.PQ.serTie B sg sb)
  pb := fun t => match t with
    | .link => Ser.ofEquiv pbF (pbE (Bd := Bd) D early e .link)
    | .test => pT
    | .onl => pO

/-- **The total code behind the escape over L2, at these.** -/
def backAlong (sx : Ser X2) (B : TypedOracleCompiler.Run.PQ.BodyD Bd) (sg : Ser SgX) (sb : Ser Bd)
    (pT : Ser (PlainPart (shapeOf L2 .test) (annOf L2 .test)))
    (pO : Ser (PlainPart (shapeOf L2 .onl) (annOf L2 .onl))) (K : ℕ) : StrCode (AllPts 256 K L2) :=
  backP (fun _ : Unit => L2) (serAlong L2 D early e pbF bd sx B sg sb pT pO) K

end TypedOracleCompiler.Run.ArmBack
