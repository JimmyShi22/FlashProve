-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5AttDef.lean

"The attention link is in order", said of the integer matrices of the verifier's own list for an
attention sub-proof, for every shape of that sub-proof. Definitions alone.

The verifier's attention sub-proof has a list of matrices (OnBytes/Model/AttentionPlan.lean:
matrices): the NAs parts of "as", then ah, ao, bA and qa. The library has a relation on the cells of
an attention segment, for all sizes: Inst.Model.AttSeg.RFraw (Inst/Model/Att/Trace.lean): every cell
is below 2^18, every key of the four calls is an entry of its table, the three kinds of identities
are 0. This file reads that relation at the verifier's matrices.

Every letter of the relation is made from a record S of the type of the verifier's shapes
(OnBytes/Model/AttentionShape.lean). S IS ANY RECORD: that it is what the verifier's function shape
returns is a hypothesis of whoever uses these definitions (what shape returns:
Johnson/Road/Lane5AttShape.lean, Johnson/Road/Lane5AttPlan.lean).
* "dimOf S": the sizes.
* "sclOf S": the table of scales. The relation reads one word of it: the shift of the segment's
  first layer.
* "tbOf S": the table functions. The relation reads Exp alone, at the rows below S.u0.
* "addrA S", "cellsA S Z": where the cell of a name stands in the verifier's matrices, and the cell.
  The rule is the verifier's, as its forms read the tables of these matrices
  (OnBytes/Model/AttentionClaimsA.lean: plane, shV, xl with Model.tenCell;
  OnBytes/Model/AttentionClaimsB.lean: atRh, atRhp) and as the heads of
  OnBytes/Model/AttentionHeard.lean and OnBytes/Model/AttentionTables.lean say in words where an
  entry of a table lies in its matrix. It is written here by a reading of these texts: that it is
  the program's rule is shown by no theorem. What is proved of it, for every shape that shape
  returns: it gives each cell the library's own number (Johnson/Road/Lane5AttNum.lean) and, where 0
  < cf.NAs, is one-to-one on the valid names (Johnson/Road/Lane5AttInj.lean).
* "AttOrd S Z": the link is in order at Z: the relation, and nothing else.
* "AttFit S": two public conditions on the shape (below).

The library has one shift for a segment, the verifier one for each layer: "OneShift". The library's
bound on a score is the constant 128 * 2047^2, the verifier's is dh * 2047^2; the library's tables
have 2^16 rows, the verifier's table of exponentials 2^kFD. So the relation can be what the
verifier's calls and claims are there to show only at a shape with one shift, ldh = 7 and kFD = 16.
AttFit holds the first two. The third is not asked here: it is a hypothesis where the tables are
compared (Johnson/Road/Lane5AttTabs.lean, whose head says what the verifier's own test af-policy-kF
admits).

The names sclOf and dimOf also stand in the namespace OnBytes.Road, for the layers' files
(Johnson/Road/FormsKeysFits.lean). Inside OnBytes.Road.L5 they mean the definitions of this file.

Not claimed: that a proof file which a verifier accepts has such matrices; that the rule of
addresses is the program's. The program does not import this file.

Files named above that a package may lack. OnBytes/Model/AttentionPlan.lean,
OnBytes/Model/AttentionTables.lean, Johnson/Road/Lane5AttShape.lean, Johnson/Road/Lane5AttPlan.lean,
Johnson/Road/Lane5AttNum.lean, Johnson/Road/Lane5AttInj.lean, Johnson/Road/Lane5AttTabs.lean and
Johnson/Road/FormsKeysFits.lean are in the library's full tree and are not imported by this file; a
package that is cut to what its front theorems need may not hold them. Where they lack, what this
comment says of them cannot be checked there.

-/
import OnBytes.Model.AttentionClaimsB
import Inst.Model.Att.Trace
import Cb.Gl.GlField

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

/-- The integer matrices of one link's list: number in the list, row, column. -/
abbrev Zs : Type := ℕ → ℕ → ℕ → ℤ

/-- **The library's sizes of an attention segment, from the verifier's shape.** -/
def dimOf (S : Attention.Shape) : Inst.Model.AttSeg.Dim :=
  ⟨S.cf.lgk, S.lnT - 1, S.cf.lB, S.cf.ldh, S.HA, S.Lam, S.u0⟩

/-- The words of layer l of the group: its shift and the length of the table of exponentials. The
other words are 0: an attention segment reads none of them. -/
def wordOf (S : Attention.Shape) (l : ℕ) : Inst.Model.LayerScale :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, (S.u0 : ℤ), S.cf.sh.getD l 0⟩

/-- The table of scales of the segment, from the verifier's shape. -/
@[reducible] def sclOf (S : Attention.Shape) : Inst.Model.Scl := ⟨wordOf S, ⟨0, 0, 0⟩⟩

/-- The table functions, from the verifier's shape: Exp is the verifier's table of exponentials. The
others are 0: an attention segment reads none of them. -/
def tbOf (S : Attention.Shape) : Inst.Model.Tables :=
  ⟨fun _ => 0, fun _ => 0, fun t => ((S.Tt.getD t.toNat 0 : ℕ) : ℤ), fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- Cell number n of the matrix "as": number in the list, row, column. "Cell number n of as is row
n mod 2^lmS of column n / 2^lmS, and column c is in part c / (kAs / NAs)". -/
def asCell (S : Attention.Shape) (n : ℕ) : ℕ × ℕ × ℕ :=
  (n / 2 ^ S.cf.lmS / (S.kAs / S.cf.NAs), n % 2 ^ S.cf.lmS, n / 2 ^ S.cf.lmS % (S.kAs / S.cf.NAs))

/-- Feature φ at token i, in matrix number a of the list, which has wc features in a column. -/
def featCell (S : Attention.Shape) (a wc φ i : ℕ) : ℕ × ℕ × ℕ := (a, φ % wc * S.T + i, φ / wc)

/-- **Where the cell of a name stands in the verifier's list**: number in the list, row, column.
Pair number b is the layer b / HA and the query head b % HA among those of its head of keys and
values. -/
def addrA (S : Attention.Shape) : Inst.Model.AttSeg.Raw → ℕ × ℕ × ℕ
  | .c .M jj b x =>
    asCell S (((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nM + x)
  | .c .D jj b x =>
    asCell S (5 * S.Lam * S.HA * 2 ^ S.nM +
      ((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nD + x)
  | .mx k b g i =>
    featCell S S.cf.NAs S.cf.wcH
      (S.oMr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b % S.HA)) i
  | .den k b g i =>
    featCell S S.cf.NAs S.cf.wcH
      (S.oZr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b % S.HA)) i
  | .ib k b g i =>
    featCell S S.cf.NAs S.cf.wcH
      (S.oIb + (0 * S.Lam + b / S.HA) * (S.cf.lt * S.cf.H) + (k * S.cf.H + g * S.HA + b % S.HA)) i
  | .qh b g i n =>
    featCell S (S.cf.NAs + 1) S.cf.wcO
      (Model.tenCell (Attention.atRh S) 0 (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + n) i
  | .qh' b g i n =>
    featCell S (S.cf.NAs + 1) S.cf.wcO
      (Model.tenCell (Attention.atRhp S) 0 (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + n) i
  | .qry k b g i n =>
    featCell S (S.cf.NAs + 3) S.cf.wcQ
      (Model.tenCell S.atQ k (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + n) i
  | .out k b g i n =>
    featCell S (S.cf.NAs + 3) S.cf.wcQ
      (Model.tenCell S.atO k (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + n) i
  | .key k lam g j n =>
    featCell S (S.cf.NAs + 3) S.cf.wcQ (Model.tenCell S.atK k lam (g * S.dh) + n) j
  | .val k lam g j n =>
    featCell S (S.cf.NAs + 3) S.cf.wcQ (Model.tenCell S.atV k lam (g * S.dh) + n) j

/-- The matrices of a list at (number, row, column). -/
def zAt (Z : Zs) (a : ℕ × ℕ × ℕ) : ℤ := Z a.1 a.2.1 a.2.2

/-- **The cells of the attention segment, read in the verifier's matrices.** -/
def cellsA (S : Attention.Shape) (Z : Zs) : Inst.Model.AttSeg.Raw → ℤ := fun c => zAt Z (addrA S c)

/-- All layers of the group have one shift. -/
def OneShift (S : Attention.Shape) : Prop := ∀ l < S.Lam, S.cf.sh.getD l 0 = S.cf.sh.getD 0 0

/-- **The shapes at which the library's relation can be what the verifier's calls and claims are
there to show**: the group has one shift, and a head has 128 features. Public. -/
structure AttFit (S : Attention.Shape) : Prop where
  one : OneShift S
  ldh : S.cf.ldh = 7

/-- **The attention link is in order** at the integer matrices Z of its list: the library's relation
of an attention segment holds of the cells, modulo the protocol's prime, at the sizes, the shift of
the group's first layer and the table of exponentials of the verifier's shape. A statement on the
integer matrices Z; the shape is public. A record with one field, so that no step compares two such
statements by unfolding the relation. -/
structure AttOrd (S : Attention.Shape) (Z : Zs) : Prop where
  rel : Inst.Model.AttSeg.RFraw (scl := sclOf S) (dimOf S) (tbOf S) Cb.Gl.F (cellsA S Z)

end OnBytes.Road.L5
