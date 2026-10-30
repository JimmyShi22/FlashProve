-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Key.lean: the kind "lookup" (Johnson/Desc/First/Look/K3LookupGeneral.lean) AT A
KEY FILE: its numbers out of the lookup's public record there, and the public table that says which
oracle message's which mask entry a hidden value is. Definitions with code. No theorem.

Main names:
  `faceOfLkp S`: the face of a lookup with the public record S (`Lkp.Public`,
    OnBytes/Iop/Lkp.lean:96-128).
  `fromKeys f`: for each hidden value, in the order of sending: whether it is one of the two end
    values of a part's last key level, whose mask entries lie in another message than the rest
    (`Lkp.fresh`, OnBytes/Iop/Lkp.lean:517-525).
  `homes f own key`: the hidden values' mask entries, out of the two messages' next free entries.
  `maskSide F home a`: a form over hidden values as a linear form in mask entries and a public
    value: the sum of c_j mf_j mask_j, and the constant plus the sum of c_j vp_j, where the hidden
    value under slot j is vp_j - mf_j mask_j (OnBytes/Model/Hide.lean:167-176).
  `rowOfAff`, `rowOfPlane`, `groupRows`: the claims as rows of the lookup's group, IN THE PROGRAM'S
    ORDER AND UNDER ITS SIGNS: a claim is "form = 0", a row "coefficients = target": the program's
    rows are ours with every sign turned, but for the row on the bits' value. `keyClaims`: the
    claims on the parts' keys, by the program's `keysOf`: for the caller's run.

Limits: those of K3LookupGeneral.lean. Nothing says that these are what `Lkp.run` computes.
`homes` takes the two lists of free entries from its caller.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3LookupGeneral
import OnBytes.Iop.Lkp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Fork Aff)

/-- The face of a lookup with the public record S. A part's last key level binds the named variables
first; every other level goes from the highest variable down. -/
def faceOfLkp (S : Lkp.Public) : Face :=
  { shifted := S.shifted, mu := S.mu, planes := S.planes, parts := S.parts, d := S.d
    orders := fun i m =>
      if m + 1 == S.parts.getD i 0 then Lkp.orderBeginning S.lastKeyLevelOrder m
      else Lkp.defaultOrder m
    padding := (Lkp.paddingList S).map fun p => (p.1, fun theta => Lkp.rowAt S theta p.2)
    leaf := fun theta alpha zb0 => Lkp.leavesFactor S theta alpha zb0.toList.reverse }

/-- n times no. -/
def own (n : Nat) : List Bool := List.replicate n false

/-- For each hidden value, in the order of sending: whether its mask entry lies in the second
message. -/
def fromKeys (f : Face) : List Bool :=
  own (7 + 6 * (f.planes - 2) + 5 * (f.parts.length - 1)) ++
    (f.parts.flatMap fun v => (List.range v).flatMap fun k =>
      if k + 1 == v then own (2 * k + 3) ++ [true, true] else own (2 * k + 5)) ++
    own (((List.range f.d).map fun l => 2 * (f.mu + l) + 5).sum +
      (1 + f.mu + 2 * f.d) + (1 + 2 * (f.mu + f.d) + 2 + 1))

/-- The hidden values' mask entries. o, k: the next free entries of the first and of the second
message. -/
def homesFrom : List Bool → List Slot → List Slot → List Slot
  | false :: bs, s :: o, k => s :: homesFrom bs o k
  | true :: bs, o, s :: k => s :: homesFrom bs o k
  | _, _, _ => []

def homes (f : Face) (o k : List Slot) : Array Slot := (homesFrom (fromKeys f) o k).toArray

/-- A form over hidden values as a linear form in mask entries, and a public value. Nothing where
the form names an entry of a virtual row, a slot without a home, or a slot that is still free. -/
def maskSide (F : Fork) (home : Array Slot) (a : Aff) : Option (MaskForm × E) :=
  if !a.ents.isEmpty then none
  else
    a.slots.foldlM (fun (x : MaskForm × E) (t : Nat × E) =>
      match home[t.1]?, F.shown t.1 with
      | some s, some v => some (x.1 ++ [(s, mulE t.2 (F.mf.getD t.1 zeroE))], addE x.2 (mulE t.2 v))
      | _, _ => none) ([], a.const)

/-! ## The claims as rows of the group, in the program's order and under its signs -/

/-- A row of a group, as the verifier program has it (`Row` alone is the fold's row here). -/
abbrev GRow : Type := OnBytes.Row

/-- Every coefficient of a mask form turned. -/
def negMasks (m : MaskForm) : MaskForm := m.map fun t => (t.1, subE zeroE t.2)

/-- A claim that reads hidden values alone, "form = 0", as the row "- masks = - value". -/
def rowOfAff (F : Fork) (home : Array Slot) (a : Aff) : Option GRow :=
  (maskSide F home a).map fun y => ({ target := subE zeroE y.2 } : GRow).addMasks (negMasks y.1)

/-- A claim that reads the planes, as a row. planesAt: the caller's: it adds a vector on the planes
to a row. turned: the row is "scalar * <v, bits> - masks = - value"; else "- scalar * <v, bits> +
masks = value". -/
def rowOfPlane (planesAt : GRow → Tensor → GRow) (F : Fork) (home : Array Slot)
    (turned : Bool) (c : PlaneClaim) : Option GRow :=
  (maskSide F home c.lead).map fun y =>
    if turned then
      (planesAt { target := subE zeroE y.2 } { scalar := c.scalar, pairs := c.pairs }).addMasks
        (negMasks y.1)
    else
      (planesAt { target := y.2 } { scalar := subE zeroE c.scalar, pairs := c.pairs }).addMasks y.1

/-- **The rows that a lookup leaves in its group, in the program's order**: the claims that read
hidden values alone but for the last (the bits' sumcheck's); the leaves' row; the bits' sumcheck's;
the bits' value; the counts'. F: the ledger behind "planes". Nothing where a claim has no row, or
there are not three claims on the planes. -/
def groupRows (planesAt : GRow → Tensor → GRow) (F : Fork) (home : Array Slot)
    (objects : List Aff) (planes : List PlaneClaim) : Option (List GRow) :=
  match planes, objects.getLast? with
  | [leaves, value, counts], some bits => do
    let front ← objects.dropLast.mapM (rowOfAff F home)
    let r₁ ← rowOfPlane planesAt F home true leaves
    let r₂ ← rowOfAff F home bits
    let r₃ ← rowOfPlane planesAt F home false value
    let r₄ ← rowOfPlane planesAt F home true counts
    pure (front ++ [r₁, r₂, r₃, r₄])
  | _, _ => none

/-- **The claims on the parts' keys**, by the program's own `keysOf`: FOR THE CALLER'S RUN. -/
def keyClaims (S : Lkp.Public) (F : Fork) (home : Array Slot) (g : HeardG) :
    Option (List Lkp.Keys) :=
  g.keys.zipIdx.mapM fun k =>
    (maskSide F home k.1.2).map fun y =>
      Lkp.keysOf S g.theta g.alpha k.2 ⟨k.1.1.toList.reverse, y.1, y.2⟩

end VerifiableInference.Desc.K3
