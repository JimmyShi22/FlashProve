-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/HeadTabs.lean: five small makers in the description's own text, for the block that
makes the head's list of tables (Johnson/Desc/K8/ReadsQuiet.lean: tables). Each can give nothing,
and the block refuses there under its own name.

  cutTail z k          a point cut in two: the coordinates in front of its last k, and its last k.
                       Nothing: the point has fewer than k coordinates.
  tailOf z k           the last k coordinates. Nothing as in cutTail.
  callWith L seg       the number of the first call of the head's layout that has a segment of this
                       name. Nothing: no call has one.
  planeWeights g lm e  the weights on the 2 ^ lm rows of the planes' matrix under which the planes
                       are read at the lookup's point number e. Nothing: lm is not from 5 to kT + 5.
  tableAdded mats t M0 parts Lf phi nm   one table more: a record for each of the parts M0, M0 + 1
                       and so on of a matrix. Nothing: the table would be empty (it would share its
                       first entry with the next one).

What is taken from the hand-written program's files: the records E, TMat, HFun, Head.HL, CallD, Seg,
Head.Tables, Forest.Heard and Forest.Shape with their fields, and one plain function that cannot
refuse: eqTab (OnBytes/Model/Frame.lean). No function of these files that returns a Bool, an Option
or an Except is called.
That each says just what the program's cutLast, lastOf, Head.callNo, Forest.phiB and Head.addFun
say, at all arguments, is proved beside, in Johnson/Desc/Own/HeadTabsAgree.lean, which no block
imports.
LIMIT: whether these makers refuse enough is not said here.
No theorem here. Nothing on soundness.

-/
import OnBytes.Model.HeadTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Model

/-- A point cut in two: the coordinates in front of its last k, and its last k. -/
def cutTail (z : Array E) (k : Nat) : Option (Array E × Array E) :=
  if k > z.size then none
  else some (z.extract 0 (z.size - k), z.extract (z.size - k) z.size)

/-- The last k coordinates of a point. -/
def tailOf (z : Array E) (k : Nat) : Option (Array E) := (cutTail z k).map (·.2)

/-- The number of the first call that has a segment of this name. -/
def callWith (L : Head.HL) (seg : String) : Option Nat :=
  L.calls.findIdx? fun c => (c.segs.find? fun g => g.name == seg).isSome

/-- The weights under which the planes are read at the lookup's point number e (0, or another). -/
def planeWeights (g : Forest.Heard) (lm e : Nat) : Option (Array E) :=
  let h := g.shape
  let z := if e = 0 then g.zb0 else g.zb1
  if lm < 5 || lm > h.kT + 5 then none
  else some (eqTab (z.extract (h.kT + 5 - lm) h.kT ++ z.extract (h.kT + h.cK) z.size))

/-- One table more. Lf: the length of a stretch. -/
def tableAdded (mats : Array TMat) (t : Head.Tables) (M0 parts Lf : Nat) (phi : Array E)
    (nm : String) : Option Head.Tables :=
  let r := (List.range parts).foldl
    (fun (s : Array HFun × Nat) q =>
      let M := mats.getD (M0 + q) {}
      (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
        s.2 + M.k * (M.m / Lf)))
    (t.funs, t.p)
  if r.2 == t.p then none
  else some { funs := r.1, p := r.2, tab := t.tab ++ [(nm, t.p, r.2 - t.p)] }

end VerifiableInference.Desc.Own
