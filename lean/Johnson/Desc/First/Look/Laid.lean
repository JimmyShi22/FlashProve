-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/Laid.lean: for each lookup of the proof's
first chain, the host's count «laid»: for each tree of the key side, how many of its places the
host's key forms treat as padding: as plain functions of the plan. Definitions with code; no
theorem; nothing is evaluated in this file.

What it is for. The lookup's test on the plan (P.planOk, Johnson/Desc/First/Look/LookKind.lean) is
handed laid and asks laid == pub: the verifier program's Forest.paddingLaid
(OnBytes/Model/Look.lean). In the program three of the four hosts count laid inside a routine that
also builds forms. Here the counting alone stands, in the program's order:
  laidDigits tl: the smallness test's lookup on the digits: after HTailF2.linJoin9
    (OnBytes/Model/Tail.lean): the places that the claim's runs read, counted by tree by the
    program's own plain placesRead; what is left of a tree's 2^dT places is padding.
  laidLayers P: a layers' link: after Layer.joinStart (OnBytes/Model/Layer.lean): the program's own
    plain Env.weighedOf and Env.laidOf (OnBytes/Model/LayerForms.lean), by name, at a record Env of
    which they read the layout y alone [by their text]; the other fields are idle here.
  markColumnsP, laidHeadCall, laidHead h L: the head's link: after Head.markColumns, Head.keyForm
    (OnBytes/Model/HeadForms.lean) and Head.claimJoin (OnBytes/Model/Head.lean): TYPED ANEW: the
    program's two take the run's whole record, of which the counting reads the layout and the shape.
  At attention the program has the plain function already: Attention.laidPadding.
  tlAt X i: the plan's record of link i's smallness test.
  laidAt X i digits: the four, at link i of the public record; the split by i is lookAt's.
  padKeyDigits tl, padKeyAtt S, padKeyAt X i digits: THE TEST THAT STANDS IN FRONT OF THE COUNT at
    two of the four hosts: the call's padding key, before the shift, is 0 (HTailF2.linJoin9's
    "internal-f-padding-key"; Attention.paddingLaid's "internal-af-padding-key", but for calls of
    the kind KFD). There the key forms have no term at a padding place, so they read the key 0:
    «laid == pub» SAYS THAT THE HOST LAYS THE PADDING ROW ONLY TOGETHER WITH THIS TEST. At the
    layers and the head the key forms weigh the padding key itself: the program has no such test.

Limits. As the program's own docstring says of Forest.paddingLaid: the places are counted NEXT TO
the key forms, from the lists of columns or pieces, not FROM the forms: a fault inside a form is not
seen; at the layers and the head pub itself comes of the same lists, so a fault in a list is not
seen either. That a function here counts as the program's routine counts has been held by reading
and by runs alone. At the head the program takes first, dT and NT from the HEARD record's shape, at
the layers NT: here they are the layout's (L.fs; P.y.fo): one shape wherever the lookup was run at
the layout's own, which is not asked here. P.planOk does not ask padKeyAt: it is a clause for the
hosts' own tests on the plan. These counts belong to the hosts' kinds.

No soundness is claimed. Not claimed: anything on completeness or hiding.

-/
import OnBytes.Model.VerifyPublic
import OnBytes.Model.Layer
import OnBytes.Model.Head
import OnBytes.Model.Attention

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The digits. None where a run reads a place behind its call's last tree, or a tree is read at
more places than it has. -/
def laidDigits (tl : HTailF2) : Option (Array Nat) :=
  let h := tl.f9
  let read : Option (Array Nat) :=
    [0, 1].foldlM
      (fun read q =>
        let i := h.iota.getD q 0
        (tl.zOf q).pieces.foldlM
          (fun read p =>
            (List.range p.Rp).foldlM
              (fun read rr =>
                HTailF2.placesRead h.dT i (h.first.getD q 0) (2 ^ i + 1) read (p.off + rr * p.CP)
                  p.Cp)
              read)
          read)
      (Forest.noPub h)
  read.bind fun r =>
    if r.all fun x => decide (x ≤ 2 ^ h.dT) then some (r.map fun x => 2 ^ h.dT - x) else none

/-- The digits: the padding key of both calls, before the shift, is 0. -/
def padKeyDigits (tl : HTailF2) : Bool :=
  [0, 1].all fun q => let c := (tl.zOf q).call; c.tauAt c.t0 == 0

/-- Attention: the same of every call but those of the kind KFD. -/
def padKeyAtt (S : Attention.Shape) : Bool :=
  S.calls.all fun c => c.kind == .kfd || c.call.tauAt c.call.t0 == 0

/-- A layers' link. None where two segments list one column, or a column lies in no tree. -/
def laidLayers (P : Layer.Pub) : Option (Array Nat) :=
  let v : Layer.Env := { y := P.y, sc := P.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] }
  (P.y.calls.mapM v.weighedOf).bind fun weighed =>
    weighed.toList.zipIdx.foldlM (fun laid x => v.laidOf x.2 x.1 laid) (Forest.noPub P.y.fo)

/-- The head: the columns of one segment are marked: 1 if the column holds real places, 2 if its
entry is no entry of the vocabulary. None at a column that two segments list or that lies behind
the call's last. -/
def markColumnsP (h : Head.Shape) (L : Head.HL) (weighed : Array Nat) (g : Seg) :
    Option (Array Nat) :=
  let v0 := Head.firstEntry L g.name
  (List.range g.n).foldlM
    (fun w x =>
      let p := g.pos.getD x 0
      if p < w.size && w.getD p 1 == 0 then
        some (w.set! p (if Head.perEntry g.name && v0 + x ≥ h.V then 2 else 1))
      else none)
    weighed

/-- The head, call number q: T keys more in its tree for each column that is not marked 1. -/
def laidHeadCall (h : Head.Shape) (L : Head.HL) (q : Nat) (laid : Array Nat) :
    Option (Array Nat) :=
  let c := L.calls.getD q default
  (c.segs.foldlM (markColumnsP h L) (Array.replicate c.J 0)).bind fun weighed =>
    (List.range c.J).foldlM
      (fun laid j =>
        if weighed.getD j 0 != 1 then
          let y := L.fs.first.getD q 0 + j / 2 ^ (L.fs.dT - h.lt)
          if y < laid.size then some (laid.modify y (· + h.T)) else none
        else some laid)
      laid

/-- The head's link. -/
def laidHead (h : Head.Shape) (L : Head.HL) : Option (Array Nat) :=
  (List.range L.calls.size).foldlM (fun laid q => laidHeadCall h L q laid)
    (Array.replicate L.fs.NT 0)

/-- The plan's record of link i's smallness test. -/
def tlAt (X : Verify.Public) (i : Nat) : Option HTailF2 :=
  let step := if X.p4 then 2 else 1
  if i == step * X.NGr then some X.H.tl
  else if i % step == 0 then X.G[i / step]?.map (·.tl)
  else X.A[i / step]?.map (·.seam.tl)

/-- **The host's count at link i's lookup, of the public record alone.** -/
def laidAt (X : Verify.Public) (i : Nat) (digits : Bool) : Option (Array Nat) :=
  let step := if X.p4 then 2 else 1
  if digits then (tlAt X i).bind laidDigits
  else if i == step * X.NGr then laidHead X.hS X.HLy
  else if i % step == 0 then (X.G[i / step]?).bind fun _ => laidLayers X.layers
  else X.A[i / step]?.bind fun a => (Attention.laidPadding a.S a.fs).toOption

/-- The test on the padding key at link i's lookup; true where the program has none. -/
def padKeyAt (X : Verify.Public) (i : Nat) (digits : Bool) : Option Bool :=
  let step := if X.p4 then 2 else 1
  if digits then (tlAt X i).map padKeyDigits
  else if i == step * X.NGr then some true
  else if i % step == 0 then (X.G[i / step]?).map fun _ => true
  else X.A[i / step]?.map fun a => padKeyAtt a.S

end VerifiableInference.Desc.First.Look
