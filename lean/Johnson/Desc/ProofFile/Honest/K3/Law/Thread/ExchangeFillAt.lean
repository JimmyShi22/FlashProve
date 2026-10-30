-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeFillAt.lean: the honest side of the kind
"lookup" (K3): THE THREE SENTENCES ON A FILLING that `worth_site_fill`
(Honest/K3/Law/Thread/ExchangeFill.lean) asks, AT THE FOUR SORTS OF SITE, at the seated filling, AT
NAMED KEY VECTORS AND A NAMED READING WITH ANY MASK ROW. A structure of propositions; theorems with
proofs.

  `FillsAt s a L kv ν theta heard`   the three sentences, under one name: the reader a yields
                     `L.hidden` at the challenges heard; L's keys are the joint vector of kv at the
                     site's shape, at every index below 2 ^ s.shape.v (of the other indices nothing
                     is said); L's bits are ν's readings of their places at the site's numbers
  `fills_layers`     on the calls of a group's layers
  `fills_attention`  on the calls of a group's attention
  `fills_head`       on the head's calls
  `fills_digits`     on the digits of the smallness test

Each is CONDITIONAL ON: the site is one of the public part's; its shape is the shape that the plan
holds for it; at the calls: the plan's labels and owners, the names' fit and the trace's law, and
the readers' equations; at a group's layers and attention moreover hg: the group's number is below
12; at the digits: the plan's pieces. Three written numbers stand in the statements: 12 (hg), 24
(`fills_head`: the number at which `nuFrom` reads the head's cells) and 32 (`FillsAt.bits`: the
planes): the named readings are spelled at the full size's numbering, as the library's own text has
them (Johnson/HonestTrace/FromCells.lean: `fromH` reads at 24; `PartsFit.as` speaks of the groups
below 12). Each joins Honest/K3/Law/SiteShapes.lean (which filling, shape and packing a site has) to
Honest/K3/Law/MeetsNamed.lean (the fillings' keys and bits by name).

Limits. That the table of joints' own reading and key vectors at an honest witness are the named
ones, with the coins spent as the mask row, is shown nowhere here. No instance of these hypotheses
is exhibited in this file. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeFill
import Johnson.Desc.ProofFile.Honest.K3.Law.MeetsNamed
import Johnson.Desc.ProofFile.Honest.K3.Law.SiteShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Slice (GE)
open OnBytes.HonestTrace (fromG fromA fromH nuFrom fsAt cellOf entryOf kvZ NamesFit MeetsAll Tr)
open OnBytes.Road (Hd.shapeA)
open Inst.Model (Instance ppref)

/-- **The three sentences on a filling**, under one name. -/
structure FillsAt (s : Site) (a : Ask) (L : LookIn) (kv : Nat → Nat → GE) (ν : _root_.Fo.Pl → GE)
    (theta : GE) (heard : List Fmt.Drawn) : Prop where
  /-- the reader yields the filling's structure at the challenges heard -/
  reads : a heard = L.hidden
  /-- the filling's keys are the joint vector, at every index below 2 ^ s.shape.v: `worth_site_fill`
  asks them there alone -/
  keys : ∀ x, x < 2 ^ s.shape.v → L.key theta x = OnBytes.Ends.jointKey s.shape kv theta x
  /-- the filling's bits are the reading of their places -/
  bits : ∀ u j, u < 2 ^ s.shape.d → j < 32 →
    L.bit u j = ν ((_root_.Fo.numsF s.shape s.p.lm s.p.first theta).bAt u j)

variable {W₀ Rc Xi Tr' : Type}
variable (Z : Pub) (cells : Tr' → Cells) (weights : W₀ → Weights)
  (req : Xi → OnBytes.Model.Head.Covered × Array Nat)
variable {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- **CONDITIONAL, as the file's head lists: on the calls of a group's layers.** No instance of
these hypotheses is exhibited in this file. -/
theorem fills_layers (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .layers) (t : Local W₀ Rc Xi Tr') (B : ShapeIsFs Z.p.X s)
    (PL : PlanLabels Z.p.X) (O : PlanOwners Z.p.X) (N : NamesFit Z.p.X T)
    (M : MeetsAll Z.p.X i x T) (hg : s.group < 12) (hC : cells t.trace = ⟨cellOf Z.p.X T⟩)
    (hW : weights t.w₀ = ⟨entryOf i⟩) (mask : Nat → GE) (theta : GE) (heard : List Fmt.Drawn) :
    FillsAt s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t)
      (lookG Z.p.X s.group ⟨cellOf Z.p.X T⟩ ⟨entryOf i⟩)
      (OnBytes.Ends.G.kvG Z.p.X.layers s.group (fromG Z.p.X (cellOf Z.p.X T) (entryOf i) s.group))
      (nuFrom Z.p.X (cellOf Z.p.X T) (2 * s.group) mask) theta heard := by
  obtain ⟨h1, h2, h3⟩ := Spec.site_layers Z s hs hd hc
  have hsh : s.shape = Z.p.X.y.fo := Option.some.inj (B.symm.trans h1)
  refine ⟨?_, fun n _ => ?_, fun u j hu hj => ?_⟩
  · rw [h3]
    show ((tiedOwnSources Z.p.X cells weights req).layers s.group (cells t.trace)
      (weights t.w₀)).hidden = _
    rw [hC, hW]
    exact congrArg LookIn.hidden (ownLayers_eq PL O N M hg cells weights _)
  · rw [hsh]
    exact lookG_key Z.p.X s.group _ _ theta n
  · rw [hsh, h2]
    exact lookG_bit Z.p.X hg _ _ mask theta s.p.first (by rw [← hsh]; exact hu) hj

/-- **CONDITIONAL, as the file's head lists: on the calls of a group's attention.** No instance of
these hypotheses is exhibited in this file. -/
theorem fills_attention (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .attention) (t : Local W₀ Rc Xi Tr') (B : ShapeIsFs Z.p.X s)
    (PL : PlanLabels Z.p.X) (O : PlanOwners Z.p.X) (N : NamesFit Z.p.X T)
    (M : MeetsAll Z.p.X i x T) (hg : s.group < 12) (hC : cells t.trace = ⟨cellOf Z.p.X T⟩)
    (mask : Nat → GE) (theta : GE) (heard : List Fmt.Drawn) :
    FillsAt s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t)
      (lookA Z.p.X s.group ⟨cellOf Z.p.X T⟩)
      (OnBytes.Ends.A.kvA (Hd.shapeA Z.p.X s.group) (fsAt Z.p.X s.group)
        (fromA Z.p.X (cellOf Z.p.X T) s.group))
      (nuFrom Z.p.X (cellOf Z.p.X T) (2 * s.group + 1) mask) theta heard := by
  obtain ⟨h1, h2, h3⟩ := Spec.site_attention Z s hs hd hc
  have hsh : s.shape = fsAt Z.p.X s.group := Option.some.inj (B.symm.trans h1)
  refine ⟨?_, fun n _ => ?_, fun u j hu hj => ?_⟩
  · rw [h3]
    show ((tiedOwnSources Z.p.X cells weights req).attention s.group (cells t.trace)).hidden = _
    rw [hC]
    exact congrArg LookIn.hidden (ownAttention_eq PL O N M hg cells weights _)
  · rw [hsh]
    exact lookA_key Z.p.X s.group _ theta n
  · rw [hsh, h2]
    exact lookA_bit Z.p.X s.group _ mask theta s.p.first (by rw [← hsh]; exact hu) hj

/-- **CONDITIONAL, as the file's head lists: on the head's calls.** No instance of these hypotheses
is exhibited in this file. -/
theorem fills_head (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .head) (t : Local W₀ Rc Xi Tr') (B : ShapeIsFs Z.p.X s)
    (PL : PlanLabels Z.p.X) (O : PlanOwners Z.p.X) (N : NamesFit Z.p.X T)
    (M : MeetsAll Z.p.X i x T) (hC : cells t.trace = ⟨cellOf Z.p.X T⟩)
    (hW : weights t.w₀ = ⟨entryOf i⟩) (mask : Nat → GE) (theta : GE) (heard : List Fmt.Drawn) :
    FillsAt s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t)
      (lookH Z.p.X (headPub Z.p.X (req t.x).1 (req t.x).2) ⟨cellOf Z.p.X T⟩ ⟨entryOf i⟩)
      (OnBytes.Ends.H.kvH (headPub Z.p.X (req t.x).1 (req t.x).2)
        (fromH Z.p.X (cellOf Z.p.X T) (entryOf i)))
      (nuFrom Z.p.X (cellOf Z.p.X T) 24 mask) theta heard := by
  obtain ⟨h1, h2, h3⟩ := Spec.site_head Z s hs hd hc
  have hsh : s.shape = Z.p.X.HLy.fs := Option.some.inj (B.symm.trans h1)
  refine ⟨?_, fun n _ => ?_, fun u j hu hj => ?_⟩
  · rw [h3]
    show ((tiedOwnSources Z.p.X cells weights req).head t.x (cells t.trace)
      (weights t.w₀)).hidden = _
    rw [hC, hW]
    exact congrArg LookIn.hidden (ownHead_eq PL O N M cells weights _ t.x)
  · rw [hsh]
    exact lookH_key Z.p.X _ _ _ theta n
  · rw [hsh, h2]
    exact lookH_bit Z.p.X _ rfl rfl _ _ mask theta s.p.first (by rw [← hsh]; exact hu) hj

/-- **CONDITIONAL, as the file's head lists: on the digits of the smallness test.** r: the number of
the round that samples the test's matrix. No instance of these hypotheses is exhibited in this file.
-/
theorem fills_digits (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = true)
    (t : Local W₀ Rc Xi Tr') (B : ShapeIsFs Z.p.X s)
    (hF : Fo.ZPlan.FromPieces (tlOf Z.p.X s.link)) (mask : Nat → GE) (theta : GE)
    (heard : List Fmt.Drawn) :
    ∃ r, s.rng = some r ∧
      FillsAt s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t)
        (lookZ (tlOf Z.p.X s.link) (zzOwn Z.p.X s.link (cells t.trace) (tritsAt heard r)))
        (kvZ (tlOf Z.p.X s.link)
          (inExt (zzOwn Z.p.X s.link (cells t.trace) (tritsAt heard r))))
        (nuZm (tlOf Z.p.X s.link) (zzOwn Z.p.X s.link (cells t.trace) (tritsAt heard r)) mask)
        theta heard := by
  obtain ⟨r, hr, h1, h2, h3⟩ := Spec.site_digits Z s hs hd
  have hsh : s.shape = (tlOf Z.p.X s.link).f9 := Option.some.inj (B.symm.trans h1)
  refine ⟨r, hr, ?_, fun n _ => ?_, fun u j hu hj => ?_⟩
  · rw [h3]
    rfl
  · rw [hsh]
    exact lookZ_key _ _ theta n
  · rw [hsh, h2]
    exact lookZ_bit hF _ mask theta s.p.first (by rw [← hsh]; exact hu) hj

#print axioms ProofFile.Honest.K3.Law.Exchange.fills_layers
#print axioms ProofFile.Honest.K3.Law.Exchange.fills_attention
#print axioms ProofFile.Honest.K3.Law.Exchange.fills_head
#print axioms ProofFile.Honest.K3.Law.Exchange.fills_digits
#print axioms ProofFile.Honest.K3.Law.Exchange.FillsAt

end ProofFile.Honest.K3.Law.Exchange
