-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeTies.lean: the honest side of the kind "lookup"
(K3): THE TIES BETWEEN A READING AND KEY VECTORS OF ANOTHER MAKE AND THE SEATED FILLING'S OWN, IN
THEIR SMALLEST FORM. A structure of propositions; theorems with proofs.

`worth_at_digits`, `worth_at_attention`, `worth_at_layers`
(Honest/K3/Law/Thread/ExchangeWorth.lean) ask the three sentences on a filling (`FillsAt`) at the
table of joints' own reading and key vectors. The seated filling meets them at its own named
reading and vectors (Honest/K3/Law/Thread/ExchangeFillAt.lean), and they pass to a reading with the
same cells and to vectors whose joint vector is the same at every index below 2 ^ s.shape.v
(`FillsAt.turn`, Honest/K3/Law/Thread/ExchangeMg.lean).

  `TiedTo s ν₀ kv₀ theta ν kv`   THE PREMISE, three clauses: ν has ν₀'s cells; ν has ν₀'s value at
                     the place "zero"; kv has kv₀'s joint vector at the site's shape, at every
                     index below 2 ^ s.shape.v
  `FillsAt.tied`     the three sentences pass along the tie
  `tied_layers`, `tied_attention`, `tied_head`, `tied_digits`   CONDITIONAL ON `TiedTo` at the
                     sort's named reading and vectors, and on what the sort's theorem of
                     ExchangeFillAt.lean asks: `FillsAt` at ν and kv

The clause on cells is the form of the tie "the cell that the table's world reads is the filling's".
No clause speaks of a mask entry: `TiedTo` reads cells and the place "zero" alone. So the mask row
that is written at the named readings below (the function that is 0) lays no value anywhere.

Limits. `TiedTo` IS SHOWN HERE OF NO READING OF THE TABLE'S; no file of this folder shows it of one.
No instance of these hypotheses is exhibited in this file. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Slice (GE)
open OnBytes.HonestTrace (fromG fromA fromH nuFrom fsAt cellOf entryOf kvZ NamesFit MeetsAll Tr)
open OnBytes.Road (Hd.shapeA)
open Inst.Model (Instance ppref)

/-- **THE PREMISE: a reading and key vectors are tied to named ones.** -/
structure TiedTo (s : Site) (ν₀ : _root_.Fo.Pl → GE) (kv₀ : Nat → Nat → GE) (theta : GE)
    (ν : _root_.Fo.Pl → GE) (kv : Nat → Nat → GE) : Prop where
  /-- the same cells -/
  cells : ∀ r c, ν (.cell r c) = ν₀ (.cell r c)
  /-- the same value at the place "zero" -/
  zero : ν .zero = ν₀ .zero
  /-- the same joint vector, at every index below 2 ^ s.shape.v -/
  keys : ∀ x, x < 2 ^ s.shape.v →
    OnBytes.Ends.jointKey s.shape kv theta x = OnBytes.Ends.jointKey s.shape kv₀ theta x

/-- The three sentences pass along the tie. -/
theorem FillsAt.tied {s : Site} {a : Ask} {L : LookIn} {kv₀ : Nat → Nat → GE}
    {ν₀ : _root_.Fo.Pl → GE} {theta : GE} {heard : List Fmt.Drawn}
    (h : FillsAt s a L kv₀ ν₀ theta heard) {ν : _root_.Fo.Pl → GE} {kv : Nat → Nat → GE}
    (t : TiedTo s ν₀ kv₀ theta ν kv) : FillsAt s a L kv ν theta heard :=
  h.turn kv ν t.keys t.cells t.zero

variable {W₀ Rc Xi Tr' : Type}
variable (Z : Pub) (cells : Tr' → Cells) (weights : W₀ → Weights)
  (req : Xi → OnBytes.Model.Head.Covered × Array Nat)
variable {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- **CONDITIONAL, as the file's head lists: on the calls of a group's layers.** No instance of
these hypotheses is exhibited in this file. -/
theorem tied_layers (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .layers) (t : Local W₀ Rc Xi Tr') (B : ShapeIsFs Z.p.X s)
    (PL : PlanLabels Z.p.X) (O : PlanOwners Z.p.X) (N : NamesFit Z.p.X T)
    (M : MeetsAll Z.p.X i x T) (hg : s.group < 12) (hC : cells t.trace = ⟨cellOf Z.p.X T⟩)
    (hW : weights t.w₀ = ⟨entryOf i⟩) (theta : GE) (heard : List Fmt.Drawn)
    (ν : _root_.Fo.Pl → GE) (kv : Nat → Nat → GE)
    (hT : TiedTo s (nuFrom Z.p.X (cellOf Z.p.X T) (2 * s.group) fun _ => 0)
      (OnBytes.Ends.G.kvG Z.p.X.layers s.group (fromG Z.p.X (cellOf Z.p.X T) (entryOf i) s.group))
      theta ν kv) :
    FillsAt s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t)
      (lookG Z.p.X s.group ⟨cellOf Z.p.X T⟩ ⟨entryOf i⟩) kv ν theta heard :=
  (fills_layers Z cells weights req s hs hd hc t B PL O N M hg hC hW _ theta heard).tied hT

/-- **CONDITIONAL, as the file's head lists: on the calls of a group's attention.** No instance of
these hypotheses is exhibited in this file. -/
theorem tied_attention (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .attention) (t : Local W₀ Rc Xi Tr') (B : ShapeIsFs Z.p.X s)
    (PL : PlanLabels Z.p.X) (O : PlanOwners Z.p.X) (N : NamesFit Z.p.X T)
    (M : MeetsAll Z.p.X i x T) (hg : s.group < 12) (hC : cells t.trace = ⟨cellOf Z.p.X T⟩)
    (theta : GE) (heard : List Fmt.Drawn) (ν : _root_.Fo.Pl → GE) (kv : Nat → Nat → GE)
    (hT : TiedTo s (nuFrom Z.p.X (cellOf Z.p.X T) (2 * s.group + 1) fun _ => 0)
      (OnBytes.Ends.A.kvA (Hd.shapeA Z.p.X s.group) (fsAt Z.p.X s.group)
        (fromA Z.p.X (cellOf Z.p.X T) s.group)) theta ν kv) :
    FillsAt s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t)
      (lookA Z.p.X s.group ⟨cellOf Z.p.X T⟩) kv ν theta heard :=
  (fills_attention Z cells weights req s hs hd hc t B PL O N M hg hC _ theta heard).tied hT

/-- **CONDITIONAL, as the file's head lists: on the head's calls.** No instance of these hypotheses
is exhibited in this file. -/
theorem tied_head (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .head) (t : Local W₀ Rc Xi Tr') (B : ShapeIsFs Z.p.X s)
    (PL : PlanLabels Z.p.X) (O : PlanOwners Z.p.X) (N : NamesFit Z.p.X T)
    (M : MeetsAll Z.p.X i x T) (hC : cells t.trace = ⟨cellOf Z.p.X T⟩)
    (hW : weights t.w₀ = ⟨entryOf i⟩) (theta : GE) (heard : List Fmt.Drawn)
    (ν : _root_.Fo.Pl → GE) (kv : Nat → Nat → GE)
    (hT : TiedTo s (nuFrom Z.p.X (cellOf Z.p.X T) 24 fun _ => 0)
      (OnBytes.Ends.H.kvH (headPub Z.p.X (req t.x).1 (req t.x).2)
        (fromH Z.p.X (cellOf Z.p.X T) (entryOf i))) theta ν kv) :
    FillsAt s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t)
      (lookH Z.p.X (headPub Z.p.X (req t.x).1 (req t.x).2) ⟨cellOf Z.p.X T⟩ ⟨entryOf i⟩) kv ν theta
      heard :=
  (fills_head Z cells weights req s hs hd hc t B PL O N M hC hW _ theta heard).tied hT

/-- **CONDITIONAL, as the file's head lists: on the digits of the smallness test.** The tie is asked
at every number r of a round: the site has one. No instance of these hypotheses is exhibited in this
file. -/
theorem tied_digits (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = true)
    (t : Local W₀ Rc Xi Tr') (B : ShapeIsFs Z.p.X s)
    (hF : Fo.ZPlan.FromPieces (tlOf Z.p.X s.link)) (theta : GE) (heard : List Fmt.Drawn)
    (ν : _root_.Fo.Pl → GE) (kv : Nat → Nat → GE)
    (hT : ∀ r, s.rng = some r →
      TiedTo s
        (nuZm (tlOf Z.p.X s.link) (zzOwn Z.p.X s.link (cells t.trace) (tritsAt heard r))
          fun _ => 0)
        (kvZ (tlOf Z.p.X s.link) (inExt (zzOwn Z.p.X s.link (cells t.trace) (tritsAt heard r))))
        theta ν kv) :
    ∃ r, s.rng = some r ∧
      FillsAt s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t)
        (lookZ (tlOf Z.p.X s.link) (zzOwn Z.p.X s.link (cells t.trace) (tritsAt heard r))) kv ν
        theta heard := by
  obtain ⟨r, hr, hL⟩ := fills_digits Z cells weights req s hs hd t B hF (fun _ => 0) theta heard
  exact ⟨r, hr, hL.tied (hT r hr)⟩

#print axioms ProofFile.Honest.K3.Law.Exchange.FillsAt.tied
#print axioms ProofFile.Honest.K3.Law.Exchange.tied_layers
#print axioms ProofFile.Honest.K3.Law.Exchange.tied_attention
#print axioms ProofFile.Honest.K3.Law.Exchange.tied_head
#print axioms ProofFile.Honest.K3.Law.Exchange.tied_digits
#print axioms ProofFile.Honest.K3.Law.Exchange.TiedTo

end ProofFile.Honest.K3.Law.Exchange
