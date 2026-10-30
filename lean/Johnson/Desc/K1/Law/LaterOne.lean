-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/LaterOne.lean: K01_law: THE FIFTY LATER PLACES UNDER ONE STATEMENT: the two tops (k01_reads_tied · k01_digits_tied) as one, with a letter d : Bool (false: the link's reads; true: its digits): so that the row's top has one
binder a premise.
  parL · blkL · noL · recL · momL · tiedL      the place's numbers, the lot's own block, the flat number, the written entry's number, the moment, the public items that come (tied; made by the door's filling): by cases on d
  k01_later_tied                               **the five ties at (l, d)**; hback is asked at the reads alone
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.FiftyAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Flat OnBytes.Maker
open Johnson.Pack (portOmZ)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ TiedAt relAt
  openAfter linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

variable {Pp Cl W : Type} {F : Frame}

def momL : Bool → ℕ
  | true => 2
  | false => 1

def recL (l : ℕ) : Bool → ℕ
  | true => 3 * l + 2
  | false => 3 * l + 1

abbrev noL (l : ℕ) (d : Bool) : ℕ := 14 * l + k1Ix l d + 2

def parL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) : Bool → Par
  | true => parD G.first (gpOf Z) l
  | false => parR Z G l

def blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) :
    Block S Unit :=
  match d with
  | true => laterAt G.first (gpOf Z) l (k1Ix l true + 1) 2 arrs
  | false => k1Reads Z G l X (k1Ix l false + 1) arrs

/-- The public items that come at (l, d): the tied ones (at the reads), and what the door's filling M makes at the place (FOURTH FORM). -/
def tiedL (M : More) (l : ℕ) : Bool → List Pub
  | true => [] ++ madeAt M linksFull (flatPlacesOf linksFull true) (noD l)
  | false => tiedAt linksFull (flatPlacesOf linksFull true) (noR l) ++
      madeAt M linksFull (flatPlacesOf linksFull true) (noR l)

/-- **THE FIVE TIES AT A LATER PLACE (l, d), AT ANY BLOCK UNDER THE LOT's OWN.** -/
theorem k01_later_tied (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hc : G.first.codes = codesFull2) (hs : G.first.shape = shapeFull) (l : ℕ) (hl : l < 25)
    (d : Bool) (X : LinkH) (arrs : Option (List Nat)) (c : Block S Cl)
    (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S Cl))
    (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry (parL Z G l d)) (hk₁ : d₁.kind = .seeds) (e : Nat)
    (he : errPort (parL Z G l d) (radRec (recL l d) (parL Z G l d)) ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ (parL Z G l d).codes (shapeAt (parL Z G l d) j) (radRec (recL l d) (parL Z G l d) j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j,
      (portOmZ (parL Z G l d).codes (shapeAt (parL Z G l d) j) (radRec (recL l d) (parL Z G l d) j.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) c base d₁ d₂
      (parL Z G l d).coordinates e).ior.imp y τ) = fIn y τ.1)
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)), N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G l d)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G l d).sent.size)
    (hF : FillL (YesOf (blkL Z G l d X arrs)) (InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d)) N Mg (openAt linksFull (flatPlacesOf linksFull true) (noL l d))
      ((First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD []) (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1))
      ((First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD []))
    (hgo : ∀ (x x' : Pp × S) y y' w i, YesOf (blkL Z G l d X arrs) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      KeptBelow base y y' →
      openAfter (insQ linksFull (flatPlacesOf linksFull true)) (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ First.start linksFull) (noL l d) i →
      ¬ insQ linksFull (flatPlacesOf linksFull true) (noL l d) i → i.holds N Mg x' y' w → i.holds N Mg x y w)
    (hP : laterSeatsB N (parL Z G l d) l (momL d) (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (hbase : ∀ u ∈ First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)), u.1 < base)
    (hg : ∀ (s : S) y, InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) y →
      ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (hseal : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂ (parL Z G l d).coordinates e).ior.red.out a τ = some x →
      (∀ j, sampledAt (parL Z G l d) j →
        Sealed (parL Z G l d).codes (shapeAt (parL Z G l d) j) (radRec (recL l d) (parL Z G l d) j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (parL Z G l d)).length + j.val)) →
      ∀ u ∈ N.sent l (momL d), Mg.held u.1 u.2 (z, x.1) = true ∧
        Mg.noColl u.1 u.2 (z, x.1) (strsOf F x.2))
    (hshown : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂ (parL Z G l d).coordinates e).ior.red.out a τ = some x →
      ∀ u ∈ N.sent l (momL d), Mg.shown u.1 u.2 (strsOf F x.2))
    (hpub : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂ (parL Z G l d).coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ tiedL Mg.more l d, Mg.pub q (z, x.1) = true)
    (hpubP : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂ (parL Z G l d).coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ tiedL Mg.more l d,
        q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] → Mg.pubP q (z, x.1))
    (hback : d = false → ∀ a τ x w, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d) a →
      a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂ (parL Z G l d).coordinates e).ior.red.out a τ = some x →
      relAt (meansQ N Mg fun s : S => (z, s)) (outsQ linksFull (flatPlacesOf linksFull true) (noL l d)) x w →
      relAt (meansQ N Mg fun s : S => (z, s)) (insQ linksFull (flatPlacesOf linksFull true) (noL l d)) a w) :
    TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noL l d)
      (sendPiece (W := W) (F := F) c base d₁ d₂ (parL Z G l d).coordinates e) := by
  cases d with
  | true =>
    exact k01_digits_tied N Mg z G.first (gpOf Z) hc hs l hl arrs c hu base d₁ d₂ he₁ hk₁ e he fOf
      fIn hf hinj trees msgs hF hgo hP hbase hg hseal hshown hpub hpubP
  | false =>
    exact k01_reads_tied N Mg z Z G hc hs l hl X arrs c hu base d₁ d₂ he₁ hk₁ e he fOf fIn hf
      hinj trees msgs hF hgo hP hbase hg hseal hshown hpub hpubP (hback rfl)

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_later_tied
