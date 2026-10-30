-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/FiftyAtFull.lean: K1's FIFTY LATER PLACES OF THE FULL SIZE (every link's reads and digits), EACH AT THE LOT's OWN BLOCK AND THE PLACE's OWN NUMBERS, AT ITS ROW OF THE TABLE OF JOINTS: THE FIVE TIES, for every
value z of the public part: Johnson/Desc/K1/Law/TiedAtLater.lean's block_tied, with these of its premises had AT THE WRITTEN CONFIGURATION:
  · the four facts on the block's text: Johnson/Desc/K1/Law/BlocksAtLater.lean
  · the kind's Boolean condPort: from Johnson/Desc/K1/Law/AtFull.lean's k01_sits_first_chain (the place stands on its written entry: 3 l + 2 | 3 l + 1), under hc · hs
  · RowL: its nine fields that read the table alone: BY THE KERNEL at the table's own written list of places (Johnson/Desc/K1/Law/RowLFull.lean); its other three ARE the premises hinj · trees · msgs (NO PREMISE «the door makes nothing at the place»: what the door's filling makes at the place, madeAt, comes into the list that hpub | hpubP pay)
  · at a digits' row hback: the row closes and reads nothing (readsNoneB_full, BY THE KERNEL); and no tied public item comes there (what the door's filling makes there may come)
Main names:
  radRec · condPort_radRec · parD | parR · noD | noR · readsNoneB · readsNoneB_full
  later_sampled_full  [kernel] EVERY MESSAGE OF THE FIFTY PLACES HAS A SAMPLE, at the written shape: so «all the place's messages» (laterSeatsB; the joining) and «the sampled tenants» (N.sent; the seal) speak of
                      the same messages there · later_sampled: so at the place's own numbers, under hs
  k01_digits_tied     ∀ l < 25, ∀ z: TiedAt N Mg linksFull (flatPlacesOf linksFull true) (z, ·) (14 l + k1Ix l true + 2) (sendPiece (laterAt q gp l (k1Ix l true + 1) 2 digits).retype …)
  k01_reads_tied      the like at 14 l + k1Ix l false + 2, at (k1Reads Z G l X (k1Ix l false + 1) reads).retype
USER. k01_later_tied (Johnson/Desc/K1/Law/LaterOne.lean) calls both.
PREMISES LEFT, BY NAME: hc · hs (by runs) · ON THE PLAN's NUMBERS: hinj · trees · msgs · laterSeatsB · hbase · ON THE LETTERS: FillL · hgo · ON THE PROMISE IN FRONT: hg (it must say that the
state's frame's group is the plan's: NO CLAUSE OF onAt SAYS SO TODAY: it wants a public item) · ON THE PIECE: d₁'s entry and kind; e · hseal · hshown · hpub · hpubP (at the digits: at what the door's filling makes there alone) · AT THE READS ALONE: hback («the forms at the committed
array and the tie give the forms as functions of the cells»: the table books that exchange as its own files' to show).
What is not claimed. NO MEMBER OF THESE IS SHOWN; whether they can be met together at an honest run is not shown. X (the link's part of the state) is a letter at the reads: a mismatched X makes the quiet step the refuser, and the
tie idle. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.TiedAtLater
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.Desc.K1.Law.RowLFull
import Johnson.Desc.K1.Law.AtFull
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Flat OnBytes.Maker
open Johnson.Pack (portOmZ)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ TiedAt relAt
  openAfter rowQ linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

variable {Pp Cl W : Type} {F : Frame}

/-- The radii of entry number k of the proof file's first chain, at the place's numbers. -/
def radRec (k : Nat) (P : Par) : Nat → Nat :=
  match (litAt sendsFullLit packFullLit 2 0)[k]? with
  | some y => radFrom P y.2.l
  | none => fun _ => 0

theorem condPort_radRec {k : Nat} {P : Par} (h : PlaceOk 2 0 k P) :
    condPort P (radRec k P) = true := by
  obtain ⟨y, hy, _, hc⟩ := h
  unfold radRec
  rw [hy]
  exact hc

/-- The digits' place's numbers at link l. -/
abbrev parD (q : Params.First) (gp : GPar) (l : Nat) : Par := parLater q gp l (k1Ix l true + 1) 2

/-- The reads' place's numbers at link l. -/
abbrev parR (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) : Par :=
  parLater G.first (gpOf Z) l (k1Ix l false + 1) 1

/-- The numbers of link l's digits' and reads' blocks in the flat list. -/
abbrev noD (l : Nat) : Nat := 14 * l + k1Ix l true + 2
abbrev noR (l : Nat) : Nat := 14 * l + k1Ix l false + 2

/-- The row closes and reads nothing. -/
def readsNoneB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((rowQ links ps k).ins ++ (rowQ links ps k).ctx ++ [Item.unmarked]).all fun i => i == Item.unmarked

set_option maxRecDepth 1000000 in
theorem readsNoneB_full : ((List.range 25).all fun l => readsNoneB linksFull (flatPlacesOf linksFull true) (noD l)) = true ∧
    readsNoneB linksFull (flatPlacesOf linksFull true) (noR 3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Every message of the fifty places has a sample**, at the written shape. -/
theorem later_sampled_full : ((List.range 25).all fun l => [1, 2].all fun m =>
    !(laterSent shapeFull l m).isEmpty && (laterSent shapeFull l m).all fun n => n.shape.answers != 0) =
      true := by
  decide +kernel

theorem later_sampled (q : Params.First) (gp : GPar) (hs : q.shape = shapeFull) (l piece m : Nat)
    (hl : l < 25) (hm : m = 1 ∨ m = 2) (j : Fin (shapesOf (parLater q gp l piece m)).length) :
    sampledAt (parLater q gp l piece m) j := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 later_sampled_full l (List.mem_range.2 hl)) m
    (by rcases hm with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.1 ((Bool.and_eq_true_iff.1 h).2)
  have hmem : (shapesOf (parLater q gp l piece m))[j.val] ∈
      (laterSent shapeFull l m).map (·.shape) := by
    have e : shapesOf (parLater q gp l piece m) = (laterSent shapeFull l m).map (·.shape) := by
      unfold shapesOf
      rw [parLater_sent, hs]
    rw [← e]
    exact List.getElem_mem j.isLt
  obtain ⟨n, hn, e⟩ := List.mem_map.1 hmem
  have := h2 n hn
  unfold sampledAt msgAt
  rw [← e]
  simpa using this

/-- **THE FIVE TIES AT EVERY LINK's DIGITS' PLACE, AT THE LOT's OWN BLOCK.** -/
theorem k01_digits_tied (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (q : Params.First) (gp : GPar)
    (hc : q.codes = codesFull2) (hs : q.shape = shapeFull) (l : ℕ) (hl : l < 25)
    (digits : Option (List Nat)) (c : Block S Cl) (hu : c.UnderR ((laterAt q gp l (k1Ix l true + 1) 2 digits : Block S Unit).retype : Block S Cl))
    (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry (parD q gp l)) (hk₁ : d₁.kind = .seeds) (e : Nat)
    (he : errPort (parD q gp l) (radRec (3 * l + 2) (parD q gp l)) ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ (parD q gp l).codes (shapeAt (parD q gp l) j) (radRec (3 * l + 2) (parD q gp l) j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j,
      (portOmZ (parD q gp l).codes (shapeAt (parD q gp l) j) (radRec (3 * l + 2) (parD q gp l) j.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) c base d₁ d₂
      (parD q gp l).coordinates e).ior.imp y τ) = fIn y τ.1)
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noD l + 1)), N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noD l + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noD l]? + (layOf (parD q gp l)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noD l + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noD l]? + (parD q gp l).sent.size)
    (hF : FillL (YesOf (laterAt q gp l (k1Ix l true + 1) 2 digits : Block S Unit)) (InAt N Mg linksFull (flatPlacesOf linksFull true) (noD l)) N Mg (openAt linksFull (flatPlacesOf linksFull true) (noD l))
      ((First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noD l]?.getD []) (openAt linksFull (flatPlacesOf linksFull true) (noD l + 1))
      ((First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noD l + 1]?.getD []))
    (hgo : ∀ (x x' : Pp × S) y y' w i, YesOf (laterAt q gp l (k1Ix l true + 1) 2 digits : Block S Unit) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noD l) x y →
      KeptBelow base y y' →
      openAfter (insQ linksFull (flatPlacesOf linksFull true)) (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ First.start linksFull) (noD l) i →
      ¬ insQ linksFull (flatPlacesOf linksFull true) (noD l) i → i.holds N Mg x' y' w → i.holds N Mg x y w)
    (hP : laterSeatsB N (parD q gp l) l 2 (N.treesAt (flatPlacesOf linksFull true)[noD l]?) = true)
    (hbase : ∀ u ∈ First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noD l)), u.1 < base)
    (hg : ∀ (s : S) y, InAt N Mg linksFull (flatPlacesOf linksFull true) (noD l) (z, s) y →
      ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (hseal : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noD l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parD q gp l).coordinates e).ior.red.out a τ = some x →
      (∀ j, sampledAt (parD q gp l) j →
        Sealed (parD q gp l).codes (shapeAt (parD q gp l) j) (radRec (3 * l + 2) (parD q gp l) j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (parD q gp l)).length + j.val)) →
      ∀ u ∈ N.sent l 2, Mg.held u.1 u.2 (z, x.1) = true ∧
        Mg.noColl u.1 u.2 (z, x.1) (strsOf F x.2))
    (hshown : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noD l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parD q gp l).coordinates e).ior.red.out a τ = some x →
      ∀ u ∈ N.sent l 2, Mg.shown u.1 u.2 (strsOf F x.2))
    (hpub : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noD l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parD q gp l).coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ [] ++ madeAt Mg.more linksFull (flatPlacesOf linksFull true) (noD l), Mg.pub q (z, x.1) = true)
    (hpubP : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noD l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parD q gp l).coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ [] ++ madeAt Mg.more linksFull (flatPlacesOf linksFull true) (noD l),
        q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noD l + 1]?.getD [] → Mg.pubP q (z, x.1)) :
    TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noD l)
      (sendPiece (W := W) (F := F) c base d₁ d₂ (parD q gp l).coordinates e) :=
  block_tied N Mg linksFull (flatPlacesOf linksFull true) z (noD l) l 2 (parD q gp l) (laterAt q gp l (k1Ix l true + 1) 2 digits : Block S Unit) c hu rfl
    (isSend_commitAtS _ _ _ _) (commit_mark _ _ _ _)
    (fun s s' r₁ r₂ gs h g hg' => stepL_commitAtS _ _ _ _ s s' r₁ r₂ gs h g hg' z)
    (radRec (3 * l + 2) (parD q gp l))
    (condPort_radRec ((k01_sits_first_chain q gp hc hs).2.1 l (k1Ix l true + 1) 2 hl (Or.inr rfl)))
    base d₁ d₂ he₁ hk₁ e he fOf fIn hf _
    (rowL_digits_full N Mg.more l hl _ _ hinj trees msgs) hF hgo hP hbase hg hseal hshown
    hpub hpubP
    (fun a τ x w _ hm _ _ i hi => by
      have := List.all_eq_true.1 (List.all_eq_true.1 readsNoneB_full.1 l (List.mem_range.2 hl)) i hi
      obtain rfl : i = .unmarked := eq_of_beq this
      exact hm)

/-- **THE FIVE TIES AT EVERY LINK's READS' PLACE, AT THE LOT's OWN BLOCK.** -/
theorem k01_reads_tied (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hc : G.first.codes = codesFull2) (hs : G.first.shape = shapeFull) (l : ℕ) (hl : l < 25)
    (X : LinkH) (reads : Option (List Nat)) (c : Block S Cl)
    (hu : c.UnderR ((k1Reads Z G l X (k1Ix l false + 1) reads).retype : Block S Cl))
    (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry (parR Z G l)) (hk₁ : d₁.kind = .seeds) (e : Nat)
    (he : errPort (parR Z G l) (radRec (3 * l + 1) (parR Z G l)) ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ (parR Z G l).codes (shapeAt (parR Z G l) j) (radRec (3 * l + 1) (parR Z G l) j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j,
      (portOmZ (parR Z G l).codes (shapeAt (parR Z G l) j) (radRec (3 * l + 1) (parR Z G l) j.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) c base d₁ d₂
      (parR Z G l).coordinates e).ior.imp y τ) = fIn y τ.1)
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noR l + 1)), N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noR l + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noR l]? + (layOf (parR Z G l)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noR l + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noR l]? + (parR Z G l).sent.size)
    (hF : FillL (YesOf (k1Reads Z G l X (k1Ix l false + 1) reads)) (InAt N Mg linksFull (flatPlacesOf linksFull true) (noR l)) N Mg (openAt linksFull (flatPlacesOf linksFull true) (noR l))
      ((First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noR l]?.getD []) (openAt linksFull (flatPlacesOf linksFull true) (noR l + 1))
      ((First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noR l + 1]?.getD []))
    (hgo : ∀ (x x' : Pp × S) y y' w i, YesOf (k1Reads Z G l X (k1Ix l false + 1) reads) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noR l) x y →
      KeptBelow base y y' →
      openAfter (insQ linksFull (flatPlacesOf linksFull true)) (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ First.start linksFull) (noR l) i →
      ¬ insQ linksFull (flatPlacesOf linksFull true) (noR l) i → i.holds N Mg x' y' w → i.holds N Mg x y w)
    (hP : laterSeatsB N (parR Z G l) l 1 (N.treesAt (flatPlacesOf linksFull true)[noR l]?) = true)
    (hbase : ∀ u ∈ First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noR l)), u.1 < base)
    (hg : ∀ (s : S) y, InAt N Mg linksFull (flatPlacesOf linksFull true) (noR l) (z, s) y →
      ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (hseal : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noR l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parR Z G l).coordinates e).ior.red.out a τ = some x →
      (∀ j, sampledAt (parR Z G l) j →
        Sealed (parR Z G l).codes (shapeAt (parR Z G l) j) (radRec (3 * l + 1) (parR Z G l) j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (parR Z G l)).length + j.val)) →
      ∀ u ∈ N.sent l 1, Mg.held u.1 u.2 (z, x.1) = true ∧
        Mg.noColl u.1 u.2 (z, x.1) (strsOf F x.2))
    (hshown : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noR l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parR Z G l).coordinates e).ior.red.out a τ = some x →
      ∀ u ∈ N.sent l 1, Mg.shown u.1 u.2 (strsOf F x.2))
    (hpub : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noR l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parR Z G l).coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ tiedAt linksFull (flatPlacesOf linksFull true) (noR l) ++
        madeAt Mg.more linksFull (flatPlacesOf linksFull true) (noR l), Mg.pub q (z, x.1) = true)
    (hpubP : ∀ a τ x, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noR l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parR Z G l).coordinates e).ior.red.out a τ = some x →
      ∀ q ∈ tiedAt linksFull (flatPlacesOf linksFull true) (noR l) ++
        madeAt Mg.more linksFull (flatPlacesOf linksFull true) (noR l),
        q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noR l + 1]?.getD [] → Mg.pubP q (z, x.1))
    (hback : ∀ a τ x w, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noR l) a → a.1.failed = none →
      (sendPiece (W := W) (F := F) c base d₁ d₂
        (parR Z G l).coordinates e).ior.red.out a τ = some x →
      relAt (meansQ N Mg fun s : S => (z, s)) (outsQ linksFull (flatPlacesOf linksFull true) (noR l)) x w →
      relAt (meansQ N Mg fun s : S => (z, s)) (insQ linksFull (flatPlacesOf linksFull true) (noR l)) a w) :
    TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun s : S => (z, s)) (noR l)
      (sendPiece (W := W) (F := F) c base d₁ d₂ (parR Z G l).coordinates e) :=
  block_tied N Mg linksFull (flatPlacesOf linksFull true) z (noR l) l 1 (parR Z G l) (k1Reads Z G l X (k1Ix l false + 1) reads) c hu
    (rounds_k1Reads _ _ _ _ _ _)
    (isSend_k1Reads _ _ _ _ _ _) (reads_mark _ _ _ _ _ _)
    (fun s s' r₁ r₂ gs h g hg' => stepL_k1Reads _ _ _ _ _ _ s s' r₁ r₂ gs h g hg' z)
    (radRec (3 * l + 1) (parR Z G l))
    (condPort_radRec ((k01_sits_first_chain G.first (gpOf Z) hc hs).2.1 l (k1Ix l false + 1) 1 hl
      (Or.inl rfl)))
    base d₁ d₂ he₁ hk₁ e he fOf fIn hf _
    (rowL_reads_full N Mg.more l hl _ _ hinj trees msgs) hF hgo hP hbase hg hseal hshown hpub
    hpubP hback

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.condPort_radRec
#print axioms VerifiableInference.Desc.K1.readsNoneB_full
#print axioms VerifiableInference.Desc.K1.later_sampled_full
#print axioms VerifiableInference.Desc.K1.later_sampled
#print axioms VerifiableInference.Desc.K1.k01_digits_tied
#print axioms VerifiableInference.Desc.K1.k01_reads_tied
