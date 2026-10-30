-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4MeansAtWide.lean: THE STRUCTURES OF EQUATIONS `K4Means` (K4Means.lean) AND
`K4PileNames` (Riders/KeptNames.lean) HOLD AT THE WIDER MEANING `mgWide Dm E Mg`
(Johnson/Desc/Sound/MgWide.lean: the composed meaning with the tests and rows of the names that left
its door laid over it again). A definition and two statements; the proofs: unfolding, and lemmas on
mgAll, mgWide, pubAll, pubWide and k3SortAt. THE TEXT FOLLOWS A LEMMA AT ANOTHER TEXT OF THE
COMPOSED MEANING (Johnson/Desc/Sound/MgAt/K4.lean [not in this library]), field by field.

  `k4DataWide Dm E Mg`: the data: Dm's parameters, what the composed meaning makes of them, and the
    struck parts' data E (d12 · reqW · free0 · fvs; `k4Pile_mgWide` reads E.dP.tl too). E IS A FREE
    LETTER: at a wrong E (tl m = none, say: then "K8.lay7" at m is false at every state) no unmarked
    state is inside the promise at the wider meaning: E is held by the bridge's premises and by the
    filler's equations, not here.
  **`k4Means_mgWide`**: UNDER THREE PREMISES: the output head's segment is no feed-forward segment ·
  Mg's sentences without a test read no state · they hold at lookIn.
  **`k4Pile_mgWide`**: the five equations, by rfl.

Limits. THE WIDER MEANING IS A BRIDGE's SIDE, NOT THE MEANING THAT COUNTS: a law shown at it counts
only when the bridge's premises are paid (facts on reached states, most of them owed). It says which
terms the fields and tests ARE. Nothing of any sub-protocol. K04_law, the law of K4's sub-protocol
itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Riders.KeptNames
import Johnson.Desc.Sound.MgWide
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Road.K4.Riders (K4PileNames)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.First.FillK4 (isLay lookLayB callerInLayB)
open VerifiableInference.Desc.First.Look (K3Data k3SortAt lookInC lookOutC liveIsC sort_at)
open VerifiableInference.OnPublicFiles (fillK3HeadG headLink)
open VerifiableInference.Desc.Sound (MsgT mgAll mgWide MgData WideData oneDec)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P)
  (Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT))

/-- The wider meaning's own parameters, as the structure's data. -/
noncomputable def k4DataWide : K4Data Xi P Tok rows cols nR Dm.P13.lin.kCol X where
  cs := Dm.cs
  G := Dm.G
  arr := Dm.arr
  smp := Dm.smp
  ms := Dm.ms
  decT := Dm.decT
  hd := headLink X
  put := Dm.put
  H := oneDec Dm.decT Dm.H
  headPart := Dm.headPart
  digitsPart := Dm.digitsPart
  Rd := Dm.Rd
  runs := Dm.runs
  St := Dm.St
  wt := Dm.wt
  N := Dm.N
  base := Mg.inOrder
  shape := Dm.shape
  layout := Dm.layout
  reqW := E.reqW
  reqB := Dm.reqB
  rw13 := Dm.rw13
  nsOf := Dm.pubD.nsOf
  links := Dm.links
  nextOf := VerifiableInference.Desc.First.FillK4.nextOfPlan X
  d12 := E.d12
  D3 := Dm.sent
  L3 := Dm.l3
  d1 := Dm.d1
  free0 := E.dP.free0
  fvs := E.dP.fvs
  worthBase :=
    letI := VerifiableInference.OnPublicFiles.k3SizesAt X
    letI := VerifiableInference.OnPublicFiles.k3PolicyAt X
    (fillK3HeadG X Dm.sent Dm.l3 (VerifiableInference.OnPublicFiles.k3AdrAt X) Dm.rq
      (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells) Mg).worth
  moreL := (mgWide Dm E Mg).more
  sd := Dm.pubD.dS

/-- **UNDER hH, hP, hL: the 44 fields at the wider meaning as imported (a bridge's side).** -/
theorem k4Means_mgWide (hH : isLay Dm.links (headLink X) = false)
    (hP : ∀ q z s s', Mg.pubP q (z, s) → Mg.pubP q (z, s')) (hL : ∀ m j a, Mg.pubP (.lookIn m j) a)
    :
    K4Means (mgWide Dm E Mg) (k4DataWide Dm E Mg) where
  pin := rfl
  pinW := rfl
  constr := rfl
  decIs := rfl
  worth := by
    show (mgAll Dm Mg).worth = _
    rw [VerifiableInference.Desc.Sound.mgAll_worth]
    rfl
  formsT := rfl
  wo := rfl
  pile := rfl
  row := rfl
  decodes := rfl
  inOrder := fun _ => rfl
  held := rfl
  shown := rfl
  noColl := rfl
  more := rfl
  ledger := fun _ _ => rfl
  freeAbove := fun _ _ => rfl
  unheard := fun _ => rfl
  look := fun m' a hl => by
    change isLay Dm.links m' = true at hl
    have hne : (m' == headLink X) = false := by
      cases e : m' == headLink X with
      | false => rfl
      | true =>
        rw [beq_iff_eq.mp e, hH] at hl
        cases hl
    show (if m' == headLink X then _ else if isLay Dm.links m' then lookLayB a.2 else _) = _
    rw [hne, hl]
    rfl
  callerIn := fun m' a hl => by
    change isLay Dm.links m' = true at hl
    show (if isLay Dm.links m' then
      (VerifiableInference.Desc.First.FillK4.nextOfPlan X m').any fun n => callerInLayB n a.2
      else _) = _
    rw [hl]
    rfl
  weightsOk := fun _ => rfl
  bookInOrder := fun _ => rfl
  seatsCarried := fun _ => rfl
  msgShapes := fun _ => rfl
  bookFits := fun _ => rfl
  sentIs := fun m a => by
    rw [VerifiableInference.Desc.Sound.mgWide_pub,
      VerifiableInference.Desc.First.pubWide_hand _ _ _ _ _ rfl]
    exact VerifiableInference.Desc.First.pubAll_more_sentIs Dm.pubD Mg.pub m a
  treesAre := fun m a => by
    rw [VerifiableInference.Desc.Sound.mgWide_pub,
      VerifiableInference.Desc.First.pubWide_hand _ _ _ _ _ rfl]
    exact VerifiableInference.Desc.First.pubAll_more_treesAre Dm.pubD Mg.pub m a
  rowsBare := fun m a hl => by
    rw [VerifiableInference.Desc.Sound.mgWide_pub,
      VerifiableInference.Desc.First.pubWide_hand _ _ _ _ _ rfl]
    exact VerifiableInference.Desc.First.pubAll_more_rowsBare Dm.pubD Mg.pub m hl a
  lookLeft := fun m a hl => by
    rw [VerifiableInference.Desc.Sound.mgWide_pub,
      VerifiableInference.Desc.First.pubWide_hand _ _ _ _ _ rfl]
    exact VerifiableInference.Desc.First.pubAll_more_lookLeft Dm.pubD Mg.pub m hl a
  indexIs := fun _ => rfl
  indexThere := fun _ => rfl
  formsInT := fun _ _ _ _ => rfl
  hasRow := fun _ _ => rfl
  room := fun _ _ => rfl
  linkFresh := fun _ _ => rfl
  lookIn := fun m dg a => by
    show (match k3SortAt X m (VerifiableInference.Desc.K3.pieceAt X m dg) with
      | some dg => lookInC (K3Data.of X Dm.sent) m dg a.2
      | none => _) = _
    rw [sort_at]
    rfl
  lookOut := fun m dg a => by
    show (match k3SortAt X m (VerifiableInference.Desc.K3.pieceAt X m dg) with
      | some dg => lookOutC (K3Data.of X Dm.sent) m dg a.2
      | none => _) = _
    rw [sort_at]
    rfl
  liveIs := fun _ _ => rfl
  leftB := fun _ _ => rfl
  leftOnB := fun _ _ => rfl
  left := fun _ _ => rfl
  leftOn := fun _ _ => rfl
  pubPRides := fun q z s s' h1 h2 h => by
    cases q with
    | left m => exact absurd rfl (h1 m)
    | leftOn m => exact absurd rfl (h2 m)
    | _ =>
      first
        | exact hP _ z s s' h
        | trivial
  pubPLookIn := fun m j a => hL m j a

/-- **The five equations more, at the wider meaning.** -/
theorem k4Pile_mgWide : K4PileNames (mgWide Dm E Mg) E.dP.tl where
  pileMasks := fun _ => rfl
  pileWithin := fun _ => rfl
  oneRow := fun _ => rfl
  lay7 := fun _ _ => rfl
  funsThird := fun _ _ => rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4Means_mgWide
#print axioms OnBytes.Road.K4.k4Pile_mgWide
