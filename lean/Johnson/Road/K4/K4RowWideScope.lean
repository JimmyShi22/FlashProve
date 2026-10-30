-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RowWideScope.lean: K4's ROW AT THE TABLE OF JOINTS, ON THE SIDE OF THE PROMISE AND
OF WHAT RIDES, AT THE WIDER MEANING OVER THE CLOSED BASE (k4Row_wide,
Johnson/Road/K4/K4RowAtWide.lean), CALLED IN THE GOALS' SCOPE AT AN OPENING OF THE IOP AS WRITTEN IN
LEAN: what that theorem asks of the public parameters, of one value of the type Link and of eight
lines on the composed meaning's parameters Dm is paid here out of TWELVE LINES "THIS PARAMETER OF
Dm, OR OF THE WIDER MEANING's DATA E, IS THIS TERM". One structure, four statements with their
proofs: calls. The eighth line, head: hhead is
concluded from it. The ninth and tenth lines, on E's flags and count of free entries:
with them the named test room1 is a closed test. The eleventh and twelfth lines, on
E's planned data of the approximate range proof and on E.d12.ft: no statement here spends them: they
stand so that the wider meaning's tests at the names "K8.lay7" and K13's are not asked at a free
letter. THE TWELFTH FIXES A VALUE, 0, NOT A TERM: it is the premise under which another file
shows K13's structure at the wider meaning (fillsK13_mgWide, Johnson/Desc/Sound/MgAt/K13.lean);
that 0 is the value at the data that counts is shown by nobody. THE PUBLIC
PARAMETERS ARE A LETTER X WITH ONE PREMISE hX : Bs.G₀.W = X: the constant that is meant for Dm has
the index Z.p.X in its type, which is Bs.G₀.W by a theorem (IM.Open.W), not by unfolding.

  `K4Fill Dm E Z c`: the twelve lines: links is the written list linksFull · built is the public
    part's own list of built segments · d1 is d1At Z (Johnson/Top/H0/Fill/D1At.lean) · lk
    reads the first chain c's list of links · smp is the named reader of samples · the committed
    table's decoder reads no state of the verifier (NoRec) · H.req reads the public part alone ·
    headPart reads no string, and of the verifier's state the value of H.req and that of one more
    reader tokH, which rides inside a layers' segment · E.dP.fvs is D1At.lean's fvsAt Z · E.dP.free0
    is D1At.lean's free0Of at Dm's codes, E's list of shapes and the index masks' number · E.dP.tl
    is D1At.lean's tlAt Z · E.d12.ft is 0.
  `room1_of_fill`: in the goals' scope, at an opening, g < 12: the field room1 of K4NamedW at
    segment 2 g, out of 1 ≤ free0Of Dm.cs E.d12.M Dm.N.indexNo - g: the flags are no letter any
    more (rowsBefore_at, Johnson/Road/K4/Riders/BuiltFvs.lean).
  `hhead_of_fill`: the line head of the structure K4Reads (Johnson/Road/K4/K4Reads.lean) at Dm's
    headPart, out of the lines head and req: head_blind (Johnson/Road/K4/K4HeadBlind.lean).
  `k4OnD_of_fill`: ALL EIGHT FIELDS OF K4OnD at segment 2 g, at par := x.2 with k3Runs := true, at
    n := Forest.elems X.y.fo. Premises: the scope (hS, hR) · an opening O · g < 12 · hx, hl: x is
    the member of K4's lot's list that bears the number 2 g · Fl : K4Fill Dm E Z c.
  **`k4Row_wide_scope`**: K4Front ∧ K4Riders ∧ a place pl' with K4Keeps, all three at
    mgWide Dm E mgBase. PREMISES: those six · H : AtK4 at the written lists, at border k and place
    pl (a theorem elsewhere has it at 28 g + 4 and K4's address: atK4_full,
    Johnson/Road/K4/K04Tied.lean: not imported) · Sn : the nine named tests K4NamedW · hbase (one
    fact on the piece).
  PAID INSIDE: K4OnX's nine (k4OnX_of_scope) · K4OnD's eight · hhead · hH (the head's segment is
    24: no layers' segment of the written list) · Dm.lk (2 g) = some Lk and the five ties on Lk's
    sub-protocols (seats_at_open, at the same x by k04_sits_one).
Limits. THE WIDER MEANING IS A BRIDGE's SIDE, NOT THE MEANING THAT COUNTS: what is shown at it
counts only when the bridge's premises are paid. K4Fill IS SHOWN AT NO Dm; the nine tests and hbase
stand as premises; THEY ARE SHOWN TOGETHER NOWHERE. That there is an opening is shown by
no theorem. THE PROMISE's SIDE ALONE: what the claims that K4 opens are worth is not touched.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4RowAtWide
import Johnson.Road.K4.K4NextOfScope
import Johnson.Road.K4.K4HeadBlind
import Johnson.Road.K4.Riders.BuiltNcl
import Johnson.Road.K4.Riders.BuiltFvs
import Johnson.Road.K4.Riders.NsOfAtMgAll
import Johnson.Road.K4.Riders.OnXOfPlan
import Johnson.Road.K4.Riders.SeatsAtDesc
import Johnson.Top.H0.Fill.D1At

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4.Riders (built_ncl nsOf_mgAll k4OnX_of_scope seats_at_open rowsBefore_at)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Block FileDescription)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.FillP1 (d1At fvsAt free0Of)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open VerifiableInference.Desc.First.Look (Stored.NoRec)
open VerifiableInference.OnPublicFiles (LeftQ headLink)
open VerifiableInference.Desc.Sound (Frame Piece strsOf MsgT mgWide MgData WideData mgBase
  linksFull smpNamed)

variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}

/-- Twelve lines "this parameter of the composed meaning, or of the wider meaning's data, is this
term". -/
structure K4Fill (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P) (Z : ProofFile.Pub)
    (c : VerifiableInference.Desc.Chain S Claim) : Prop where
  links : Dm.links = linksFull
  built : Dm.built = Z.p.built.links
  d1 : Dm.d1 = d1At Z
  lk : Dm.lk = fun m => c.links[m]?
  smp : ∃ seats : List (ℕ × ℕ), Dm.smp = smpNamed Dm.cs seats
  dec : Stored.NoRec Dm.decT
  req : ∃ R : P → P5J.TReq, Dm.H.req = fun a => R a.1
  head : ∃ (T : Type)
    (Hp : P5J.TPart → IdxM → P5J.TReq → T → Wit (CellsK rows cols) Tok MsgT → Prop)
    (tokH : P × S → T), (Dm.headPart = fun p i a _ w => Hp p i (Dm.H.req a) (tokH a) w) ∧
      ∀ z s s', LayRest s s' → tokH (z, s) = tokH (z, s')
  fvs : E.dP.fvs = fvsAt Z
  free0 : E.dP.free0 = free0Of Dm.cs E.d12.M Dm.N.indexNo
  tl : E.dP.tl = VerifiableInference.Desc.First.FillP1.tlAt Z
  ft : E.d12.ft = 0

/-- **The line head at Dm's headPart, out of the lines head and req.** -/
theorem hhead_of_fill {Dm : MgData Xi P Tok rows cols nR X} {E : WideData P} {Z : ProofFile.Pub}
    {c : VerifiableInference.Desc.Chain S Claim} (Fl : K4Fill Dm E Z c) (z : P) (base : ℕ) :
    ∀ s s' (u v : Fr.E.Str), LayRest s s' → SameStr Fr base u v → ∀ p i w,
      Dm.headPart p i (z, s') (strsOf Fr v) w → Dm.headPart p i (z, s) (strsOf Fr u) w := by
  obtain ⟨R, hreq⟩ := Fl.req
  obtain ⟨T, Hp, tokH, hD, htok⟩ := Fl.head
  exact head_blind
    (D := k4DataWide Dm E (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))) z Fr base
    (Hp := Hp) (tokH := tokH) hD
    (req_pub (D := k4DataWide Dm E (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))) z
      (R := R) hreq)
    (htok z)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ} {x : Bool × Par}

/-- **All eight fields of K4OnD, out of the lines of K4Fill, in the goals' scope.** -/
theorem k4OnD_of_fill (Dm : MgData Xi P Tok rows cols nR X) {E : WideData P}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hX : Bs.G₀.W = X)
    (hg : g < 12)
    (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none) (hl : x.2.link = 2 * g)
    (Fl : K4Fill Dm E Z c) :
    K4OnD Dm (2 * g) { x.2 with k3Runs := true } (Forest.elems X.y.fo) := by
  subst hX
  have Sx := k4OnX_of_scope hS hR O hg hx hl
  have e7 : x.2.P = Bs.G₀.W.layers := by
    obtain ⟨_, _, y, _, _, e3, _, e5, _, e7, _⟩ := k4Of_of_open hS hR O g hg
    obtain rfl : x = y := k04_sits_one hx e3 hl e5
    exact e7
  have hlay : Dm.d1.lay = x.2.P.wsLay := by
    rw [Fl.d1, e7, O.W]
    rfl
  have hncl : Dm.d1.ncl (2 * g) = x.2.hp.NCL := by
    rw [Fl.d1]
    exact built_ncl hS hR O hg hx hl
  exact
    { links := Fl.links
      nextOf := nextOf_lay Sx.pubOf Sx.notHead Sx.step Sx.plan
      nsOf := nsOf_mgAll Dm hS hR O hg hx hl Fl.built
      lay := hlay
      ncl := hncl
      smp := Fl.smp
      dec := Fl.dec
      req := Fl.req }

/-- **The named test room1 at segment 2 g, out of a closed test.** -/
theorem room1_of_fill {Dm : MgData Xi P Tok rows cols nR X} {E : WideData P}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12)
    (Fl : K4Fill Dm E Z c) (h : 1 ≤ free0Of Dm.cs E.d12.M Dm.N.indexNo - g) :
    1 ≤ E.dP.free0 - rowsBefore E.dP.fvs (2 * g) := by
  rw [Fl.free0, Fl.fvs, rowsBefore_at hS hR O hg]
  exact h

variable {z : P} {k : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)}
  {told : List (List VerifiableInference.Desc.Oracle)}

/-- **UNDER THE SCOPE, AN OPENING, THE TWELVE LINES, H, THE NINE TESTS AND hbase (ALL PREMISES):
K4's row's three structures of lines, at the wider meaning over the closed base.** -/
theorem k4Row_wide_scope (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hX : Bs.G₀.W = X)
    (hg : g < 12)
    (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none) (hl : x.2.link = 2 * g)
    (Fl : K4Fill Dm E Z c) (H : AtK4 linksFull (flatPlacesOf linksFull true) k (2 * g) pl)
    (Sn : K4NamedW Dm E k (2 * g) { x.2 with k3Runs := true } told (Forest.elems X.y.fo))
    (hbase : Dm.N.treesAt (some pl) = q.base) :
    K4Front (mgWide Dm E (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))) z linksFull
        (flatPlacesOf linksFull true) (2 * g) X.y.fo X.y.h.lmb 0 (LeftQ x.2.hp.ns) ∧
      K4Riders Dm.N (mgWide Dm E (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))) z
        linksFull (flatPlacesOf linksFull true) k (2 * g) q { x.2 with k3Runs := true } ∧
      ∃ pl', K4Keeps Dm.N
        (mgWide Dm E (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))) z linksFull
        (flatPlacesOf linksFull true) k (2 * g) pl pl' q { x.2 with k3Runs := true } := by
  subst hX
  obtain ⟨k4, kN, _⟩ := Meaning.scope_plans hS hR O.public
  obtain ⟨Lk, x', e1, e3, e5, st, runO, runG, fO, oRun, fG, gRun⟩ := seats_at_open hS hR O hg
  obtain rfl : x = x' := k04_sits_one hx e3 hl e5
  have hH : isLay Dm.links (headLink Bs.G₀.W) = false := by
    rw [Fl.links]
    unfold headLink
    rw [k4, kN, if_pos rfl]
    decide +kernel
  have hlk : Dm.lk (2 * g) = some Lk := by
    rw [Fl.lk]
    exact e1
  exact k4Row_wide Dm E hH H (k4OnX_of_scope hS hR O hg hx hl)
    (k4OnD_of_fill Dm hS hR O rfl hg hx hl Fl) Sn (hhead_of_fill Fl z q.base) hbase hlk st fO oRun
    fG gRun

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hhead_of_fill
#print axioms OnBytes.Road.K4.k4OnD_of_fill
#print axioms OnBytes.Road.K4.room1_of_fill
#print axioms OnBytes.Road.K4.k4Row_wide_scope
