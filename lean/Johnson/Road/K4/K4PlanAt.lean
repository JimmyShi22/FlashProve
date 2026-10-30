-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanAt.lean: THE TESTS OF Johnson/Road/K4/K4PlanTests.lean AND
K4PlanTestsFirst.lean WITH SEVEN OF THEIR FREE LETTERS (D, seatT, num, arr, L, N, n) FILLED BY TERMS
OFF THE PUBLIC PARAMETERS Z, and hEnd paid. EACH TERM IS
SPELLED AS THE COMPOSED MEANING's CLOSED CONSTANT SPELLS ITS FIELD (Johnson/P5J/LettersAt.lean,
Rad3Seat3At.lean), so that the two are one by unfolding; this file does not import these: their
closure is heavy. Nine definitions with code and three theorems. Glue: calls; no draw, no count.

  `sentAt Z`: what the lookup's caller reads: THE FIRST CHAIN's PARAMETERS' codes, the request's
    shape, the layout, the built links' lists of arrays.
  `seatsAt Z` := planSeats Z Z.D.1 · `allSeatsAt Z` := planSeatsAll Z Z.D
    (Johnson/P5T/PlanSeats.lean).
  `arrAt Z` := arrOf (allSeatsAt Z) · `numAt Z` := numOfPlan (allSeatsAt Z): over all three chains'
    seats (Johnson/P5T/NumOfPlan.lean).
  `numbersAt Z` := numbersOf (seatsAt Z) (Johnson/P5T/NumbersOf.lean).
  `lists0At Z`: THE MEMBERS' LISTS BY THE MAKE OFF THE PLAN's SEATS (`memberListsR`,
    Johnson/P5T/MembersByMake.lean) AT THE RADII 0: no raw file is read a second time.
  `seatTAt Z rad l` := the lookup's authors' seatCallsT: the seat BY ROLE of a member of the
    caller's list (Johnson/P5T/SeatsAt.lean).
  `lastAt Z`: the number of the request's groups.

  `shapesTied_of_table`: `ShapesTied` from `shapesTiedB` at a table of the 25 groups that is laid
    once.
  `k4PlanFit_at`, `k4PlanFitF_at`: `K4PlanFit`, `K4PlanFitF` from the tests at these letters, ENDING
    AT ms := P5T.msAtR Z radM FOR EVERY FAMILY radM OF THE MEMBERS' RADII AND AT EVERY N' WITH
    numbersAt Z's sent AND index (Johnson/Road/K4/K4PlanCarry.lean); hEnd paid by `groups_end`.

Limits. K04_law IS NOT PROVED BY THIS. NO RUN IS A PART OF THIS FILE. THAT THESE ARE THE CLOSED
CONSTANT's FIELDS IS MEANT TO HOLD BY UNFOLDING AND IS SHOWN IN NO FILE. FREE: the place x
and the parameters p of K4's sub-protocol, the caller's radii rad, and posI, oW, enc, wOf:
Johnson/Road/K4/K4PlanClosed.lean closes these. The composed meaning's H has the seats `seatsOf X
(sizesOf X) layout num`: in the goals' scope these are `seatBy (fLay layout num) X (sizesOf X)` by
`seatsOf_is_seatBy`: not called here.
-/
import Johnson.Road.K4.K4PlanCarry
import Johnson.Road.K4.GroupsEnd
import Johnson.P5T.ArrAll
import Johnson.P5T.SeatsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (MemberLists)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf pubAt stepOf)
open VerifiableInference.Desc.Sound (msOf)
open Johnson.Road.K4.LayoutTies (shapesTiedB shapesTied_of_B)
open Meaning (ShapesTied seatBy fLay)
open Inst.Model.Layout (kRef hRef)

/-! ## The letters -/

/-- What the lookup's caller reads beside the public parameters. -/
def sentAt (Z : ProofFile.Pub) : Sent :=
  ⟨Z.made.p.chains.proof.first.codes, Z.made.p.chains.proof.first.shape,
    Z.made.p.chains.proof.first.layout, Z.made.p.built.links.map (·.arrayOf)⟩

/-- The first chain's seats. -/
def seatsAt (Z : ProofFile.Pub) : List P5T.PSeat := P5T.planSeats Z Z.D.1

/-- All three chains' seats. -/
def allSeatsAt (Z : ProofFile.Pub) : List P5T.PSeat := P5T.planSeatsAll Z Z.D

def arrAt (Z : ProofFile.Pub) : ℕ → ℕ → ℕ := P5T.arrOf (allSeatsAt Z)

def numAt (Z : ProofFile.Pub) : ℕ → ℕ → ℕ := P5T.numOfPlan (allSeatsAt Z)

def numbersAt (Z : ProofFile.Pub) : Numbers := P5T.numbersOf (seatsAt Z)

/-- The members' lists by the make off the plan's seats, at the radii 0. -/
def lists0At (Z : ProofFile.Pub) : MemberLists :=
  P5T.memberListsR Z.made.proof.1.sends.length (fun _ _ => 0) (seatsAt Z)

/-- The seat by role of a member of the caller's list at link l. -/
def seatTAt (Z : ProofFile.Pub) (rad : OnBytes.OracleShape → ℕ) (l : ℕ) :
    Fin (sigListCalls (sentAt Z) rad l).length → ℕ × ℕ :=
  fun j => P6T.seatCallsT (seatsAt Z) (sentAt Z) l j.val

/-- The number of the request's groups. -/
def lastAt (Z : ProofFile.Pub) : ℕ := (OnBytes.reqGroups Z.first.shape).toList.length

/-! ## A small law on one test -/

/-- **The tie of letters from the test at a table of the 25 groups that is laid once.** -/
theorem shapesTied_of_table {codes : Codes} {shape : Params.ReqShape} {layout : Params.ReqLayout}
    {num arr : ℕ → ℕ → ℕ} {L : MemberLists} {N : Numbers} (tbl : List (List (ℕ × ℕ)))
    (ht : tbl = (List.range 25).map fun k => N.group k)
    (h : shapesTiedB codes shape layout num arr L (fun k => tbl.getD k []) = true) :
    ShapesTied codes shape layout num arr (msOf L) fun k => N.group k := by
  intro l as A m hl hA hm k hk y hy hg hn
  refine shapesTied_of_B h l as A m hl hA hm k hk y hy ?_ hn
  subst ht
  show VerifiableInference.Desc.Sound.seatOf y ∈ ((List.range 25).map fun k => N.group k).getD k []
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simpa using hg

/-! ## At the letters -/

variable {rows cols : ℕ} {posI : ℕ → Bool × ℕ × ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {m : ℕ}

/-- **`K4PlanFit` at the makers' letters**: from the eleven tests there; at every family of the
members' radii and every N' with the same sent and index; no premise on the groups beyond the
last. -/
theorem k4PlanFit_at {pol KL : ByteArray} {tk : Array Nat} (Z : ProofFile.Pub) (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    {p : Par} {x : VerifiableInference.Desc.First.Look.Place} {rad : OnBytes.OracleShape → ℕ}
    {enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg} (hd : ℕ)
    (T : K4PlanTests (X := Z.p.X) (p := p) x (sentAt Z) rad (seatTAt Z rad x.link) posI oW enc wOf
      (numAt Z) (arrAt Z) (lists0At Z) (numbersAt Z) m (lastAt Z))
    (hg0 : 0 < p.g) (St : PublicSteps pol KL Z.p.X) (B : RefPub Z.p.X p.g)
    (hP : p.P = { Z.p.X.layers with tokv := tk }) (hG : Z.p.X.G[p.g]? = some p.hp)
    (hg : p.g < 12) (P0 : PlaceIs x p 0) (hgr : m / stepOf Z.p.X = p.g) (hm : m = 2 * p.g)
    (hhd : m ≠ hd) :
    K4PlanFit (X := Z.p.X) (p := p) x (pubAt Z.p.X (m / stepOf Z.p.X)) (sentAt Z) rad
      (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z) (P5T.msAtR Z radM) N' m
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) hd :=
  planFit_carry (samePairs_R _ _ radM _) hs hi
    (k4PlanFit_of_tests hd T (groups_end Z Z.D.1) hg0 St B hP hG hg P0 hgr hm hhd)

/-- **`K4PlanFitF` at the makers' letters**: from the two tests there. -/
theorem k4PlanFitF_at {pol KL : ByteArray} {tk : Array Nat} (Z : ProofFile.Pub) (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    {p : Par} {x : VerifiableInference.Desc.First.Look.Place} {rad : OnBytes.OracleShape → ℕ}
    {enc : (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) → oW.Msg} (hd : ℕ)
    (T : K4PlanTestsF (X := Z.p.X) (p := p) x (sentAt Z) rad (seatTAt Z rad x.link) posI oW enc wOf
      (numAt Z) (arrAt Z) (msOf (lists0At Z)) (numbersAt Z) m)
    (St : PublicSteps pol KL Z.p.X) (B : RefPub Z.p.X p.g)
    (hP : p.P = { Z.p.X.layers with tokv := tk }) (hG : Z.p.X.G[p.g]? = some p.hp)
    (hg : p.g < 12) (P0 : PlaceIs x p 0) (hgr : m / stepOf Z.p.X = p.g) (hm : m = 2 * p.g)
    (hhd : m ≠ hd) :
    K4PlanFitF (X := Z.p.X) (p := p) x (pubAt Z.p.X (m / stepOf Z.p.X)) (sentAt Z) rad
      (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z) (P5T.msAtR Z radM) N' m
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) hd :=
  planFitF_carry (samePairs_R _ _ radM _) hs hi
    (k4PlanFitF_of_tests hd T St B hP hG hg P0 hgr hm hhd)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.shapesTied_of_table
#print axioms OnBytes.Road.K4.k4PlanFit_at
#print axioms OnBytes.Road.K4.k4PlanFitF_at
