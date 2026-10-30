-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.ProofFile.Lot.K12
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.IMR.BackSeat
/-
H2K12/K12RowAlone.lean: THE PROXIMITY TEST's (the
kind K12's) ROW AMONG THE ROWS THAT "the proof file's description returns, with its cut" WANTS OF
EACH LOT OF SUB-PROTOCOLS: THE FIRST CHAIN's ONE SUB-PROTOCOL, number 354 of the written cut: THE
GENERAL HALF AND THE CLOSED HALF. What the row asks of a lot: (i) it returns its sub-protocols; (ii)
at its places the cut's rows are the written ones (Johnson/Desc/Ok/PlanWritten/CutLit.lean); (iii)
each sub-protocol's test on the plan says yes.
  k12_own          (i): the lot's list is one sub-protocol, atFinish at the numbers that
                   H2U.p12OfMade makes of the plan: by the lot's text. k12_blocks: the like of
                   Lot.blocks, through which the chain reads a lot. THEY SAY LITTLE: A LOT's LIST
                   CANNOT REFUSE: where the plan gives no numbers p12OfMade falls to H2U.noP12
  k12_row_alone    the cut's row of a sub-protocol b that is the lot's, laid alone under a spot's
                   name at an address (IM.LaidAlone, Johnson/IMR/SeatForm.lean): the name and the
                   address are the seat's letters; the four other columns are terms off the kind's
                   own sub-protocol at p. General in p; nothing is evaluated. In the form of the
                   row for K4 in other files
  k12_planOk_alone b's test on the plan is that of the lot's sub-protocol. k12_bare_alone: b has
                   neither claims nor runs behind a batching: so the flat list's "and it is bare"
                   (Chain.blocksInOrder, Johnson/Desc/Block.lean) adds nothing
  rowL_full        at the written member piLFull (Johnson/Desc/K12/Law/PlacesFull.lean): the written
                   cut's row number 354 is ("F:2", the member's place, these four columns). From
                   rowL_fullB: the cut's own test on two rows (sameRow,
                   Johnson/Desc/Ok/PlanWritten/CutTest.lean) says yes: by the kernel. rowL_fullB_no:
                   of row number 353 it says no
  rowL_own_no      the lot's sub-protocol's own whole row at piLFull is NOT the written row number
                   354: the cut's own test on two lists of rows says no. By the kernel. (With
                   rowL_full: it is the names that part them.)
  planL_full       at piLFull the lot's sub-protocol's test on the plan says yes. By the kernel.
                   planL_full_no: with the list idx one entry shorter it says no
  k12_row_at       (ii) AND (iii) AT A PUBLIC PART Z, OF b AS IT STANDS IN THE FLAT LIST, FROM FOUR
                   PREMISES, BY NAME: hV : H2U.p12OfMade Z.made = piLFull; la: b is the lot's
                   sub-protocol laid alone under name at a; hn, ha: the name is "F:2" and the
                   address ⟨1, none, 2, K12⟩: there is y, the written cut's row number 354, that is
                   the one row of the cut of b with "and it is bare"; and that sub-protocol's test
                   on the plan says yes
  k12_row_open     THE SAME AT NUMBER 354 OF THE FIRST CHAIN's FLAT LIST: in scope, under an opening
                   of the files (IM.Open, Johnson/IMR/SeatOpen.lean), from hV and hn (of the
                   sub-protocol at c.back[1]): (cutOf c.blocksInOrder)[354]? is the written cut's row number
                   354, and the sub-protocol there says yes on the plan. The seat's form and the
                   number are other files' theorems, called: IM.back_of, IM.back_numbers
                   (Johnson/IMR/BackSeat.lean)
WHAT IS LEFT BEHIND THIS FILE: hV IS THE LOT's WHOLE DEBT: that the numbers which the plan gives at
Z are the written member is shown NOWHERE here, and by PlacesFull.lean's own head by no theorem: the
member was made by a program off a run's print. The name's column is not this lot's to pay
(rowL_own_no): by report it is the spots'.
WHAT IT IS NOT: the three sub-protocols of the kind on the two later chains are not here.
k12_row_open stands under an opening: it does not say that the files can be opened; and an opening
holds every step of the description's return: so that theorem serves the cut and the tests on the
plan, which speak of the description once returned, NOT the return itself. The full size alone. No
soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Block Place KindName Oracle Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts atFinish)
open VerifiableInference.PlanWritten (cutOf toldRounds cutFirstFull sameRow sameRows sameRow_iff
  row_at)
open H2K.Member (piLFull)

/-- The kind's own sub-protocol at p. -/
abbrev kB (p : P12) : Block T12 Unit := proximityTestKind guardedProximityTestParts p

/-- The lot's sub-protocol at p, carried over to the fold's claims. -/
abbrev lotB (p : P12) : Block S ProofFile.Cl := (atFinish p).retype

/-- A sub-protocol outside the links as `Chain.blocksInOrder` lays it. -/
abbrev bareOf (b : Block S ProofFile.Cl) : Block S ProofFile.Cl := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

/-- The four columns of the cut's row that are the lot's to pay. -/
def colsOf (p : P12) : Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat) :=
  ((kB p).rounds.length, (kB p).oracles.length, toldRounds (kB p), (kB p).before)

/-- **(i)** -/
theorem k12_own (Z : ProofFile.Pub) (g : ProofFile.Ground) :
    (VerifiableInference.Desc.K12.lot Z).own g = [atFinish (H2U.p12OfMade Z.made)] := rfl

theorem k12_blocks (Z : ProofFile.Pub) (g : ProofFile.Ground) :
    (VerifiableInference.Desc.K12.lot Z).blocks g = [lotB (H2U.p12OfMade Z.made)] := rfl

section
variable {same : S → S → Bool} {b : Block S ProofFile.Cl} {name : String} {a : Place} {p : P12}

/-- **The cut's row of the lot's sub-protocol as it stands in the chain.** -/
theorem k12_row_alone (la : IM.LaidAlone same b (lotB p) name a) :
    cutOf [b] = [(name, a, colsOf p)] := by
  subst la
  rfl

theorem k12_planOk_alone (la : IM.LaidAlone same b (lotB p) name a) :
    b.planOk = (lotB p).planOk := IM.alone_planOk la

theorem k12_bare_alone (la : IM.LaidAlone same b (lotB p) name a) : b.hasNoClaimsAndNothingAfter = true := by
  subst la
  rfl

end

/-- **The written cut's row number 354 at the written member**: by the cut's own test on two
rows. -/
theorem rowL_fullB : (cutFirstFull[354]?).any
    (fun y => sameRow y ("F:2", piLFull.place, colsOf piLFull)) = true := by decide +kernel

theorem rowL_fullB_no : (cutFirstFull[353]?).any
    (fun y => !sameRow y ("F:2", piLFull.place, colsOf piLFull)) = true := by decide +kernel

/-- The written row, whole. -/
theorem rowL_full : cutFirstFull[354]? = some ("F:2", piLFull.place, colsOf piLFull) := by
  have h := rowL_fullB
  cases e : cutFirstFull[354]? with
  | none =>
    rw [e] at h
    exact absurd h (by simp)
  | some y =>
    rw [e] at h
    exact congrArg some ((sameRow_iff _ _).1 h)

/-- **The lot's sub-protocol's OWN row is NOT the written one**, by the cut's own test on two lists
of rows: it bears the kind's name for itself; the written row bears another ("F:2"). So this lot
does not pay the column of names. -/
theorem rowL_own_no : (cutFirstFull[354]?).any
    (fun y => !sameRows (cutOf [lotB piLFull]) [y]) = true := by decide +kernel

/-- **The test on the plan at the written member.** -/
theorem planL_full : (lotB piLFull).planOk = true := by decide +kernel

theorem planL_full_no : (lotB { piLFull with idx := piLFull.idx.dropLast }).planOk = false := by
  decide +kernel

/-- **(ii) AND (iii) AT Z, FROM "THE PLAN's NUMBERS ARE THE WRITTEN MEMBER".** -/
theorem k12_row_at {same : S → S → Bool} {b : Block S ProofFile.Cl} {name : String} {a : Place}
    (Z : ProofFile.Pub) (hV : H2U.p12OfMade Z.made = piLFull)
    (la : IM.LaidAlone same b (lotB (H2U.p12OfMade Z.made)) name a) (hn : name = "F:2")
    (ha : a = ⟨1, none, 2, .K12⟩) :
    (∃ y, cutFirstFull[354]? = some y ∧ cutOf [bareOf b] = [y]) ∧ (bareOf b).planOk = true := by
  rw [hV] at la
  refine ⟨⟨_, rowL_full, ?_⟩, ?_⟩
  · have h : cutOf [bareOf b] = cutOf [b] := rfl
    rw [h, k12_row_alone la, hn, ha]
    rfl
  · show (b.planOk && b.hasNoClaimsAndNothingAfter) = true
    rw [k12_planOk_alone la, planL_full, k12_bare_alone la]
    rfl

/-- **(ii) AND (iii) AT NUMBER 354 OF THE FIRST CHAIN's FLAT LIST, UNDER AN OPENING.** -/
theorem k12_row_open {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hV : H2U.p12OfMade Z.made = piLFull)
    (hn : ∀ b, c.back[1]? = some b → b.name = "F:2") :
    (∃ y, cutFirstFull[354]? = some y ∧ (cutOf c.blocksInOrder)[354]? = some y) ∧
      ∃ b, c.blocksInOrder[354]? = some b ∧ b.planOk = true := by
  obtain ⟨_, ⟨b, b', hb, _, rfl, la⟩, _⟩ := IM.back_of O
  have h354 : c.blocksInOrder[354]? = some (bareOf b) := (IM.back_numbers hS hR O).1 1 b hb
  obtain ⟨⟨y, hy, hc⟩, hp⟩ := k12_row_at Z hV la (hn b hb) rfl
  refine ⟨⟨y, hy, ?_⟩, _, h354, hp⟩
  have hc' : [((bareOf b).name, (bareOf b).place, (bareOf b).rounds.length,
      (bareOf b).oracles.length, toldRounds (bareOf b), (bareOf b).before)] = [y] := hc
  rw [row_at, h354]
  exact congrArg some (List.cons.inj hc').1

end H2K12

#print axioms H2K12.k12_own
#print axioms H2K12.k12_blocks
#print axioms H2K12.k12_row_alone
#print axioms H2K12.k12_planOk_alone
#print axioms H2K12.k12_bare_alone
#print axioms H2K12.rowL_fullB
#print axioms H2K12.rowL_fullB_no
#print axioms H2K12.rowL_full
#print axioms H2K12.rowL_own_no
#print axioms H2K12.planL_full
#print axioms H2K12.planL_full_no
#print axioms H2K12.k12_row_at
#print axioms H2K12.k12_row_open
