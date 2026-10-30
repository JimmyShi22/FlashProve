-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanLoc.lean: the rounds «LOC» of a proof file, a key file and an entry file, which
draw positions alone, AS FUNCTIONS OF THE PLANS' OWN ENTRIES AND OF THE PLANNER's RECORDS, at a rule
for the links' radii and a handed radius for the tables; and one test whose yes gives, at every
entry «LOC» of the seven plans, that the count of Johnson/Bridge/LocAtWritten.lean is at most 2^-128
of the verifier messages of every written round with that entry (of a kind other than seeds and
sealed). No numeral of a plan is written here.

Arithmetic: no statement on codes is used in this file's own proofs. Through its imports the file
stands above Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from
ArkLib and Mathlib (lean/LIMITS.md,
L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions with code, and statements that follow from `PosPlace.below`
(Johnson/Bridge/LocAtWritten.lean).

Main names:
  `PosPlace.of e r`: the place of an entry: length, draws and bits of work off the entry; the radius
    handed. `locB e r`: the entry draws positions alone, and the place's comparison says yes.
  `locB_below`: a yes gives the clause `RoundBelow` in every written round with that entry (of a
    kind other than seeds and sealed).
  `locsOf P`: a plan's entries «LOC».
  `opened z`: the records of the groups of a proof file's first chain but the first: at each the
    group of the link that was closed last is opened (`FrameN.before`, OnBytes/Plan/ReqFrames.lean).
  `linkLocs M`: the entries «LOC» of the first chain's plan, each with the record of its number.
  `tableLocs M`: the entries «LOC» of the six other plans.
  `planLocs ρ rT M`: all of them, each with its radius: the rule's at the opened group, or rT.
  `planLocB ρ rT M`: THE TEST: as many entries «LOC» in the first chain's plan as records; each
    entry's length and draws are its record's; `locB` at every entry of the seven plans.
  `planLocB_below`, `planLocB_fits`: what its yes gives.

Limits: THE RADII ARE WHATEVER THE RULE AND THE CALLER SAY: no statement here ties them to a
protocol, and rT is one number for every entry «LOC» outside the first chain's plan. A LARGER RADIUS
MAKES THE COUNT SMALLER, AND THE TEST BOUNDS NO RADIUS FROM ABOVE: at a radius of the length or more
the count is 0 and the test says yes. What bounds the rule's radii from above is `planTestsB` at the
same rule (Johnson/Bridge/PlanTests.lean); nothing here or there bounds rT:
Johnson/Bridge/PlanTables.lean does. Of the 128 bits the entry's bits of work are proof of work (the
head of Johnson/Bridge/LocAtWritten.lean has their numbers at two sizes). THAT THE COUNT IS A
BLOCK's IS NOT SAID HERE (the Limits of Johnson/Bridge/LocAtWritten.lean). WHICH ENTRY BELONGS TO
WHICH RECORD IS BY ORDER ALONE; the test holds each entry's length and draws against its record,
which does not tell records of one size apart. That the first of a proof's plans is the first
chain's is by the order in which `Params.proofPlans` lays them, by reading. How many entries «LOC»
the six other plans hold is not asked: with none the test says yes of them
(Johnson/Bridge/PlanTables.lean asks for two). How many plans the records hold is not asked. That
the records and plans are those of a file's public files is asked where they are made. That the
rounds of a plan are rounds of the description of the protocol that a verifier runs is not said
here. The rounds «SEND seed» (those in front of the links' rounds «LOC» among them) and the entry
file's round «LINK» are not here. The test has been EVALUATED at stored sets of public files by a
sheet that is not in this repository; no theorem says that it says yes at any plan. No sum over
rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.PlanTests
import Johnson.Bridge.LocAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Plan Johnson.Top.H Cb _root_.Run
open scoped ENNReal

/-- The place of an entry: length, draws and work off the entry; the radius handed. -/
def PosPlace.of (e : Fmt.Entry) (r : ℕ) : PosPlace := ⟨e.logN, e.poss, r, e.work⟩

/-- The entry draws positions alone, and the place's comparison says yes. -/
def locB (e : Fmt.Entry) (r : ℕ) : Bool :=
  Nat.beq e.drawE 0 && Nat.beq e.drawNZ 0 && Nat.beq e.trits 0 && (PosPlace.of e r).priced

/-- **A yes: the count against 2^-128**, in every written round with that entry (of a kind other
than seeds and sealed). -/
theorem locB_below {e : Fmt.Entry} {r : ℕ} (h : locB e r = true) (d : PQ.RD) (hd : d.entry = e)
    (hk1 : d.kind ≠ .seeds) (hk2 : d.kind ≠ .sealed) :
    RoundBelow (PosPlace.of e r).cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  subst hd
  simp only [locB, Bool.and_eq_true] at h
  exact PosPlace.below h.2 d (Nat.eq_of_beq_eq_true h.1.1.1) (Nat.eq_of_beq_eq_true h.1.1.2)
    (Nat.eq_of_beq_eq_true h.1.2) rfl rfl rfl hk1 hk2

/-- A plan's entries «LOC». -/
def locsOf (P : Planned) : List Fmt.Entry := P.plan.entries.filter fun e => e.name == "LOC"

/-- The records of the groups of a proof file's first chain but the first. -/
def opened (z : ProofSized) : List FrameN :=
  (framesFrom z 0 (reqGroups z.request).toList z.request.link [] z.link.group).filter
    fun n => n.l != 0

/-- The entries «LOC» of the first chain's plan, each with the record of its number. -/
def linkLocs (M : Configured) : List (Fmt.Entry × FrameN) :=
  ((M.proof.take 1).flatMap locsOf).zip (opened M.sized.proof)

/-- The entries «LOC» of the six other plans. -/
def tableLocs (M : Configured) : List Fmt.Entry :=
  (M.proof.drop 1 ++ M.key ++ [M.entry]).flatMap locsOf

/-- **Every entry «LOC»**, with its radius. -/
def planLocs (ρ : Rad) (rT : ℕ) (M : Configured) : List (Fmt.Entry × ℕ) :=
  (linkLocs M).map (fun p => (p.1, ρ M.sized.proof.set p.2.before M.sized.proof.link.t)) ++
    (tableLocs M).map fun e => (e, rT)

/-- **The test on the plans' entries and the planner's records.** -/
def planLocB (ρ : Rad) (rT : ℕ) (M : Configured) : Bool :=
  Nat.beq ((M.proof.take 1).flatMap locsOf).length (opened M.sized.proof).length &&
    ((linkLocs M).all fun p =>
      Nat.beq p.1.logN p.2.before.main.logN && Nat.beq p.1.poss M.sized.proof.link.t) &&
    ((planLocs ρ rT M).all fun p => locB p.1 p.2)

/-- **A yes of the test: at every entry «LOC» the count is at most 2^-128 of the round's written
verifier messages**, at its radius. -/
theorem planLocB_below {ρ : Rad} {rT : ℕ} {M : Configured} (h : planLocB ρ rT M = true) :
    ∀ p ∈ planLocs ρ rT M, ∀ d : PQ.RD, d.entry = p.1 → d.kind ≠ .seeds → d.kind ≠ .sealed →
      RoundBelow (PosPlace.of p.1 p.2).cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128) := fun p hp d =>
  locB_below (List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 p hp) d

/-- **A yes of the test: no entry of the first chain's plan is left over, and each has the length
and the draws of its record.** -/
theorem planLocB_fits {ρ : Rad} {rT : ℕ} {M : Configured} (h : planLocB ρ rT M = true) :
    ((M.proof.take 1).flatMap locsOf).length = (opened M.sized.proof).length ∧
      ∀ p ∈ linkLocs M, p.1.logN = p.2.before.main.logN ∧ p.1.poss = M.sized.proof.link.t := by
  simp only [planLocB, Bool.and_eq_true] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1.1, fun p hp => ?_⟩
  have := List.all_eq_true.1 h.1.2 p hp
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

end Johnson.Bridge

#print axioms Johnson.Bridge.locB_below
#print axioms Johnson.Bridge.planLocB_below
#print axioms Johnson.Bridge.planLocB_fits
