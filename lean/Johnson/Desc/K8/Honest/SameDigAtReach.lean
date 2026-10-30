-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/SameDigAtReach.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: IN FRONT
OF EACH OF THE 25 BATCHINGS THE STATE's DATA OF THE TEST AGREE, IN THE SIX FIELDS THAT THE LOOKUP ON
THE DIGITS READS (`SameDig`, Johnson/Desc/First/Look/K3DigRows.lean), WITH THE DATA THAT THE READER
OF THE DIGITS' PLACE MAKES (`Look.digAt`, Johnson/Desc/First/Look/K3CallerTests.lean); AND THE
PLACE's FIRST SLOT IS THE NEXT SLOT OF THAT PLACE's LEDGER: IN THE GOALS' SCOPE, THE FILES READ,
UNDER AN OPENING OF THE DESCRIPTION, AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH THERE.
THAT ANY SUCH STATE IS REACHED IS NOT SHOWN. A definition and lemmas; none of the library's goals.

  `digFields tl`, `planned_digFields` the data with all but ix, mz, tau, z1, z2 at their defaults; a
                   reading of planned fields (LinkJoin.Planned,
                   Johnson/Desc/First/Link/Law/PlannedAtDraw.lean): none of the five is a field that
                   a block of the segment writes
  `planned_at_all` the scope · the files read · the opening · l < 25 · the built segment Xl · Reach
                   0 c.blocksInOrder (ProofFile.startS Z) (14 l + (if l = 24 then 11 else 9)) (z, s) · s.tl? = some
                   tl ⊢ g tl = g Xl.tl, at every planned reading g
  **`sameDig_at_all`** these · Look.digAt Bs.G₀.W l = some (xx, tlD) ⊢ SameDig tlD tl ∧ ∀ P',
                   placeAt Bs.G₀.W l true = some P' → P'.first = xx.F.next
By: LinkJoin.planned_at_batch · `planned_heldFields` (HeldPublic.lean), for f9 · `tlAt_at_built`,
`shape_at_built` (LeftAtReach.lean) · the text of `Look.digAt`: the plan's data with f9 laid anew
off the place's own shape · the text of `placeAt` and of `Look.P.ofPlace`.
KIN IN THE LIBRARY: `SameDig` is a premise wherever the library takes it at a state ("STAYS A
PREMISE", Johnson/P5T/DigFiveAtMg.lean); as an end by that word it stands once, at data against
themselves with four fields written (K3DigRows.lean); THE NEAREST KIN: it is the first field of
`DigStatic`, which P5J.AtMg.k9_ground (Johnson/P5T/K9AtMg.lean) concludes AT THE BUILT SEGMENT's
data, under the public test k9Entry, at the other text of the reader: here without that test, at the
state. shape_of_dig (Johnson/LPFE1R/ShapeOfDig.lean) has the clause on f9 at the other text of the
reader (K3Asks.digAt); its proof's first steps are WRITTEN A FURTHER TIME here. `planned_at_all`
gathers what `left_at_batch` (LeftAtReach.lean) and `digitsLeft_at_head_seg`
(AllFrontAtHeadSeg.lean: a file that the library may not hold) do each at one reading.
No option is raised and no instance is taken away. TACTICS THAT SEARCH: `omega` on one line, behind
a `split`, on a sum of numbers of blocks.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED: where none is, all is idle. At Bs.G₀.W: that this is
the public data under another name is not said. IN SCOPE ALONE: the full size; the first chain; at
OnBytes.secondHashFunction. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.LeftAtReach
import Johnson.Desc.First.Look.K3DigRows
import Johnson.Desc.First.Look.K3CallerTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (SameDig)
open VerifiableInference.Desc.First.Look (placeAt)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The data with all but five fields at their defaults. -/
def digFields (tl : HTailF2) : HTailF2 :=
  { ix := tl.ix, mz := tl.mz, tau := tl.tau, z1 := tl.z1, z2 := tl.z2 }

/-- A reading of planned fields. -/
theorem planned_digFields : LinkJoin.Planned digFields :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In front of each of the 25 batchings a planned reading of the test's data is the built
segment's. -/
theorem planned_at_all {α : Type} {g : HTailF2 → α} (hg : LinkJoin.Planned g)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : g tl = g Xl.tl := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
        14 * l + (if l = 24 then 11 else 9) := by
      split <;> omega
    rw [e]
    exact h
  exact LinkJoin.of_readTl (LinkJoin.planned_at_batch hg hS hR O hx e3 (z, s) h') tl ht

/-- **IN FRONT OF EACH OF THE 25 BATCHINGS THE STATE's DATA OF THE TEST AGREE WITH THE DATA THAT
THE READER OF THE DIGITS' PLACE MAKES, IN THE SIX FIELDS; AND THE PLACE's FIRST SLOT IS THAT
PLACE's LEDGER's NEXT.** -/
theorem sameDig_at_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) {xx : Look.Place} {tlD : HTailF2}
    (hd : Look.digAt Bs.G₀.W l = some (xx, tlD)) :
    SameDig tlD tl ∧ ∀ P', placeAt Bs.G₀.W l true = some P' → P'.first = xx.F.next := by
  have v := planned_at_all planned_digFields hS hR O hl e3 h ht
  have w := planned_at_all planned_heldFields hS hR O hl e3 h ht
  unfold Look.digAt at hd
  obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 hd
  obtain ⟨tl0, h0, h3⟩ := Option.bind_eq_some_iff.1 h2
  obtain ⟨sh, hsh, h4⟩ := Option.map_eq_some_iff.1 h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
  obtain rfl : Xl.tl = tl0 :=
    Option.some.inj ((tlAt_at_built hS hR O hl e3).symm.trans h0)
  have hP : placeAt Bs.G₀.W l true =
      some (Look.P.ofPlace (Params.settingOf Bs.G₀.W.P.frame) true y) := by
    unfold placeAt
    rw [hy]
    rfl
  have e9 : sh = Xl.tl.f9 := shape_at_built hS hR O hl e3 hP hsh
  refine ⟨⟨?_, congrArg (·.ix) v, congrArg (·.mz) v, congrArg (·.tau) v, congrArg (·.z1) v,
    congrArg (·.z2) v⟩, fun P' hP' => ?_⟩
  · show tl.f9 = sh
    rw [e9]
    exact congrArg (·.f9) w
  · obtain rfl := Option.some.inj (hP.symm.trans hP')
    rfl

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.planned_digFields
#print axioms VerifiableInference.Desc.First.K8.Honest.planned_at_all
#print axioms VerifiableInference.Desc.First.K8.Honest.sameDig_at_all
#print axioms VerifiableInference.Desc.First.K8.Honest.digFields
