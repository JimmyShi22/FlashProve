-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamAtFull2.lean: at the full-size parameters, which positions of the two
tables the link's prover opens, and how many the link's verifier reads of each: at most 62.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Except in linkBeside_filesD, the rounds' description is dsFull and the list
of openings of the two tables (the first table and the copy) is frD.xs. fr_storedOk, fr_storedNo and
fr_own are checked by evaluation in Lean's kernel; fr_cnt follows from the list's value (fr_xs) by
definition. Only public numbers occur in the statements.
  fr_storedOk    the test storedOk (SeamInput.lean) accepts these parameters and the tables' depth.
  fr_storedNo    a control that checks that this test can fail: with the two tables swapped in the
                 list of openings, storedOk rejects.
  fr_storedTie   hence StoredTie (SeamInput.lean) holds here for every list of verifier challenges.
  fr_own         every tree that a round of dsFull opens has a number below 2^16.
  fr_cnt         the two counts of openings, cntOf false and cntOf true, are 62 and 62.
  fr_linkCounts  hence the link's verifier at these parameters (linkProtocolOfRoundData, OnBytes/Flat/LinkSib.lean),
                 for every decision function, reads at most 62 positions of the first table and at
                 most 62 of the copy, at every instance and verifier message. It is also local
                 (IsLocal; SeamCounts.lean says what that means).
  linkBeside_filesD   LinkBeside (Johnson/LinkSim/Spec.lean) holds for the protocol structure of the
                 three files threeProtocolsAtFullSize (Johnson/Flat/Dec/WiresAtSizes.lean), at the counts of its
                 list of openings xs. It holds for every value of every argument of threeProtocolsAtFullSize; of
                 these, the link's protocol is built from ds, xs and the decision alone (by
                 inspection of the proof, not proved). The one premise is that every tree that a
                 round of ds opens has a number below 2^16.

How it fits. LinkBeside gathers part of what the premises of index privacy (PremW) ask of the link's
protocol besides a simulator: two counts and locality (linkBeside_of_premW,
Johnson/LinkSim/Spec.lean). fr_storedTie is used in the proof of homeExact
(Johnson/LinkSim/AtHome/Home.lean), through Johnson/LinkSim/AtHome/HomeTies.lean. fr_linkCounts
gives home_beside (Johnson/LinkSim/AtHome/HomeTies.lean): LinkBeside at 62 and 62, which
link_all_met (Johnson/LinkSim/AtHome/CompileFiller.lean) uses. Under Johnson/LinkSim/ no file calls
linkBeside_filesD.

Limits.
- Everything is at the full-size parameters alone. In linkBeside_filesD these are the sizes (frS,
  frZ and 402653181), the tables' depth and the choice of challenge types (ckP .two); every other
  argument is a variable.

Notes. fr_storedOk, fr_storedNo and fr_own raise a limit of elaboration (Johnson/LinkSim/Spec.lean,
"maxRecDepth").
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SeamInput
import Johnson.LinkSim.AtText.SeamCounts
import Johnson.Prover.Link.ChainSeats
import Johnson.Flat.Dec.WiresAtSizes

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes.LinkSim
open OnBytes.Flat (linkProtocolOfRoundData dsFull)
open OnBytes.Slice (frS frD fr_xs)
open _root_.Desc.K15 (frP)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP)
open _root_.Run.PQ (View XO cntOf)

set_option maxRecDepth 100000 in
/-- The test storedOk accepts the full-size parameters, the tables' depth and the list of
openings. -/
theorem fr_storedOk : storedOk frP frS.P.T.a dsFull frD.xs = true := by
  rw [fr_xs]
  decide +kernel

set_option maxRecDepth 100000 in
/-- A control that checks that the test can fail: with the two tables swapped in the list of
openings, storedOk rejects. -/
theorem fr_storedNo :
    storedOk frP frS.P.T.a dsFull [⟨3, true, 0, 62⟩, ⟨3, false, 62, 62⟩] = false := by
  decide +kernel

/-- StoredTie at the full-size parameters, for every list of verifier challenges. -/
theorem fr_storedTie (Ds : List Fmt.Drawn) : StoredTie frP frS.P.T.a dsFull frD.xs Ds :=
  storedTie_of_ok frP _ dsFull _ Ds fr_storedOk

set_option maxRecDepth 100000 in
/-- Every tree that a round of dsFull opens has a number below 2^16. -/
theorem fr_own : ∀ d ∈ dsFull, ∀ n ∈ d.opens, n < 2 ^ 16 := fun d hd n hn =>
  of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1
    (show (dsFull.all fun d => d.opens.all fun n => decide (n < 2 ^ 16)) = true by
      decide +kernel) d hd) n hn)

/-- In the full-size list of openings, the counts for the first table and for the copy (cntOf) are
62 and 62. -/
theorem fr_cnt : cntOf false frD.xs = 62 ∧ cntOf true frD.xs = 62 := by
  rw [fr_xs]
  exact ⟨rfl, rfl⟩

/-- At the full-size parameters, for every decision function, the link's verifier reads at most 62
positions of each table, and it is local. -/
theorem fr_linkCounts (Xi : Type) (dec : Xi → View → Bool) :
    (∀ x ρ, (((linkProtocolOfRoundData (ckP .two) dsFull frS.P.T.a frD.xs dec).extReads x ρ).filter
      fun p => p.isLeft).card ≤ 62) ∧
    (∀ x ρ, (((linkProtocolOfRoundData (ckP .two) dsFull frS.P.T.a frD.xs dec).extReads x ρ).filter
      fun p => p.isRight).card ≤ 62) ∧
    (linkProtocolOfRoundData (ckP .two) dsFull frS.P.T.a frD.xs dec).IsLocal := by
  have h := linkCounts (ckP .two) dsFull frS.P.T.a frD.xs Xi dec fr_own
  rw [fr_cnt.1, fr_cnt.2] at h
  exact h

section
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.Maker
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool)
  (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO)
  (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- **LinkBeside, part of what the premises of index privacy ask of the link's protocol besides a
simulator**, for the protocol structure of the three files, at every value of their arguments. -/
theorem linkBeside_filesD (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) :
    LinkBeside ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)
      (cntOf false xs) (cntOf true xs) :=
  ⟨(linkCounts (ckP .two) ds frS.P.T.a xs _ dec hown).1,
    (linkCounts (ckP .two) ds frS.P.T.a xs _ dec hown).2.1,
    (linkCounts (ckP .two) ds frS.P.T.a xs _ dec hown).2.2⟩

end

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.linkBeside_filesD
#print axioms OnBytes.LinkSim.Seam.fr_storedOk
#print axioms OnBytes.LinkSim.Seam.fr_storedNo
#print axioms OnBytes.LinkSim.Seam.fr_storedTie
#print axioms OnBytes.LinkSim.Seam.fr_own
#print axioms OnBytes.LinkSim.Seam.fr_linkCounts
