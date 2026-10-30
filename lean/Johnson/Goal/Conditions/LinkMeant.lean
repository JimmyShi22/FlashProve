-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/LinkMeant.lean: the seven clauses of Meant hold of the honest link prover's
input, that is of two encodings and OOD samples of one index with the honest row polynomials
(meant_home).
What the link is, where these files stand, and the common limits 1 to 4:
Johnson/Prover/Link/LinkYesStm.lean.

What this file has. meant_home. Take any b, any public files Z, any index i of homeR b Z
(Johnson/Goal/Conditions/HomeAtWider.lean), any two values q, q' of the encoding randomness (the
encoder's second argument, HolographicProtocol's type EncodingRandomness; free variables here) and any two seeds e, e'. Let M₀ and
M₁ be the honest row polynomials of (i, q) and (i, q'). Then the seven clauses of Meant
(LinkYesStm.lean) hold of the instance (recOf i q e, recOf i q' e'), the input oracles (encodeIndex i q, encodeIndex
i q') and M₀, M₁. There is no premise on Z, i, q, q', e or e'. The statement is a conjunction in the
order rec0, rec1, tab0, tab1, same, words, wide.
The honest row polynomials are honestPolys (OnBytes/Slice/Honest.lean) at the words that the encoder
encodes: cellWords (Johnson/Flat/CodingCells.lean), rowWords and tailWords
(OnBytes/Flat/CodingHonest.lean). The number 402653181 in them is the cut: the message's length
402,653,184 less the 3 pad entries of the sample map's one answer (fr_Z,
OnBytes/Slice/FullRecLink.lean; recZ, OnBytes/Slice/RecordRead.lean).
meant_obj is the same conjunction for general sizes S, sample map, cut and numbers of the committed
matrix (MatrixNums, Johnson/Flat/Claims.lean), over the explicit encoder codingCells
(CodingCells.lean). It has one premise, S.P.cut ≤ cut. meant_home is its instance at the full-size
parameter set, where fr_cut proves that premise.

How it fits. Meant is the one premise of link_yes (Johnson/Prover/Link/LinkJoinF.lean).
accept_met_home (Johnson/Goal/Conditions/LinkAcceptMet.lean) restates meant_home with the structure
Meant and adds that every symbol of the two oracles carries its position, for link_accLaw_home
(Johnson/Goal/Conditions/LinkAcceptHome.lean). linkFits_of_yes
(Johnson/Goal/Conditions/LinkFitsHome.lean) has the premise hmeant: a relation that is a parameter
there holds of homeR b Z's instances, oracles and polynomials. linkFits_one
(Johnson/Goal/Conditions/LinkFitsOne.lean) sets that relation to the conjunction of the seven
clauses and proves hmeant by meant_home, on the way to linkFits_at
(Johnson/Goal/Conditions/LinkFitsAt.lean). This file states no goal.

Other names (namespace FlashProve), each with a docstring below: polysOf, enc_obj, recW_obj,
rec_obj, enc_home.
Local notation. The letter Z is a sample map in the general part of the file and the public files in
enc_home and meant_home. The letter b (PublicFiles → ℕ) is homeR's first argument; enc_home and meant_home
hold for every b.

Lemmas used: rec_cells (Johnson/Prover/Link/BodyEnds.lean); tab_honest, same_cells
(Johnson/Prover/Link/FrontCoding.lean); table_honestTab (Johnson/Prover/At/OwedAt.lean);
lt_honestTab (Johnson/Prover/Link/ViewWords.lean); fr_cut (OnBytes/Slice/FullRecSz.lean). Everything
is proved at sizes that are variables and then instantiated: at the full size's numerals Lean's
elaborator runs out of recursion depth on the same steps. No limit is raised.

Limits. meant_home speaks only of the encodings, OOD samples and honest row polynomials of homeR b
Z.
Nothing on the decision (see link_yes). Nothing on what any value discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.LinkFitsPaid
import Johnson.Flat.CodingCells
import Johnson.Prover.Link.BodyEnds
import Johnson.Prover.Link.FrontCoding
import Johnson.Prover.Link.ViewWords
import Johnson.Prover.At.OwedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run.PQ (SgX)
open _root_.Iop (twoExternalStrings)
open VerifiableInference.Desc (fieldPrimeWord)

/- Lean compares these by their names. (Not the coding: it is unfolded below.) -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

section
variable (S : Sz) (Z : Cb.Ood.Sample OnBytes.Slice.GE S.En) (cut : ℕ) (N : MatrixNums) {X : Type}
  (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref)
  (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Z cut) N pp req)
    (relationsAndEncodingOfClaims _ (codingCells S Z cut N pp req)))) (P : F.Provers)
  (i : Cells (S.toDecR Z cut) N)

/-- The honest row polynomials of an encoding, for general sizes. -/
abbrev polysOf (q : PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)) :
    S.ix.Row → S.Co → OnBytes.Slice.GE :=
  honestPolys S (rowWords S (honestMsgs S (cellWords S Z cut N i q.1))) (tailWords S q.2)

/-- The encoding of an index, unfolded, in a protocol structure over the explicit encoder
codingCells: for general sizes, at every three protocols F over that configuration and all their
provers P. -/
theorem enc_obj (q : (F.withProvers P).EncodingRandomness) :
    (F.withProvers P).encodeIndex i q =
      honestTab S (rowWords S (honestMsgs S (cellWords S Z cut N i q.1))) (tailWords S q.2) :=
  rfl

/-- Its OOD sample, unfolded. -/
theorem recW_obj (q : (F.withProvers P).EncodingRandomness) (e : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).recOf i q e =
      (e, (S.toDecR Z cut).ix.ZR.val e (honestMsgs S (cellWords S Z cut N i q.1))) :=
  rfl

/-- The answers of its OOD sample are the sample map's values on these rows. -/
theorem rec_obj (q : (F.withProvers P).EncodingRandomness) (e : (F.withProvers P).OutOfDomainSeed) (ρ : (S.ixR Z).Row) (s : Z.S) :
    ((F.withProvers P).recOf i q e).2 (ρ, s) =
      ∑ j, Z.mat ((F.withProvers P).recOf i q e).1 s j * polysOf S Z cut N i q ρ ((S.ixR Z).pl j) :=
  Johnson.Prover.Link.rec_cells S Z cut N i q.1 (tailWords S q.2) e ρ s

/-- **The seven clauses, for general sizes**, under the one premise S.P.cut ≤ cut. -/
theorem meant_obj (hc : S.P.cut ≤ cut) (q q' : (F.withProvers P).EncodingRandomness) (e e' : (F.withProvers P).OutOfDomainSeed) :
    (∀ ρ s, ((F.withProvers P).recOf i q e).2 (ρ, s) =
      ∑ j, Z.mat ((F.withProvers P).recOf i q e).1 s j * polysOf S Z cut N i q ρ ((S.ixR Z).pl j)) ∧
    (∀ ρ s, ((F.withProvers P).recOf i q' e').2 (ρ, s) =
      ∑ j, Z.mat ((F.withProvers P).recOf i q' e').1 s j * polysOf S Z cut N i q' ρ ((S.ixR Z).pl j)) ∧
    ((S.lkR Z).tab ((F.withProvers P).encodeIndex i q) =
      fun ρ => (S.ixR Z).G.mulVec (polysOf S Z cut N i q ρ)) ∧
    ((S.lkR Z).tab ((F.withProvers P).encodeIndex i q') =
      fun ρ => (S.ixR Z).G.mulVec (polysOf S Z cut N i q' ρ)) ∧
    (S.lwR Z).SameOn ((S.ixR Z).view (polysOf S Z cut N i q))
      ((S.ixR Z).view (polysOf S Z cut N i q')) ∧
    (∀ p, (((twoExternalStrings (2 ^ S.P.T.a) SgX).rd ((F.withProvers P).encodeIndex i q, (F.withProvers P).encodeIndex i q') p).2.all
      (· < fieldPrimeWord)) = true) ∧
    (∀ (w : Bool) (x : ℕ) (h : x < 2 ^ S.P.T.a),
      ((twoExternalStrings (2 ^ S.P.T.a) SgX).rd ((F.withProvers P).encodeIndex i q, (F.withProvers P).encodeIndex i q')
        (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = 2 ^ S.P.v) := by
  refine ⟨rec_obj S Z cut N pp req F P i q e, rec_obj S Z cut N pp req F P i q' e',
    Johnson.Prover.Link.tab_honest S Z _ _, Johnson.Prover.Link.tab_honest S Z _ _,
    Johnson.Prover.Link.same_cells S Z cut N i q.1 q'.1 _ _ hc (Nat.sub_le _ _), fun p => ?_,
    fun w x h => ?_⟩
  · cases p with
    | inl x => exact Johnson.Prover.Link.lt_honestTab S _ _ x
    | inr x => exact Johnson.Prover.Link.lt_honestTab S _ _ x
  · cases w
    · exact (Johnson.Prover.At.table_honestTab S _ _ ⟨x, h⟩).2.2
    · exact (Johnson.Prover.At.table_honestTab S _ _ ⟨x, h⟩).2.2

end

/-- The encoding and the OOD sample of an index of homeR b Z, unfolded. -/
theorem enc_home :
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (i : (homeR b Z).Index) (q : (homeR b Z).protocol.EncodingRandomness) (e : (homeR b Z).protocol.OutOfDomainSeed),
    (homeR b Z).protocol.encodeIndex i q =
        honestTab frS (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q.1)))
          (tailWords frS q.2) ∧
      (homeR b Z).protocol.recOf i q e =
        (e, (frS.toDecR frZ 402653181).ix.ZR.val e
          (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q.1))) :=
  fun _ Z i q e =>
    ⟨enc_obj frS frZ 402653181 numsRef (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) Subtype.val _ _ i
      q, recW_obj frS frZ 402653181 numsRef (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) Subtype.val
      _ _ i q e⟩

/-- **The seven clauses at homeR b Z**: for all b, Z, i, q, q', e, e', at the honest row polynomials
M₀ and M₁. -/
theorem meant_home :
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (i : (homeR b Z).Index) (q q' : (homeR b Z).protocol.EncodingRandomness)
    (e e' : (homeR b Z).protocol.OutOfDomainSeed)
    (M₀ M₁ : (frS.ixR (recZ frS.P.T.l 29 1)).Row → frS.Co → OnBytes.Slice.GE),
    M₀ = honestPolys frS
      (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q.1)))
      (tailWords frS q.2) →
    M₁ = honestPolys frS
      (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q'.1)))
      (tailWords frS q'.2) →
    (∀ ρ s, ((homeR b Z).protocol.recOf i q e).2 (ρ, s) =
      ∑ j, (recZ frS.P.T.l 29 1).mat ((homeR b Z).protocol.recOf i q e).1 s j *
        M₀ ρ ((frS.ixR (recZ frS.P.T.l 29 1)).pl j)) ∧
    (∀ ρ s, ((homeR b Z).protocol.recOf i q' e').2 (ρ, s) =
      ∑ j, (recZ frS.P.T.l 29 1).mat ((homeR b Z).protocol.recOf i q' e').1 s j *
        M₁ ρ ((frS.ixR (recZ frS.P.T.l 29 1)).pl j)) ∧
    ((frS.lkR (recZ frS.P.T.l 29 1)).tab ((homeR b Z).protocol.encodeIndex i q) =
      fun ρ => (frS.ixR (recZ frS.P.T.l 29 1)).G.mulVec (M₀ ρ)) ∧
    ((frS.lkR (recZ frS.P.T.l 29 1)).tab ((homeR b Z).protocol.encodeIndex i q') =
      fun ρ => (frS.ixR (recZ frS.P.T.l 29 1)).G.mulVec (M₁ ρ)) ∧
    (frS.lwR (recZ frS.P.T.l 29 1)).SameOn ((frS.ixR (recZ frS.P.T.l 29 1)).view M₀)
      ((frS.ixR (recZ frS.P.T.l 29 1)).view M₁) ∧
    (∀ p, (((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd
      ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q') p).2.all (· < fieldPrimeWord)) = true) ∧
    (∀ (w : Bool) (x : ℕ) (h : x < 2 ^ frS.P.T.a),
      ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q')
        (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = 2048) := by
  intro b Z i q q' e e' M₀ M₁ h0 h1
  subst h0 h1
  exact meant_obj frS frZ 402653181 numsRef (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) Subtype.val
    _ _ i (le_of_eq (fr_cut _ _ _ _)) q q' e e'

end FlashProve

#print axioms FlashProve.enc_obj
#print axioms FlashProve.recW_obj
#print axioms FlashProve.rec_obj
#print axioms FlashProve.meant_obj
#print axioms FlashProve.enc_home
#print axioms FlashProve.meant_home
