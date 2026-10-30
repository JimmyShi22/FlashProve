-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LockAtMember.lean: CONDITIONAL. THE TWO NAMES OF THE LOCK OF
THE LAYERS' OWN ROUNDS (kind K4), AT THE BOOK's MAKER's OWN LETTERS, AT EACH GROUP OF LAYERS OF AN
OPENED DESCRIPTION IN THE GOALS' SCOPE.

What is here. PUBLIC DATA ALONE. A join of laws that stand elsewhere; no new thought. The tops of
Law/W/LockOfBook.lean, whose head says what the lock and its two names are, take a sub-protocol b of
the first chain and the form `K4RowIsPlan` (Law/W/RowIsPlanForm.lean). Here b is taken and not
assumed: the library's `IM.k4_of` (Johnson/IMR/K4Seat.lean) hands the member of the opened
description's first chain at K4's place of a group, with K4's own declared rounds. The form then
comes from Law/W/RowIsPlan.lean; its four counts from `k4Counts_of_public`
(Law/W/CountsOfLayout.lean): of that law's three premises the library pays two in the goals' scope
(`IM.Open.public`, Johnson/IMR/SeatOpen.lean; the field covers of `refPub_in_scope`,
Johnson/Road/K4/RefInScope.lean); the third is hQ's first equation. Statements and proofs.

  `k4_member_there`: a member of the first chain stands at K4's place of the group and declares
      the entries of K4's table.
  `k4Counts_at_group`: the four counts are not 0.
  `k4Names_at_group`: both names, AT A LETTER M for the maker's list of merges: twelve
      hypotheses.
  `k4Names_at_record`: **both names AT THE LIST OF MERGES THAT THE FUNCTION WHICH BUILDS THE
      HONEST PROVER HANDS** (`mergesByName`, Honest/BookWhole.lean; `onlineProverFromPublicFiles`, Honest/AtPure.lean,
      calls `bookWhole` at `mergesByName F.first.blocksInOrder`, which behind O.desc is `mergesByName
      c.blocksInOrder`): EIGHT HYPOTHESES. The two premises on the list, and that no round is named "SEND
      seed", come from Law/W/MergesByName.lean; that no two sub-protocols stand at one place, from
      hp (`places_nodup`, Honest/Law/Cuts.lean); hd and hca are not asked (`k4Names_whole`,
      Law/W/LockOfBook.lean, over `bookWhole_bare_at`, Honest/Small/BareOfBook.lean).

Not shown here. AT THE SECOND TOP THREE HYPOTHESES SPEAK OF THE BOOK, THE DESCRIPTION AND THE PLAN.
h: THAT THE MAKER's BOOK RETURNS. hp: the description's test on places. Laws of other writers, which
are no part of this library yet and by their writers' own word have been through working runs alone,
have the book's return at that very list, at the written description and at named files; the library
has the test on places at the written description (`wp_placesOk`) and from the plan's test
(`placesOk_of_planOk`): NO FILE THAT WE KNOW JOINS THESE TO THE F OF O. he: it fixes the letter e:
at e := the maker's count of the scalars in front of K4's row in its segment it asks nothing.
Law/W/MaskLockAt.lean's laws take the mask row's name AT ANOTHER e: the number of the lookup's
scalars on the verifier's side (`Forest.elems`). AT THAT e, he ASKS that the sub-protocols in front
of K4 in its link count just so many own scalars: a fact on other kinds' tables of rounds: shown in
no file that we know. The test `k4MaskLockAtB` reads its base and e as their sum alone: so he and
«the base is the sender's» are one equation for whoever closes the join. At the first top besides:
hfront and hmerge, on the letter M: that of K4's addresses it holds the last part's alone; hd and
hca: that the book has no coin of their own and no carried entry at K4's parts.

hS, hR and O: the public files lie in the goals' scope, are read, and the description is opened: SO
THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE (`OnBytes.secondHashFunction`). hQ: WHICH PUBLIC DATA:
five equations: the plan, the sub-proof's plan, the group, the link and the piece; r0 AND seg STAY
FREE. THAT THE PUBLIC DATA WHICH THE LOT's HONEST SIDE LAYS (`k4PubOf`, Honest/K4/Part.lean) MEET
THE FIVE IS NOT SHOWN HERE: Law/W/PubGOf.lean's `k4PubG_fields` has five such equations at the lot's
own term, and `IM.Open.W` ties the two public records; no file joins them. THAT `mergesByName` IS
THE FORMAT's LIST OF MERGES IS NOT SPOKEN OF.

LEFT OF THE JOIN: every hypothesis named above, he among them; THAT THE MAKER's LETTERS ARE THE
SENDERS': that row.owner and row.base.e are the letters at which the sender's sentence hE of
Law/W/MaskLockAt.lean is had; that idx.owner and idx.base.e are the letters of the index-mask
message's sender, and that the number behind idx.base.e is the one at which K4's text reads that
message (`k4IndexTakes`, Lot/IndexNum.lean: the sentence hE of Law/W/IndexLockAt.lean stands there);
and the two sentences hE themselves. NEVER TO BE SAID FROM THIS FILE: «K4's coins are the sender's»
as a thing that is shown · «lock and key fit». No example of the hypotheses together has been
through Lean.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach modules under Johnson/Goal/.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LockOfBook
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MergesByName
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CountsOfLayout
import Johnson.Desc.ProofFile.Honest.Law.Cuts
import Johnson.IMR.K4Seat
import Johnson.IMR.FlatIx
import Johnson.Road.K4.RefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {gk : ℕ} {Q : K4Pub}

/-- CONDITIONAL: on all five hypotheses. **A MEMBER OF THE FIRST CHAIN STANDS AT K4's PLACE OF THE
GROUP AND DECLARES THE ENTRIES OF K4's TABLE.** -/
theorem k4_member_there (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hk : gk < 12)
    (hQ : Q.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[gk]? = some Q.hp ∧ Q.g = gk ∧ Q.link = 2 * gk ∧
      Q.piece = 3) :
    ∃ b ∈ c.blocksInOrder, b.place = k4Place Q ∧ b.place = IM.k4Place gk ∧
      b.rounds = (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g).map
        fun e => ({ entry := e } : Fmt.DeclaredRound) := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hQ
  obtain ⟨Lk, b, x, e1, e2, -, hla, -, eg, eP, ehp, -, -⟩ := IM.k4_of hS hR O gk hk
  have hb : b ∈ c.blocksInOrder := List.mem_of_getElem? (IM.hear_at_flat e1 e2)
  have hpl : b.place = IM.k4Place gk := IM.alone_place hla
  have ehp' : x.2.hp = Q.hp := Option.some.inj (ehp.symm.trans q2)
  refine ⟨b, hb, ?_, hpl, ?_⟩
  · rw [hpl]
    unfold k4Place
    rw [q4, q5]
  · rw [IM.alone_rounds hla, q1, ← eP, ← ehp', q3, ← eg]
    rfl

/-- CONDITIONAL: on all five hypotheses. **THE FOUR COUNTS ARE NOT 0.** -/
theorem k4Counts_at_group (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hk : gk < 12)
    (hQP : Q.P = Bs.G₀.W.layers) : K4Counts Q :=
  k4Counts_of_public O.public hQP
    (by rw [hQP]; exact (OnBytes.Road.K4.refPub_in_scope hS hR O.public hk).covers)

variable {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}

/-- CONDITIONAL: on all twelve hypotheses. **BOTH NAMES OF K4's LOCK, AT THE MAKER's OWN LETTERS, AT
A GROUP OF LAYERS OF THE OPENED DESCRIPTION.** row and idx are what `ownerOf` returns. -/
theorem k4Names_at_group (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hk : gk < 12)
    (hQ : Q.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[gk]? = some Q.hp ∧ Q.g = gk ∧ Q.link = 2 * gk ∧
      Q.piece = 3)
    (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    (hfront : ∀ i, i + 1 < (k4RowIn Q).length → k4Addr Q i ∉ M.ends)
    (hmerge : k4Addr Q ((k4RowIn Q).length - 1) ∈ M.ends)
    (hd : ∀ i, i < (k4RowIn Q).length → dueAt (B.rowsOf 0) ⟨k4Place Q, i⟩ = ⟨0, 0⟩)
    (hca : ∀ i, i < (k4RowIn Q).length → carryE B ⟨k4Place Q, i⟩ = []) {e : ℕ}
    (he : e = ownScalarsOf (partsInFront c.blocksInOrder (2 * gk) (IM.k4Place gk))) :
    ∃ row idx,
      ownerOf maskRowRun c.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
          s!"link {2 * gk}, moment 0" isMaskRowMsg = some row ∧
        ownerOf indexMaskRun c.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
          isIndexMaskMsg = some idx ∧
        K4MaskLockAt B Q e row.owner row.base.e ∧
        K4LastEntryAt B Q idx.owner (idx.base.e + mergeEndsOf M.ends
          (linksInFront c.blocksInOrder (2 * gk) ++ partsInFront c.blocksInOrder (2 * gk) (IM.k4Place gk))) := by
  obtain ⟨b, hb, hpl, hpl', hr⟩ := k4_member_there hS hR O hk hQ
  have hpos : K4Counts Q := k4Counts_at_group hS hR O hk hQ.1
  obtain ⟨A, m, R, -⟩ := k4_rowIsPlan (M := M) hpl hr hpos hfront hmerge
  have hl : b.place.link = some (2 * gk) := by rw [hpl']
  have eF := O.desc
  subst eF
  rw [← hpl'] at he ⊢
  exact k4Names_of_bookWhole h hp hb hl R hd hca he

/-- CONDITIONAL: on all eight hypotheses. **BOTH NAMES OF K4's LOCK, AT THE MAKER's OWN LETTERS, AT
THE LIST OF MERGES THAT `onlineProverFromPublicFiles` HANDS.** row and idx are what `ownerOf` returns. -/
theorem k4Names_at_record (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hk : gk < 12)
    (hQ : Q.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[gk]? = some Q.hp ∧ Q.g = gk ∧ Q.link = 2 * gk ∧
      Q.piece = 3)
    (h : bookWhole F p0 p1 p2 (mergesByName c.blocksInOrder) = .ok B) (hp : F.placesOk = true) {e : ℕ}
    (he : e = ownScalarsOf (partsInFront c.blocksInOrder (2 * gk) (IM.k4Place gk))) :
    ∃ row idx,
      ownerOf maskRowRun c.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
          s!"link {2 * gk}, moment 0" isMaskRowMsg = some row ∧
        ownerOf indexMaskRun c.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
          isIndexMaskMsg = some idx ∧
        K4MaskLockAt B Q e row.owner row.base.e ∧
        K4LastEntryAt B Q idx.owner (idx.base.e + mergeEndsOf (mergesByName c.blocksInOrder).ends
          (linksInFront c.blocksInOrder (2 * gk) ++ partsInFront c.blocksInOrder (2 * gk) (IM.k4Place gk))) := by
  obtain ⟨b, hb, hpl, hpl', hr⟩ := k4_member_there hS hR O hk hQ
  have hpos : K4Counts Q := k4Counts_at_group hS hR O hk hQ.1
  have hE : K4Ends Q := k4Ends_of_public O.public hQ.1
  have hl : b.place.link = some (2 * gk) := by rw [hpl']
  have eF := O.desc
  subst eF
  have hnd : (c.blocksInOrder.map (·.place)).Nodup := (ProofFile.Honest.places_nodup hp).1
  obtain ⟨A, m, R, -⟩ := k4_rowIsPlan_byName hnd hb hpl hr hpos hE
  rw [← hpl'] at he ⊢
  exact k4Names_whole h hp hb hl R (k4_noSeed hr) he

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_member_there
#print axioms ProofFile.Honest.K4.W.k4Counts_at_group
#print axioms ProofFile.Honest.K4.W.k4Names_at_group
#print axioms ProofFile.Honest.K4.W.k4Names_at_record
