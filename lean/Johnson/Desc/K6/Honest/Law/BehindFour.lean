-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/BehindFour.lean: THE FOUR PUBLIC TESTS THAT THE SUB-PROTOCOL "the output
head's own rounds" (K6) MAKES (lookIn 24 8; formsInT 24 4 "own"; formsInT 24 3 "planes"; formsInT 24
4 "join") HOLD BEHIND A YES OF THE STRICT READING OF ITS BARE BLOCK. AT A STATE; general in the
composed meaning's data and in the test beneath. A GATHERING. EVERY THEOREM IS CONDITIONAL.

  `stateIsPlan_at`   behind a yes every reader of the open segment's part is a term off the public
                     parameters
  `four_made_at`     MAIN

WHY IT IS TYPED, AND HOW. As Honest/Law/BehindMade.lean: the library's `stateIsPlan_behind`
(Johnson/Desc/Kinds/Law/K6RestAt.lean) and its gathering `pubBehind_four`
(Law/K6PubBehindFour.lean), less the piece; each call there of a lemma that reads the promise in
front (`left_front`, `sentIs_front`, `fresh_front`, `book_front`, Law/K6FrontSays.lean;
`rows_front`, `linkArr_front`, `oneRow_front`, Law/K6FrontShape.lean) is here a premise on the
state, in that lemma's conclusion's own words. Called as they lie: `reads_of_C`, `maskSeated_of_C`
(Law/K6SeatsTest.lean), `entInT_reads` (Law/ReadsEntInT.lean), `runs_at_head` (Law/K6PubMore.lean),
`k6Pub_says`.

WHAT IS LEFT AS PREMISES of `four_made_at`. On the state in front: what the law asks of it (`K6On`);
what the lookup on the calls left; no count of rows waits; the open segment's number and list of
arrays; three Bools of the promise; the reads' array has one row and the planned number of columns;
two facts on a reached state (`K6Reached`); five along the fold (`FoldAt`); of the leaves. On the
state behind: `K6After`; the covered positions are there. On public data: five tests with code, that
segment 24 is the head's in the meaning's list of segments, and a bound. On the link's list of
rounds: five facts.

Why the promise's lemmas are not called: each takes the table's promise at the composed meaning,
whose three sentences on the oracles' strings are the true ones; the honest side's promise does not
hold these.

Relatives. Of `stateIsPlan_at`: `stateIsPlan_342` (Johnson/P4R/Head342.lean): the like conclusion
(with the number of messages at 342) at the state at 342, but from what the promise AT 342 says,
which is what is to be shown here. Of the arms "own" and "join" of `four_made_at`: `made_own`,
`made_join` (Law/K6FormsMade.lean): at a state, at the composed meaning's test; here the test
beneath is a letter.

Limits. No yes is shown, and no state at which the premises hold together. Modules under
lean/Johnson/Goal/ are among what this file imports: it imports no module of that folder by name and
calls nothing that is declared there: they lie beneath the library's files that it calls. Nothing on
any property.

-/
import Johnson.Desc.K6.Honest.Law.BehindMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (Block Claim Link)
open VerifiableInference.Desc.First (S Pub pubAll)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.AtTable
open VerifiableInference.Desc.Kinds.Head.Law.AtFold

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : Sound.MgData Xi P Tok rows cols nR Wp) (base : Pub → P × S → Bool) (z : P) {s s' : S}
  {rs : List Fmt.RoundView} {b6 : Block S Unit} (h6 : blockOf Wp 24 = some b6)
  (hd : (Sound.below b6).decide s rs [] = .ok s') (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
  (Lp : K12.Door.Laid) (Mm : List OracleShape)

include h6 hd

/-- **Behind a yes every reader is a term off the public parameters.** The library's proof at a
piece (`stateIsPlan_behind`, Johnson/Desc/Kinds/Law/K6RestAt.lean), less the piece and with the
promise's three Bools as premises. It asks that the strict reading accepts and spends no more than
that the bare sub-protocol's decision does; of the library's two clauses it concludes the first:
that the chain stands in the head's segment behind is dropped. CONDITIONAL. -/
theorem stateIsPlan_at (sentIs : First.FillSent.sentIsB D.pubD.dS 24 s = true)
    (fresh : VerifiableInference.OnPublicFiles.linkFreshB (D.sent.arrayOf.getD 24 #[]) s = true)
    (book : First.bookAt D.N PS[341]? s = true) (Fo : AtFold.FoldAt Lp Mm D.cs D.shape lay6 s) :
    ∃ aK, StateIsPlan lay6 D.cs D.shape D.pubD.dS Lp Mm (D.sent.arrayOf.getD 24 #[])
      (D.N.msgsAt PS[341]?) s' aK := by
  obtain ⟨_, hd'⟩ := canonical_of_below b6 s s' rs [] hd
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h6
  obtain ⟨o, F1, X, Q, ho, hop, e2, _, _⟩ := forks_blockAt _ i _ 24 hd'
  have hLa : s.link? = some o.L := by
    unfold First.S.link?
    rw [ho]
    show (if o.opened = true then some o.L else none) = _
    rw [if_pos hop]
  have hLb : s'.link? = some o.L := by
    rw [e2]
    show (if o.opened = true then some o.L else none) = _
    rw [if_pos hop]
  have hFb : s'.fork? = some F1 := by
    rw [e2]
    show (if o.opened = true then some F1 else none) = _
    rw [if_pos hop]
  have hTb : s'.tl? = some o.tl := by
    rw [e2]
    show (if o.opened = true then some o.tl else none) = _
    rw [if_pos hop]
  have hst : s'.st = s.st := by rw [e2]
  have hbk : s'.book = s.book := by rw [e2]
  have hlive : s.live = o.L.check := by
    unfold First.S.live
    rw [hLa]
  obtain ⟨aK, k1, k2, k3, k4⟩ := segAt_parts s' o.L F1 o.tl hLb hFb hTb
  have hS := sentIs
  have hfr := fresh
  have hbo := book
  unfold VerifiableInference.OnPublicFiles.linkFreshB at hfr
  rw [Bool.and_eq_true, hLa] at hfr
  have harr : o.L.arrayOf = D.sent.arrayOf.getD 24 #[] := eq_of_beq hfr.2
  unfold First.bookAt at hbo
  simp only [Bool.and_eq_true, beq_iff_eq] at hbo
  refine ⟨aK, ⟨k1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro born message
    rw [k2]
    exact First.FillSent.whereIs_of_sentIs hLa hS born message
  · rw [k2]
    exact First.FillSent.link_of_sentIs hLa hS
  · rw [k2, ← hlive]
    exact Fo.shape
  · rw [k2, ← hlive]
    exact Fo.layout
  · rw [k2]
    exact harr
  · rw [k3, hst]
    exact Fo.codes
  · rw [k3, hst]
    exact Fo.msgs
  · rw [k4, hbk]
    exact Fo.seats
  · rw [k4, hbk, hbo.1.2, hbo.2]
  · rw [k3, hst, hbo.2]

/-- **THE FOUR PUBLIC TESTS THAT THE SUB-PROTOCOL MAKES HOLD BEHIND ITS YES.** The library's
gathering at a piece (`pubBehind_four`, Johnson/Desc/Kinds/Law/K6PubBehindFour.lean), less the
piece, with what the promise in front says as premises on the state. CONDITIONAL. -/
theorem four_made_at (hOn : K6On Wp s) (hA : K6After Wp s')
    (left : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s)
    (hrows : First.Tape.RowsOwed.noneWaits s.rowsOwed = true)
    (hlk : (∃ L, s.link? = some L ∧ L.link = 24 ∧ L.arrayOf = D.sent.arrayOf.getD 24 #[]) ∧
      (s.tl?.bind (·.heard)).isNone = true)
    (sentIs : First.FillSent.sentIsB D.pubD.dS 24 s = true)
    (fresh : VerifiableInference.OnPublicFiles.linkFreshB (D.sent.arrayOf.getD 24 #[]) s = true)
    (book : First.bookAt D.N PS[341]? s = true)
    (tree : ∃ G tr, s.fork? = some G ∧ G.trees[readsOf Wp]? = some tr ∧ tr.R = 1 ∧
      tr.K = Wp.H.nU.getD 2 0)
    (R : K6Reached s) (Fo : AtFold.FoldAt Lp Mm D.cs D.shape lay6 s)
    (hLv : ∀ Fs gk, s.fork? = some Fs → s.lookHeard? = some gk →
      LeavesReady gk Fs ∧ OnBytes.PscRun.Filled Fs gk.sBit ∧
        ∀ x ∈ gk.leaves.start.slots.toList, OnBytes.PscRun.Filled Fs x.1)
    (hc : ∃ cov, s'.covered Wp.hS.T Wp.hS.V = .ok cov)
    (hC1 : k6PubC Wp = true) (hC2 : readsRoomC Wp lay6 (D.sent.arrayOf.getD 24 #[]) = true)
    (hB : tabsPlanB Wp.hS Wp.HLy Wp.H = true) (hRB : readsPlanB Wp.hS Wp.H = true)
    (hC3 : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp Mm
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    (sorts : D.links[24]? = some .head)
    (planeCols : ∀ p3 h3, First.Look.placeAt Wp 24 false = some p3 → p3.shape = some h3 →
      h3.NC * 2 ^ (h3.kT + 5 - Wp.hS.lmbH) ≤ (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
        ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH))
    (piece6 : ℕ) (Lk : Link S Claim) (small : S → Option K9.Read)
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (KB : K6Back Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (runs2 : PlanesStates (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (back2 : PlanesBack (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (readers : D.Rd 24 =
      K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk) :
    ∀ i ∈ [Pub.lookIn 24 8, .formsInT 24 4 "own", .formsInT 24 3 "planes",
      .formsInT 24 4 "join"], pubAll D.pubD base i (z, s') = true := by
  intro i hi
  obtain ⟨_, _, c3, c4, c5, _⟩ := k6Pub_says Wp hC1
  obtain ⟨aK, I⟩ := stateIsPlan_at D h6 hd lay6 Lp Mm sentIs fresh book Fo
  obtain ⟨cU, u1, u2⟩ := reads_of_C hC3 I
  have hEnt := entInT_reads Wp lay6 _ hC2 (D.N.sent 24 0) s' aK I.seg I.layout I.arrays cU u1 u2
  have hMask : (K9.maskSeat (D.N.sent 24 0) aK).isSome = true := by
    obtain ⟨o, x, m1, m2, _⟩ := maskSeated_of_C hC3 I
    unfold K9.maskSeat
    rw [Sound.maskAt_eq, m1]
    show (K9.seatAt (D.N.sent 24 0) aK.d.book o).isSome = true
    rw [m2]
    rfl
  have hruns := runs_at_head D sorts
  have forms := made_forms_at D h6 hd hOn hA piece6 Lk small KS KB readers R.noTab R.wo left tree
    c3 hB hRB hc c4 c5 aK I.seg hMask hEnt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact made_lookIn_at D base z h6 hd hOn left hrows hlk hC1
  · rw [First.pubAll_formsInT]
    have e : D.pubD.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")] :=
      hruns.2.2.2.1
    rw [e]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨forms "norm" (Or.inl rfl), forms "policy" (Or.inr (Or.inl rfl)),
      forms "logits" (Or.inr (Or.inr (Or.inl rfl)))⟩
  · rw [First.pubAll_formsInT]
    have e : D.pubD.runs 24 3 "planes" = [(2, "planes")] := hruns.2.1
    rw [e]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact made_planes_at D h6 hd hOn Lk small runs2 back2 readers R left tree c3 hB hRB hc c4 c5
      planeCols hLv aK I.seg hMask hEnt
  · rw [First.pubAll_formsInT]
    have e : D.pubD.runs 24 4 "join" = [(3, "join")] := hruns.2.2.1
    rw [e]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact forms "join" (Or.inr (Or.inr (Or.inr rfl)))

end

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.stateIsPlan_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.four_made_at
