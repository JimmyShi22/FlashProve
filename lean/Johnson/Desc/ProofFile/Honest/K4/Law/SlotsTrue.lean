-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SlotsTrue.lean: CONDITIONAL.

Not shown here. No property is claimed. THAT THE PREMISES CAN BE MET: no example is known. WHAT THE
HONEST WORDS MEAN: each is typed as the part's own text has it, padded with 0 where a maker returns
nothing or a list is too short: that it is a term of the library at the witness's cells is another
statement's matter. NOT HERE: the merge's end value: `ends_said` (Law/SaidKit.lean) has what its
round shows; a tie for the row's last coin, which is no entry of the mask row, and the word under
its slot are not in this file. Nor the slots of the sumchecks' hiding polynomials, nor what the runs
"front" and "back" lay. That the step of K4's member of the thread accepts is a premise. No
statement here calls `K4Seated.fits`: they hold at shapes that do not fit too. Nothing on soundness,
on completeness or on any other property. WHAT IT IMPORTS, by a walk over import lines: no module
under Johnson/Goal/ or Johnson/D/; seven under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue,
CmsBcs, Cms, Bcs), which come with a module of the library (Johnson/E/KObj/ProofFile.lean) through
Law/RowBatch.lean: nothing here names one of them.

What is here. A STAND is a state of a run between two sub-protocols: the run's coins k, the
verifier's state s, where the prover's run stands m, the tables at hand E. Behind the step of K4's
member on what the honest row of the layers' own rounds (the sub-protocol K4) has played from a
stand: in the world of every ledger later than the one that the step leaves, on the mask row that
is read off the witness, each slot of a value that was sent under an entry of that mask row is worth
the honest part's own word under the map `Reading.gl.val`. Definitions, and statements with their
proofs.

THE PREMISES: `K4Seated` (Law/Seated.lean) · `K4Sits` (Law/Sits.lean) · and at the one stand of
which a statement speaks: `K4MaskTieAt` (Law/ScriptAt.lean: the tie of Law/Script.lean at one stand)
· `K4SizedAt` (Law/RowBatch.lean). Who is meant to show each stands in these files. `K4Stand` HAS
THREE FIELDS MORE: stepped (the member's step at the stand), seg and heard (what lies behind the
step: the segment's part and the hearing's own): `step_hears` (Law/RowBatch.lean) gives heard's form
once seg is had; who shows seg is not said in this file. No premise "the maker returns" is asked.
`stand_seen` alone asks `Thr`, the thread's own proposition on a stand (Honest/Thread/Thr.lean).

  The row whole and its numbers: Law/RowNums.lean.
  `K4Stand …`   the premises, the stand and what lies behind the step, as one structure
  `stand_ground`   what every run's statement begins with: what lies under the slots, and the slots
      by number, behind the hearing's return on the tape of the played rounds; what the book lends
      (`lendRow`, Honest/Frame.lean); the mask row's entries behind the step are the coins
  `stand_look`, `stand_seen`, `stand_lens`   what the step has heard of the lookup in front is what
      the state in front holds; as many rounds have been shown in front of the member as the public
      data count; each sumcheck's variables' challenges are as many as its variables
  `tape_beta`, `scalars_field`, `lead_field`, `ends_field`   the verifier's factor is the prover's
      challenge; one statement for each of the three sorts of message
  `leadWord`, `endWord`   a job's lead and end value by number, or 0
  `OpenedLeft …`   one field for each run of slots. The left sides are those of the fields of
      `Opened` and `OpenedBack` (Johnson/Road/K4/W/Ground.lean), a run's slots counted from its
      first; AND MORE: the second token sumcheck's claimed sum and all the batched sumcheck's end
      values, which Johnson/Road/K4/W/OpenedOwn.lean reads
  `opened_left`   **a stand gives it**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowNums
import Johnson.Desc.ProofFile.Honest.K4.Law.SaidKit
import Johnson.Desc.ProofFile.Honest.K4.Law.ScriptAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Fork World ledNS ledNP ledNO)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.K.Kc (paired leading)
open OnBytes.PscRun (Sized Later)
open OnBytes.Desc.First.K4 (Par hearFl entries seatS k0)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgQ dataQ)
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends ownSlots)
open OnBytes.Desc.First.P1 (sentOf drawnOf tapeEps tapeCl)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-! ## 1 The stand behind the member's step -/

/-- **The premises, the stand (k, s, m, E), and what lies behind the member's step from it.** A: the
open segment's part behind the step. o: what the step has heard. It is a definition: a premise's
form. Nothing is claimed of it. -/
structure K4Stand (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (b : Nat) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub) (p : Par)
    (blk : Block First.S Claim) (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ)
    (k : Coins Bk) (s : First.S) (m : Mid (Local W₀ Rc Xi Tr) X) (E : Env) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) X) (cols : List VerifiableInference.Desc.OpenedColumn)
    (s' : First.S) (A : VerifiableInference.Desc.K9.Part) (o : Own) : Prop where
  seat : K4Seated T b cells weights tokens look Q p blk
  sits : K4Sits T b p
  sized : K4SizedAt s
  mask : K4MaskTieAt T cells weights tokens look Q own rdOf k s m
  stepped : T.Stepped blk k s m E ds y cols s'
  seg : segAt? s' = some A
  heard : seatS.own s' = some o

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- **What every run's statement begins with.** a: the open segment's part in front of the member:
the slots are counted from its ledger's next slot. c: what the book lends the row. -/
theorem stand_ground
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    ∃ (a : VerifiableInference.Desc.K9.Part)
      (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts),
      segAt? s = some a ∧
      K4Under Q.P Q.hp Q.g o A.F (paired (roundsOf y.1) (entries Q.P Q.hp Q.g)) ∧
      K4Nums Q.P Q.hp Q.g o a.F.next ∧
      K4Played T b cells weights tokens look Q p blk k m E ds y cols c ∧
      ∀ ds' j, j + 1 < spentTo (k4RowIn Q) (k4RowIn Q).length →
        (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask (a.F.next + j) =
          Reading.gl.val ((spentOf _ c).getD j zeroE) := by
  obtain ⟨a, a₀, fo, ha, ha0, haF, _, hh, hdata⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  have hSd : Sized a.F := by
    rw [haF]
    exact Z.sized a₀ ha0
  obtain ⟨⟨l, hl, hy⟩, _⟩ := Z.stepped.1
  obtain ⟨c, hc, _, _, _⟩ := chainSteps_one hl Z.seat.half
  rw [Z.seat.place] at hc
  obtain ⟨i1, i2⟩ := moved_state Z.stepped.1
  have U := hear_under hSd hh
  have N := hear_nums hSd hh
  have hlen : (spentOf _ c).length = spentTo (k4RowIn Q) (k4RowIn Q).length := by
    rw [spentOf_length]
    show spentTo ((k4RowIn Q).map _) ((k4RowIn Q).map _).length = _
    rw [spentTo_lift, List.length_map]
  refine ⟨a, c, ha,
    ⟨U.sums, U.sq, U.prods, U.cl8, U.ends8, U.terms, U.stack, U.lv1, U.lv2, U.emb⟩,
    ⟨N.sW, N.sL, N.sR, N.sPv, N.sCl, N.sEnd, N.hasT, N.terms, N.sH1, N.sB0, N.sV, N.hL, N.hR,
      N.has2, N.lv2⟩,
    ⟨Z.seat, Z.stepped.1, hc⟩, fun ds' j hj => ?_⟩
  rw [hdata, i1, i2, List.append_assoc]
  exact Z.mask a c ha hc (ds ++ ds') j (by rw [hlen]; exact hj)

/-- **What the step has heard of the lookup in front is what the state in front holds of it**: for
whoever ties the lookup's sampled values to the honest side's (`K4LookTie`, Law/Script.lean). -/
theorem stand_look
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    seatS.look s = some o.H.fo := by
  obtain ⟨a, a₀, fo, _, ha0, _, hfo, hh, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  have e : o.H.fo = fo := OnBytes.Desc.First.K4.Slots.own_fo hh
  rw [e]
  simp [seatS, ha0, hfo]

/-- **As many rounds have been shown in front of the member as the public data count**: for whoever
reads a round that was shown by its number in the chain (`k4TermsEnds`, Honest/K4/Part.lean). -/
theorem stand_seen (Se : K4Seated T b cells weights tokens look Q p blk)
    (hT : Thr T b k s m E) : m.seen.length = Q.r0 := by
  have ⟨_, _, _, _, hMade, _, _⟩ := hT
  have h := congrArg List.length hMade.1
  rw [List.length_map] at h
  rw [h]
  exact k4_heard_front Se hT

/-- **The variables' challenges of each of the six sumchecks are as many as its variables.** It asks
the whole stand; its proof spends `K4Played` (`stand_ground`) alone. -/
theorem stand_lens
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    (ownE ds (rJ1 Q.g + 1) Q.P.rd.muV).length = Q.P.rd.muV ∧
    (ownE ds (rJ2 Q.P Q.g + 1) Q.P.y.h.lt).length = Q.P.y.h.lt ∧
    (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt).length = Q.P.y.h.lt ∧
    (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).length = Q.hp.lamS ∧
    (ownE ds (rJ5 Q.P Q.hp Q.g + 1) Q.P.rd.muH).length = Q.P.rd.muH ∧
    (ownE ds (rJ6 Q.P Q.hp Q.g + 1) Q.P.rd.muH2).length = Q.P.rd.muH2 := by
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  have h := sum_rounds_there Pl (k0 Q.g + 12) _ _ _ (k4RowIn_at Q 12) ⟨2, 2⟩ rfl
  rw [(k4_row_nums Q).m6] at h
  have h' : rJ6 Q.P Q.hp Q.g + (Q.P.rd.muH2 + 2) < ds.length := by
    have e : (k4LevelShape Q.P.rd.muH2).vs.length = Q.P.rd.muH2 := List.length_replicate
    rw [← e]
    exact h
  simp only [rJ6, rJ5, rJ4, rJ3, rJ2, rowsRound, rJ1] at h' ⊢
  refine ⟨ownE_length _ _ _ ?_, ownE_length _ _ _ ?_, ownE_length _ _ _ ?_, ownE_length _ _ _ ?_,
    ownE_length _ _ _ ?_, ownE_length _ _ _ ?_⟩ <;> omega

/-! ## 3 One statement for each of the three sorts of message -/

/-- **The verifier's factor is the prover's challenge**: the element that round number n of the tape
of the played rounds sampled first. -/
theorem tape_beta {W Z : Type} {l : List (Step W Z)} {ds : List Fmt.Drawn} {m : Mid W Z}
    {y : List Played × Mid W Z} (hy : play l ds [] m = .ok y) (es : List Fmt.Entry) (n : Nat) :
    tapeEps ((paired (roundsOf y.1) es).drop n) = (ownE ds n 1).headD zeroE := by
  have e1 : ∀ t : OnBytes.K.Kc.Tape, tapeEps t = (drawnOf t).headD zeroE := by
    intro t
    cases t <;> rfl
  have q := played_drawn hy n
  rw [e1, paired_drawn]
  unfold ownE drawnE
  cases hr : (roundsOf y.1)[n]? with
  | none =>
    rw [hr] at q
    have hd : ds[n]? = none := q.symm
    rw [List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.1 hd)]
    rfl
  | some r =>
    rw [hr] at q
    have hd : ds[n]? = some r.drawn := q.symm
    have e2 : (ds.drop n).take 1 = [r.drawn] := by
      have q := List.take_add_one (l := ds.drop n) (i := 0)
      have g : (ds.drop n)[0]? = some r.drawn := by
        rw [List.getElem?_drop]
        exact hd
      rw [g] at q
      exact q
    rw [e2]
    show (r.drawn.elems.map OnBytes.E.ofTriple).headD zeroE =
      (r.drawn.elems.head?.map OnBytes.E.ofTriple).getD zeroE
    cases r.drawn.elems <;> rfl

section
variable {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}
  {G F : Fork} {mask : Nat → Cb.Gl.E} {n : Nat}

/-- **Scalars sent outside a sumcheck**: each slot is worth the part's own word. i: the part's
number. nn: how many scalars it sends. R: its round. es: the entries under which the tape is laid.
j0: its first slot. n: the slot from which the coins are counted. hb: its coins lie in front of the
row's last. -/
theorem scalars_field (Pl : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (hL : Later G F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hmask : ∀ j, j + 1 < spentTo (k4RowIn Q) (k4RowIn Q).length →
      mask (n + j) = Reading.gl.val ((spentOf _ c).getD j zeroE))
    (i nn : Nat) (f : K4Pub → K4In → Pts → List OnBytes.E)
    (hp : (k4RowIn Q)[i]? = some (k4Scalars Q nn f i)) (R : Nat)
    (hR : movesTo (k4RowIn Q) i = R) (es : List Fmt.Entry) (j0 : Nat)
    (hU : ∀ e, e < nn → Under G (j0 + e)
      ((sentOf ((paired (roundsOf y.1) es).drop R)).getD e zeroE) OnBytes.oneE)
    (hn : j0 = n + spentTo (k4RowIn Q) i)
    (hb : spentTo (k4RowIn Q) i + nn < spentTo (k4RowIn Q) (k4RowIn Q).length) :
    ∀ e, e < nn → (F.worldOf Reading.gl mask entry).slot (j0 + e) =
      Reading.gl.val ((f Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take R))).getD e zeroE) := by
  intro e he
  subst hR
  refine slot_value entry (hU e he) hL
    (coin := Reading.gl.val ((spentOf _ c).getD (spentTo (k4RowIn Q) i + e) zeroE)) ?_ ?_
  · rw [paired_sent, Reading.gl.one, one_mul]
    exact scalars_said Pl i nn f hp e he
  · rw [hn, Nat.add_assoc]
    exact hmask _ (by omega)

/-- **A sumcheck's claimed sum**: its slot is worth the job's first lead. The letters: as in
`scalars_field`. -/
theorem lead_field (Pl : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (hL : Later G F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hmask : ∀ j, j + 1 < spentTo (k4RowIn Q) (k4RowIn Q).length →
      mask (n + j) = Reading.gl.val ((spentOf _ c).getD j zeroE))
    (i : Nat) (name endName : String) (J : SumJob K4In Unit)
    (hp : (k4RowIn Q)[i]? = some (sumPart name endName J)) (hl : 0 < J.shape.lead) (R : Nat)
    (hR : movesTo (k4RowIn Q) i = R) (es : List Fmt.Entry) (j0 : Nat)
    (hU : Under G j0 (tapeCl ((paired (roundsOf y.1) es).drop R)) OnBytes.oneE)
    (hn : j0 = n + spentTo (k4RowIn Q) i)
    (hb : spentTo (k4RowIn Q) i + 1 < spentTo (k4RowIn Q) (k4RowIn Q).length) :
    (F.worldOf Reading.gl mask entry).slot j0 =
      Reading.gl.val ((J.lead (k4Wit Q cells weights tokens (look Q) m.st.input)
        (frontAt m ds y R)).getD 0 zeroE) := by
  subst hR
  refine slot_value entry hU hL
    (coin := Reading.gl.val ((spentOf _ c).getD (spentTo (k4RowIn Q) i + 0) zeroE)) ?_ ?_
  · rw [tapeCl_sent, paired_sent, headD_getD, Reading.gl.one, one_mul]
    exact lead_said Pl i name endName J hp 0 hl
  · rw [hn]
    exact hmask _ hb

/-- **A sumcheck's end values**: each slot is worth the job's end value at the variables'
challenges. R: the part's first round. nv: the number of its variables. ow: the coins of its first
run. ne: the number of its end values. j0: the first end value's slot. The other letters: as in
`scalars_field`. -/
theorem ends_field (Pl : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (hL : Later G F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hmask : ∀ j, j + 1 < spentTo (k4RowIn Q) (k4RowIn Q).length →
      mask (n + j) = Reading.gl.val ((spentOf _ c).getD j zeroE))
    (i : Nat) (name endName : String) (J : SumJob K4In Unit)
    (hp : (k4RowIn Q)[i]? = some (sumPart name endName J)) (dY ne : Nat)
    (hen : J.shape.ends = some ⟨dY, ne⟩) (R nv ow : Nat) (hR : movesTo (k4RowIn Q) i = R)
    (hv : J.shape.vs.length = nv) (ho : ownRun J.shape = ow) (es : List Fmt.Entry) (j0 : Nat)
    (hU : EndsUnder G (paired (roundsOf y.1) es) R nv j0 ne)
    (hn : j0 = n + (spentTo (k4RowIn Q) i + ow))
    (hb : spentTo (k4RowIn Q) i + ow + ne < spentTo (k4RowIn Q) (k4RowIn Q).length) :
    ∀ e, e < ne → (F.worldOf Reading.gl mask entry).slot (j0 + e) =
      Reading.gl.val ((J.ends (k4Wit Q cells weights tokens (look Q) m.st.input)
        (frontAt m ds y R) (ownE ds (R + 1) nv)).getD e zeroE) := by
  intro e he
  subst hR hv ho
  obtain ⟨⟨l, _, hy⟩, _⟩ := Pl.moved
  refine slot_value entry (hU e he) hL
    (coin := Reading.gl.val
      ((spentOf _ c).getD (spentTo (k4RowIn Q) i + ownRun J.shape + e) zeroE)) ?_ ?_
  · rw [paired_sent, tape_beta hy]
    exact ends_said Pl i name endName J hp ⟨dY, ne⟩ hen e he
  · rw [hn, Nat.add_assoc]
    exact hmask _ (by omega)

end

/-! ## 4 The honest words, and the statement -/

/-- A job's lead number e, or 0. -/
def leadWord (j : Option Job) (e : Nat) : OnBytes.E := ((j.map (·.lead)).getD []).getD e zeroE

/-- A job's end value number e at the variables' challenges rs, or 0. -/
def endWord (j : Option Job) (rs : List OnBytes.E) (e : Nat) : OnBytes.E :=
  ((j.map (·.ends rs)).getD []).getD e zeroE

/-- **EACH SLOT IS WORTH THE HONEST PART's OWN WORD UNDER THE MAP `Reading.gl.val`**, one field for
each run of slots: sums, prods, cl8, ends8, emb bear the names of `Opened`'s fields; sq is its sqL
and sqR; terms its rt, sc and sel, with the claimed sum; lv1, lv2 its lv1L to lv2R; stack holds
`OpenedBack`'s sideA and sideB among its end values. Beside them the ties among the hearing's names
for slots of one run. w: the small input. h: the challenges heard in front of the
member. ds: the member's own. seen: the rounds shown in front of the batched sumcheck. The batched
sumcheck's end values, by number from `sA0`: 0: one side's; 1: `sH1`; 2 + lm: the further gated
values; 2 + LamM: the other side's, `sB0`; from 3 + LamM on: `sV`, the merged claims'. It is a
definition. -/
structure OpenedLeft (Wd : World Cb.Gl.E) (Q : K4Pub) (o : Own) (w : K4In)
    (h ds : List Fmt.Drawn) (seen : Seen) : Prop where
  sums : ∀ i, i < ledNS Q.P.y.h.xl * Q.P.y.NI → Wd.slot (o.H.sW + i) =
    Reading.gl.val ((wSums Q w (ptsOf Q w (h ++ ds.take (k0 Q.g)))).getD i zeroE)
  sq : ∀ e, e < 2 → Wd.slot (o.H.wpl.sL + e) =
    Reading.gl.val (endWord (jobSquares Q w (ptsOf Q w (h ++ ds.take (rJ1 Q.g))))
      (ownE ds (rJ1 Q.g + 1) Q.P.rd.muV) e)
  sR : o.H.wpl.sR = o.H.wpl.sL + 1
  prods : ∀ i, i < ledNP Q.P.y.h.xl * Q.P.y.NI → Wd.slot (o.H.sPv + i) =
    Reading.gl.val ((rowProducts Q w (ptsOf Q w (h ++ ds.take (rowsRound Q.P Q.g)))).getD i zeroE)
  cl8 : Wd.slot o.H.tV.sCl =
    Reading.gl.val (leadWord (jobRows Q w (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g)))) 0)
  ends8 : ∀ e, e < ledNO Q.P.y.h.xl * Q.P.y.NI → Wd.slot (o.H.tV.sEnd + e) =
    Reading.gl.val (endWord (jobRows Q w (ptsOf Q w (h ++ ds.take (rJ2 Q.P Q.g))))
      (ownE ds (rJ2 Q.P Q.g + 1) Q.P.y.h.lt) e)
  terms : ∀ tT, o.H.tT = some tT →
    Wd.slot tT.sCl =
      Reading.gl.val (leadWord (jobTerms Q w (ptsOf Q w (h ++ ds.take (rJ3 Q.P Q.g)))) 0) ∧
    ∀ e, e < nEndT Q.P.y → Wd.slot (tT.sEnd + e) =
      Reading.gl.val (endWord (jobTerms Q w (ptsOf Q w (h ++ ds.take (rJ3 Q.P Q.g))))
        (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt) e)
  stack : ∀ e, e < nStack Q.P Q.hp Q.g → Wd.slot (o.K.sA0 + e) =
    Reading.gl.val (endWord (jobStack Q w (ptsOf Q w (h ++ ds.take (rJ4 Q.P Q.g)))
      (k4SentAt seen.rounds (k4TermsEnds Q))) (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS) e)
  sH1 : o.K.sH1 = o.K.sA0 + 1
  sB0 : o.K.sB0 = o.K.sA0 + (1 + (1 + Q.P.y.LamM))
  sV : o.K.sV = o.K.sB0 + 1
  lv1 : ∀ e, e < 2 → Wd.slot (o.hd.sL + e) =
    Reading.gl.val (endWord (jobGated Q w (ptsOf Q w (h ++ ds.take (rJ5 Q.P Q.hp Q.g))))
      (ownE ds (rJ5 Q.P Q.hp Q.g + 1) Q.P.rd.muH) e)
  hR : o.hd.sR = o.hd.sL + 1
  lv2 : ∀ o2, o.hd2 = some o2 → o2.sR = o2.sL + 1 ∧ ∀ e, e < 2 → Wd.slot (o2.sL + e) =
    Reading.gl.val (endWord (jobGated2 Q w (ptsOf Q w (h ++ ds.take (rJ6 Q.P Q.hp Q.g))))
      (ownE ds (rJ6 Q.P Q.hp Q.g + 1) Q.P.rd.muH2) e)
  emb : (Q.g == 0) = true → Wd.slot o.sVE =
    Reading.gl.val (embValue Q w (ptsOf Q w (h ++ ds.take (rE Q.P Q.hp Q.g))))

/-- **A STAND GIVES IT**, at every continuation ds' of the challenges heard, every ledger F later
than the one that the step leaves, and every entry. CONDITIONAL on the named premises. -/
theorem opened_left
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E) :
    OpenedLeft
      (F.worldOf Reading.gl
        (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask entry)
      Q o (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds
      (m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g)))) := by
  obtain ⟨a, c, _, U, N, Pl, hmask⟩ := stand_ground Z
  have R := k4_row_nums Q
  have hm := hmask ds'
  obtain ⟨tT, hT⟩ := N.hasT
  obtain ⟨o2, h2⟩ := N.has2
  obtain ⟨t1, t2, t3⟩ := N.terms tT hT
  obtain ⟨g1, g2, g3⟩ := N.lv2 o2 h2
  have nW := N.sW
  have nL := N.sL
  have nPv := N.sPv
  have nCl := N.sCl
  have nEnd := N.sEnd
  have nhL := N.hL
  have cW := R.cW
  have c1 := R.c1
  have cP := R.cP
  have c2 := R.c2
  have c3 := R.c3
  have c4 := R.c4
  have c5 := R.c5
  have c6 := R.c6
  have cE := R.cE
  have more := R.more
  refine
    { sums := scalars_field Pl hL entry hm (k0 Q.g) _ wSums (k4RowIn_at Q 0) _ R.mW _ _ U.sums
        (by omega) (by omega)
      sq := ends_field Pl hL entry hm (k0 Q.g + 2) _ _ _ (k4RowIn_at Q 2) 2 2 rfl _ _ _ R.m1
        List.length_replicate (ownRun_shapes Q.P.rd.muV 0 0 0 0).1 _ _ U.sq (by omega) (by omega)
      sR := N.sR
      prods := scalars_field Pl hL entry hm (k0 Q.g + 4) _ rowProducts (k4RowIn_at Q 4) _ R.mP _ _
        U.prods (by omega) (by omega)
      cl8 := lead_field Pl hL entry hm (k0 Q.g + 5) _ _ _ (k4RowIn_at Q 5) Nat.one_pos _ R.m2 _ _
        U.cl8 (by omega) (by omega)
      ends8 := ends_field Pl hL entry hm (k0 Q.g + 5) _ _ _ (k4RowIn_at Q 5) 2 _ rfl _ _ _ R.m2
        List.length_replicate (ownRun_shapes 0 Q.P.y.h.lt 0 2 _).2.1 _ _ U.ends8 (by omega)
        (by omega)
      terms := fun tT' hT' => ?_
      stack := ends_field Pl hL entry hm (k0 Q.g + 8) _ _ _ (k4RowIn_at Q 8) 2 _ rfl _ _ _ R.m4
        List.length_replicate (ownRun_shapes 0 0 Q.hp.lamS 2 _).2.2 _ _ U.stack (by omega)
        (by omega)
      sH1 := N.sH1
      sB0 := N.sB0
      sV := N.sV
      lv1 := ends_field Pl hL entry hm (k0 Q.g + 9) _ _ _ (k4RowIn_at Q 9) 2 2 rfl _ _ _ R.m5
        List.length_replicate (ownRun_shapes Q.P.rd.muH 0 0 0 0).1 _ _ U.lv1 (by omega) (by omega)
      hR := N.hR
      lv2 := fun o2' h2' => ?_
      emb := fun hg => ?_ }
  · obtain rfl : tT = tT' := Option.some.inj (hT.symm.trans hT')
    exact ⟨lead_field Pl hL entry hm (k0 Q.g + 6) _ _ _ (k4RowIn_at Q 6) Nat.one_pos _ R.m3 _ _
        (U.terms tT hT).1 (by omega) (by omega),
      ends_field Pl hL entry hm (k0 Q.g + 6) _ _ _ (k4RowIn_at Q 6) 1 _ rfl _ _ _ R.m3
        List.length_replicate (ownRun_shapes 0 Q.P.y.h.lt 0 1 _).2.1 _ _ (U.terms tT hT).2
        (by omega) (by omega)⟩
  · obtain rfl : o2 = o2' := Option.some.inj (h2.symm.trans h2')
    exact ⟨g2, ends_field Pl hL entry hm (k0 Q.g + 12) _ _ _ (k4RowIn_at Q 12) 2 2 rfl _ _ _ R.m6
      List.length_replicate (ownRun_shapes Q.P.rd.muH2 0 0 0 0).1 _ _ (U.lv2 o2 h2) (by omega)
      (by omega)⟩
  · have hp : (k4RowIn Q)[k0 Q.g + 14]? =
        some (k4Scalars Q 1 (fun Q w p => [embValue Q w p]) (k0 Q.g + 14)) := by
      rw [k4RowIn_at]
      show some (if Q.g == 0 then _ else _) = _
      rw [if_pos hg]
    have g3' := g3 hg
    exact scalars_field Pl hL entry hm (k0 Q.g + 14) 1 _ hp _ R.mE _ o.sVE
      (fun e he => by
        obtain rfl : e = 0 := by omega
        exact U.emb hg) (by omega) (by omega) 0 Nat.one_pos

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stand_ground
#print axioms ProofFile.Honest.K4.stand_look
#print axioms ProofFile.Honest.K4.stand_seen
#print axioms ProofFile.Honest.K4.stand_lens
#print axioms ProofFile.Honest.K4.tape_beta
#print axioms ProofFile.Honest.K4.scalars_field
#print axioms ProofFile.Honest.K4.lead_field
#print axioms ProofFile.Honest.K4.ends_field
#print axioms ProofFile.Honest.K4.opened_left
