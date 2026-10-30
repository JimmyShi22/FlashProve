-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SaidKit.lean: CONDITIONAL.

Not shown here. No property is claimed. That `K4Seated` (Law/Seated.lean) can be met: no example is
known. ONE WAY, FROM A RETURN of the frame's `play`. THE VALUE IS THE PART's OWN WORD, as its text
has it, padded with 0 where a list is too short: nothing says what that word means. Nothing on what
a verifier does with what a round shows. Nothing on the law of any coin. Nothing on soundness, on
completeness or on any other property. WHAT IT IMPORTS, by a walk over import lines: no module under
Johnson/Goal/ or Johnson/D/; seven under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs,
Cms, Bcs), which come with a module of the library (Johnson/E/KObj/ProofFile.lean) through
Law/RowBatch.lean: nothing here names one of them.

What is here: what a round of the played row of the layers' own rounds (the sub-protocol K4) shows,
under the map `Reading.gl.val` into the field, for the three sorts of message that carry a value
under a mask entry: scalars sent outside a sumcheck; a sumcheck's lead; a sumcheck's end values.
General in the part's number, and in the sumcheck's job as far as the part stands in K4's row.
Definitions, and statements with their proofs, over Law/RowKit.lean and the general statements on
the masked sumcheck's part (Honest/SumLaw/).

  `frontAt m ds y R`   what a part whose first round is number R of the row is handed of the run:
      the challenges and the rounds shown in front of it
  `ownE ds R n`   the first elements of the n challenges from number R of the row on
  `sentAt y R`   the scalars that round number R of the row shows, as the verifier's tape takes them
  `K4Played …`   the premises that these statements share, as one structure: the seat; the prover's
      side of the member's step; what the book lends the row (`lendRow`, Honest/Frame.lean)
  `k4SeatOf`, `k4_said`, `k4_coin`   a part of the row, seated; one statement for every move that
      says scalars; a part's coins in the row's list of spent coins
  `scalars_said`   value plus coin
  `lead_said`   a sumcheck's first message: each lead's value plus its coin
  `ends_said`   a sumcheck's last message: each end value plus the challenge of the round in the
      further variable times its coin
  `played_length`, `ownE_length`, `sum_rounds_there`, `sum_vars_length`   as many rounds are played
      as there are challenges; how long `ownE` is; a sumcheck's rounds are all there; so its
      variables' challenges are as many as its variables
  `slot_value`   the last step, free of the frame: under a slot lie x and f; x is mapped to
      v + f · c; the mask row's entry there is c: so in the world of every later ledger the slot is
      worth v

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Fork)
open OnBytes.K.Kc (leading)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Part.MaskedSum (Ends)
open ProofFile.Honest.SumLaw (mvOf askG askG_at saidFirst saidEnds sumGs sumPart_moves firstRun endRun
  canon canon_gl)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-! ## 1 What a part is handed, and what a round shows -/

/-- What a part whose first round is number R of the row is handed of the run. -/
def frontAt {W Z : Type} (m : Mid W Z) (ds : List Fmt.Drawn) (y : List Played × Mid W Z) (R : Nat) :
    Front Unit :=
  ⟨m.st.heard ++ ds.take R, (), m.shown.plus (roundsOf (y.1.take R))⟩

/-- The first elements of the n challenges from number R of the row on. -/
def ownE (ds : List Fmt.Drawn) (R n : Nat) : List OnBytes.E := drawnE ((ds.drop R).take n)

/-- The scalars that round number R of the row shows. -/
def sentAt {W Z : Type} (y : List Played × Mid W Z) (R : Nat) : List OnBytes.E :=
  (((roundsOf y.1)[R]?).map fun r => leading r.vals).getD []

/-- A part of K4's row at the small input, seated as `k4Row` (Honest/K4/Part.lean) seats it. -/
abbrev k4SeatOf (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (lk : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (P₀ : Part Unit K4In Unit) :
    Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  P₀.lift (fun _ => ()) (k4Wit Q cells weights tokens lk) (fun _ => ()) fun x _ => x

/-- **The premises that the statements on a played row share.** c: what the book lends the row. It
is a definition: a premise's form. Nothing is claimed of it. -/
structure K4Played (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (b : Nat) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub) (p : Par)
    (blk : Block First.S Claim) (k : Coins Bk) (m : Mid (Local W₀ Rc Xi Tr) X) (E : Env)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc Xi Tr) X)
    (cols : List VerifiableInference.Desc.OpenedColumn)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts) : Prop where
  seat : K4Seated T b cells weights tokens look Q p blk
  moved : T.Moved blk k m E ds y cols
  lent : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
    (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn}
  {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}

/-! ## 2 One statement for every move that says scalars -/

/-- **What round `movesTo` + r of the played row shows, where move number r of part number i says
scalars**: these scalars, each with its three words reduced below the prime, at the part's coins,
the rounds shown and the challenges heard in front of that round. With it: the seated part with its
coins, as the row holds them; and that the round has been played. -/
theorem k4_said (Z : K4Played T b cells weights tokens look Q p blk k m E ds y cols c) (i : Nat)
    (P₀ : Part Unit K4In Unit) (hp : (k4RowIn Q)[i]? = some P₀) (r : Nat)
    (g : P₀.Coins → Seen → State K4In Unit → List OnBytes.E)
    (hm : P₀.moves[r]? = some (mvOf g)) :
    ∃ cp : P₀.Coins,
      rowAt? (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts c i =
        some ⟨k4SeatOf Q cells weights tokens (look Q) P₀, cp⟩ ∧
      movesTo (k4RowIn Q) i + r < (roundsOf y.1).length ∧
      sentAt y (movesTo (k4RowIn Q) i + r) =
        (g cp (m.shown.plus (roundsOf (y.1.take (movesTo (k4RowIn Q) i + r))))
          ⟨k4Wit Q cells weights tokens (look Q) m.st.input,
            m.st.heard ++ ds.take (movesTo (k4RowIn Q) i + r), ()⟩).map canon := by
  obtain ⟨⟨l, hl, hy⟩, _⟩ := Z.moved
  have hc' : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c := by
    rw [Z.seat.place]
    exact Z.lent
  have hpart : (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts[i]? =
      some (k4SeatOf Q cells weights tokens (look Q) P₀) := by
    show ((k4RowIn Q).map _)[i]? = _
    rw [List.getElem?_map, hp]
    rfl
  obtain ⟨cp, hcp⟩ := rowAt_some _ c _ _ hpart
  have hmv : (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q) P₀).moves[r]? =
      some (Move.lift (k4Wit Q cells weights tokens (look Q)) (fun _ => ()) (fun x _ => x)
        (mvOf g)) := by
    show (P₀.moves.map _)[r]? = _
    rw [List.getElem?_map, hm]
    rfl
  have hmt : movesTo (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts i =
      movesTo (k4RowIn Q) i := movesTo_lift _ _ _ _ _ i
  obtain ⟨st, z, e1, e2, e3, e4, _⟩ := row_said hl Z.seat.half hc' hy i _ cp hcp r _ hmv
    (row_lt hl Z.seat.half i _ r hpart (List.getElem?_eq_some_iff.1 hmv).1)
  rw [hmt] at e2 e3 e4
  have hz : z = sayE (g cp (m.shown.plus (roundsOf (y.1.take (movesTo (k4RowIn Q) i + r))))
      ⟨k4Wit Q cells weights tokens (look Q) st.input, st.heard, ()⟩) := (Except.ok.inj e3).symm
  rw [e1, e2] at hz
  refine ⟨cp, hcp, ?_, ?_⟩
  · cases hq : (roundsOf y.1)[movesTo (k4RowIn Q) i + r]? with
    | none =>
      rw [hq] at e4
      cases e4
    | some _ => exact (List.getElem?_eq_some_iff.1 hq).1
  · have h5 := congrArg (Option.map leading) e4
    rw [Option.map_map] at h5
    have h6 : ((roundsOf y.1)[movesTo (k4RowIn Q) i + r]?).map (fun r => leading r.vals) =
        some (leading (z.vals.map Said.got)) := h5
    unfold sentAt
    rw [h6, Option.getD_some, hz, leading_sayE]

/-- **A part's coins in the row's list of spent coins.** -/
theorem k4_coin (i : Nat) (P₀ : Part Unit K4In Unit) (cp : P₀.Coins)
    (hcp : rowAt? (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts c i =
      some ⟨k4SeatOf Q cells weights tokens (look Q) P₀, cp⟩) (j : Nat) (hj : j < coinsIn P₀) :
    (spentOf _ c).getD (spentTo (k4RowIn Q) i + j) zeroE =
      (runsE P₀.spends cp.2.1).getD j zeroE := by
  have h := spentOf_at _ c i (k4SeatOf Q cells weights tokens (look Q) P₀) cp hcp j hj
  have hs : spentTo (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts i =
      spentTo (k4RowIn Q) i := spentTo_lift _ _ _ _ _ i
  rw [hs] at h
  exact h

/-- The end values' run, as the part reads it. -/
theorem runsE_ends (endName : String) : ∀ (o : Option Ends) (cs : CsAll (endRuns endName o)),
    runsE (endRuns endName o) cs = endCoins endName o cs
  | none, _ => rfl
  | some _, cs => List.append_nil (coinsE cs.1)

/-- The variables' challenges among a sumcheck's own. -/
theorem ownE_vars (ds : List Fmt.Drawn) (R nv : Nat) :
    ((ownE ds R (nv + 2)).drop 1).take nv = ownE ds (R + 1) nv := by
  unfold ownE drawnE
  rw [← List.map_drop, ← List.map_take, List.drop_take, List.drop_drop, List.take_take]
  congr 2
  omega

/-- The further variable's challenge among a sumcheck's own. -/
theorem ownE_last (ds : List Fmt.Drawn) (R nv : Nat) (h : R + (nv + 1) < ds.length) :
    (ownE ds R (nv + 2)).getLastD zeroE = (ownE ds (R + (nv + 1)) 1).headD zeroE := by
  obtain ⟨d, hd⟩ : ∃ d, ds[R + (nv + 1)]? = some d := ⟨_, List.getElem?_eq_getElem h⟩
  have e1 : (ds.drop R).take (nv + 2) = (ds.drop R).take (nv + 1) ++ [d] := by
    have q := List.take_add_one (l := ds.drop R) (i := nv + 1)
    rw [List.getElem?_drop, hd] at q
    exact q
  have e2 : (ds.drop (R + (nv + 1))).take 1 = [d] := by
    have q := List.take_add_one (l := ds.drop (R + (nv + 1))) (i := 0)
    have g : (ds.drop (R + (nv + 1)))[0]? = some d := by
      rw [List.getElem?_drop]
      exact hd
    rw [g] at q
    exact q
  unfold ownE drawnE
  rw [e1, e2, List.map_append]
  simp

/-- The moves of a sumcheck's part: the last says the end values. -/
theorem sumGs_ends (name endName : String) (J : SumJob K4In Unit) (en : Ends)
    (hen : J.shape.ends = some en) :
    (sumGs name endName J)[J.shape.vs.length + 2]? =
      some (askG name endName J (saidEnds J en) (J.shape.vs.length + 2)) := by
  unfold sumGs
  rw [hen]
  have l : ([askG name endName J (saidFirst J) 0] ++
      (List.range J.shape.vs.length).map fun i =>
        askG name endName J (SumLaw.saidVar J i) (i + 1)).length = J.shape.vs.length + 1 := by
    simp
  rw [List.getElem?_append_right (by rw [l]; omega), l,
    show J.shape.vs.length + 2 - (J.shape.vs.length + 1) = 1 from by omega]
  rfl

/-! ## 3 The three sorts of message -/

/-- **Scalars sent outside a sumcheck: value plus coin.** i: the part's number. -/
theorem scalars_said (Z : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (i n : Nat) (f : K4Pub → K4In → Pts → List OnBytes.E)
    (hp : (k4RowIn Q)[i]? = some (k4Scalars Q n f i)) (e : Nat) (he : e < n) :
    Reading.gl.val ((sentAt y (movesTo (k4RowIn Q) i)).getD e zeroE) =
      Reading.gl.val ((f Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (movesTo (k4RowIn Q) i)))).getD e zeroE) +
      Reading.gl.val ((spentOf _ c).getD (spentTo (k4RowIn Q) i + e) zeroE) := by
  obtain ⟨cp, hcp, _, hs⟩ := k4_said Z i _ hp 0
    (fun c _ t => addL (padTo n (f Q t.input (ptsOf Q t.input t.heard))) (coinsE c.2.1.1)) rfl
  rw [Nat.add_zero] at hs
  have hcoin := (k4_coin i _ cp hcp e he).trans
    (runsE_first (runName maskRowRun (k4Addr Q i) "scalars", ⟨0, n⟩) [] cp.2.1 e he)
  rw [hs, SumLaw.map_getD Reading.gl canon canon_gl, SumLaw.addL_getD, SumLaw.padTo_getD,
    if_pos he, hcoin]

/-- **A sumcheck's first message: each lead's value plus its coin.** -/
theorem lead_said (Z : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (i : Nat) (name endName : String) (J : SumJob K4In Unit)
    (hp : (k4RowIn Q)[i]? = some (sumPart name endName J)) (e : Nat) (he : e < J.shape.lead) :
    Reading.gl.val ((sentAt y (movesTo (k4RowIn Q) i)).getD e zeroE) =
      Reading.gl.val ((J.lead (k4Wit Q cells weights tokens (look Q) m.st.input)
        (frontAt m ds y (movesTo (k4RowIn Q) i))).getD e zeroE) +
      Reading.gl.val ((spentOf _ c).getD (spentTo (k4RowIn Q) i + e) zeroE) := by
  have hm : (sumPart (V := Unit) name endName J).moves[0]? =
      some (mvOf (askG name endName J (saidFirst J) 0)) := by
    rw [sumPart_moves]
    rfl
  obtain ⟨cp, hcp, _, hs⟩ := k4_said Z i _ hp 0 _ hm
  rw [Nat.add_zero] at hs
  have ha := askG_at name endName J (saidFirst J) 0 cp
    (k4Wit Q cells weights tokens (look Q) m.st.input)
    (m.st.heard ++ ds.take (movesTo (k4RowIn Q) i)) [] ()
    (m.shown.plus (roundsOf (y.1.take (movesTo (k4RowIn Q) i)))) [] rfl rfl
  rw [Seen.plus_nil, List.append_nil] at ha
  have hown : e < ownRun J.shape := Nat.lt_of_lt_of_le he (Nat.le_add_right _ _)
  have hcoin := (k4_coin i _ cp hcp e (Nat.lt_of_lt_of_le hown (Nat.le_add_right _ _))).trans
    (runsE_first (name, ⟨0, ownRun J.shape⟩) (endRuns endName J.shape.ends) cp.2.1 e hown)
  have htk : ((firstRun cp).take J.shape.lead).getD e zeroE = (coinsE cp.2.1.1).getD e zeroE := by
    unfold firstRun
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt he]
  rw [hs, ha, SumLaw.map_getD Reading.gl canon canon_gl]
  show Reading.gl.val ((addL (padTo J.shape.lead _) ((firstRun cp).take J.shape.lead) ++
    [_]).getD e zeroE) = _
  rw [List.getD_append _ _ _ _ (by
      rw [SumLaw.addL_length, SumLaw.padTo_length]
      exact lt_max_of_lt_left he),
    SumLaw.addL_getD, SumLaw.padTo_getD, if_pos he, htk, hcoin]
  rfl

/-- **A sumcheck's last message: each end value plus the challenge of the round in the further
variable times its coin.** The part's own challenges: first the one behind its first message, then
one for each variable, then the further variable's. -/
theorem ends_said (Z : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (i : Nat) (name endName : String) (J : SumJob K4In Unit)
    (hp : (k4RowIn Q)[i]? = some (sumPart name endName J)) (en : Ends)
    (hen : J.shape.ends = some en) (e : Nat) (he : e < en.n) :
    Reading.gl.val
        ((sentAt y (movesTo (k4RowIn Q) i + (J.shape.vs.length + 2))).getD e zeroE) =
      Reading.gl.val ((J.ends (k4Wit Q cells weights tokens (look Q) m.st.input)
        (frontAt m ds y (movesTo (k4RowIn Q) i))
        (ownE ds (movesTo (k4RowIn Q) i + 1) J.shape.vs.length)).getD e zeroE) +
      Reading.gl.val
          ((ownE ds (movesTo (k4RowIn Q) i + (J.shape.vs.length + 1)) 1).headD zeroE) *
        Reading.gl.val
          ((spentOf _ c).getD (spentTo (k4RowIn Q) i + ownRun J.shape + e) zeroE) := by
  have hm : (sumPart (V := Unit) name endName J).moves[J.shape.vs.length + 2]? =
      some (mvOf (askG name endName J (saidEnds J en) (J.shape.vs.length + 2))) := by
    rw [sumPart_moves]
    refine List.getElem?_map.trans ?_
    rw [sumGs_ends name endName J en hen]
    rfl
  obtain ⟨cp, hcp, hlt, hs⟩ := k4_said Z i _ hp (J.shape.vs.length + 2) _ hm
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.moved
  have hdl : (roundsOf y.1).length = ds.length := by
    have h := congrArg List.length (yields_drawn l ds [] y.1 (play_yields l ds [] m y hy))
    rw [List.length_map] at h
    exact h
  have hyl : (roundsOf y.1).length = y.1.length := List.length_map _
  have h1 : m.st.heard ++ ds.take (movesTo (k4RowIn Q) i + (J.shape.vs.length + 2)) =
      (m.st.heard ++ ds.take (movesTo (k4RowIn Q) i)) ++
        (ds.drop (movesTo (k4RowIn Q) i)).take (J.shape.vs.length + 2) := by
    rw [List.take_add, List.append_assoc]
  have h2 : m.shown.plus (roundsOf (y.1.take (movesTo (k4RowIn Q) i + (J.shape.vs.length + 2)))) =
      (m.shown.plus (roundsOf (y.1.take (movesTo (k4RowIn Q) i)))).plus
        (roundsOf ((y.1.drop (movesTo (k4RowIn Q) i)).take (J.shape.vs.length + 2))) := by
    rw [Seen.plus_plus]
    unfold roundsOf
    rw [List.take_add, List.map_append]
  have l1 : ((ds.drop (movesTo (k4RowIn Q) i)).take (J.shape.vs.length + 2)).length =
      J.shape.vs.length + 2 := by
    rw [List.length_take, List.length_drop]
    omega
  have l2 : (roundsOf ((y.1.drop (movesTo (k4RowIn Q) i)).take (J.shape.vs.length + 2))).length =
      J.shape.vs.length + 2 := by
    unfold roundsOf
    rw [List.length_map, List.length_take, List.length_drop]
    omega
  have ha := askG_at name endName J (saidEnds J en) (J.shape.vs.length + 2) cp
    (k4Wit Q cells weights tokens (look Q) m.st.input)
    (m.st.heard ++ ds.take (movesTo (k4RowIn Q) i))
    ((ds.drop (movesTo (k4RowIn Q) i)).take (J.shape.vs.length + 2)) ()
    (m.shown.plus (roundsOf (y.1.take (movesTo (k4RowIn Q) i))))
    (roundsOf ((y.1.drop (movesTo (k4RowIn Q) i)).take (J.shape.vs.length + 2))) l1 l2
  have hsum : coinsIn (sumPart (V := Unit) name endName J) = ownRun J.shape + en.n := by
    show (((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends).map (·.2.e)).sum = _
    rw [hen]
    simp [endRuns]
  have hcoin := k4_coin i _ cp hcp (ownRun J.shape + e) (by rw [hsum]; omega)
  have hrun : (runsE ((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends)
      cp.2.1).getD (ownRun J.shape + e) zeroE = (endRun cp).getD e zeroE := by
    have e0 : runsE ((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends) cp.2.1 =
        coinsE cp.2.1.1 ++ runsE (endRuns endName J.shape.ends) cp.2.1.2 := rfl
    have l0 : (coinsE cp.2.1.1).length = ownRun J.shape := by simp [coinsE]
    rw [e0, List.getD_append_right _ _ _ _ (by rw [l0]; omega), l0, Nat.add_sub_cancel_left,
      runsE_ends]
    rfl
  rw [Nat.add_assoc, hcoin.trans hrun, hs, h1, h2, ha,
    SumLaw.map_getD Reading.gl canon canon_gl]
  show Reading.gl.val ((addL (padTo en.n _) (scaleL _ (padTo en.n (endRun cp)))).getD e zeroE) = _
  rw [SumLaw.addL_getD, SumLaw.padTo_getD, if_pos he, SumLaw.scaleL_getD, SumLaw.padTo_getD,
    if_pos he]
  have v1 := ownE_vars ds (movesTo (k4RowIn Q) i) J.shape.vs.length
  have v2 := ownE_last ds (movesTo (k4RowIn Q) i) J.shape.vs.length (by omega)
  unfold ownE at v1 v2
  rw [v1, v2]
  rfl

end

/-! ## 4 How many challenges -/

/-- As many rounds are played as there are challenges. -/
theorem played_length {W Z : Type} {l : List (Step W Z)} {ds : List Fmt.Drawn} {m : Mid W Z}
    {y : List Played × Mid W Z} (hy : play l ds [] m = .ok y) :
    (roundsOf y.1).length = ds.length := by
  have h := congrArg List.length (yields_drawn l ds [] y.1 (play_yields l ds [] m y hy))
  rw [List.length_map] at h
  exact h

/-- How long `ownE` is, where the challenges reach so far. -/
theorem ownE_length (ds : List Fmt.Drawn) (R n : Nat) (h : R + n ≤ ds.length) :
    (ownE ds R n).length = n := by
  unfold ownE drawnE
  rw [List.length_map, List.length_take, List.length_drop]
  omega

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn}
  {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}

/-- **A sumcheck's rounds are all there**: the challenges reach behind the round of its end values.
Of sumchecks with end values alone (hen). -/
theorem sum_rounds_there (Z : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (i : Nat) (name endName : String) (J : SumJob K4In Unit)
    (hp : (k4RowIn Q)[i]? = some (sumPart name endName J)) (en : Ends)
    (hen : J.shape.ends = some en) :
    movesTo (k4RowIn Q) i + (J.shape.vs.length + 2) < ds.length := by
  have hm : (sumPart (V := Unit) name endName J).moves[J.shape.vs.length + 2]? =
      some (mvOf (askG name endName J (saidEnds J en) (J.shape.vs.length + 2))) := by
    rw [sumPart_moves]
    refine List.getElem?_map.trans ?_
    rw [sumGs_ends name endName J en hen]
    rfl
  obtain ⟨_, _, hlt, _⟩ := k4_said Z i _ hp (J.shape.vs.length + 2) _ hm
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.moved
  rw [played_length hy] at hlt
  exact hlt

/-- **A sumcheck's variables' challenges are as many as its variables.** Of sumchecks with end
values alone (hen). No code of ours calls it: `stand_lens` (Law/SlotsTrue.lean) goes by
`ownE_length`. -/
theorem sum_vars_length (Z : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (i : Nat) (name endName : String) (J : SumJob K4In Unit)
    (hp : (k4RowIn Q)[i]? = some (sumPart name endName J)) (en : Ends)
    (hen : J.shape.ends = some en) :
    (ownE ds (movesTo (k4RowIn Q) i + 1) J.shape.vs.length).length = J.shape.vs.length := by
  have h := sum_rounds_there Z i name endName J hp en hen
  exact ownE_length ds _ _ (by omega)

end

/-! ## 5 The last step -/

/-- **In the world of every later ledger the slot is worth the value.** "Later" is
`OnBytes.PscRun.Later`, as in `Under.later` (Law/RowsLedger.lean); the library's `Fo.Later`, which
Law/SlotsUnder.lean's two statements on a sumcheck's end values ask, is another relation:
`later_fo` (OnBytes/Desc/First/K4/TermsShown.lean) leads from the first to the second. -/
theorem slot_value {G F : Fork} {j : Nat} {x f : OnBytes.E} {mask : Nat → Cb.Gl.E}
    (entry : Nat → Nat → Nat → Cb.Gl.E) {v coin : Cb.Gl.E} (hU : Under G j x f) (hL : Later G F)
    (hx : Reading.gl.val x = v + Reading.gl.val f * coin) (hm : mask j = coin) :
    (F.worldOf Reading.gl mask entry).slot j = v := by
  show Reading.gl.val (F.vp.getD j zeroE) - Reading.gl.val (F.mf.getD j zeroE) * mask j = v
  rw [(hL.keep j hU.filled).2.1, (hL.keep j hU.filled).2.2, hU.shown, hU.factor, hx, hm]
  ring

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_said
#print axioms ProofFile.Honest.K4.k4_coin
#print axioms ProofFile.Honest.K4.runsE_ends
#print axioms ProofFile.Honest.K4.ownE_vars
#print axioms ProofFile.Honest.K4.ownE_last
#print axioms ProofFile.Honest.K4.sumGs_ends
#print axioms ProofFile.Honest.K4.scalars_said
#print axioms ProofFile.Honest.K4.lead_said
#print axioms ProofFile.Honest.K4.ends_said
#print axioms ProofFile.Honest.K4.played_length
#print axioms ProofFile.Honest.K4.ownE_length
#print axioms ProofFile.Honest.K4.sum_rounds_there
#print axioms ProofFile.Honest.K4.sum_vars_length
#print axioms ProofFile.Honest.K4.slot_value
