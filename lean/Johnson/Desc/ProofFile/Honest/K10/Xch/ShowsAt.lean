-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/ShowsAt.lean: the closing of a segment (K10), at the first chain's thread under
the library's head: where the thread's invariant holds and the closing's block has accepted a step, the rounds as
played show the hiding polynomial's sum and the honest round polynomials, at the tables made of the prover's own rows,
under the premises named below. At the exact carry the sentence is the premise hShows of `exchange_carry_at_head`
(Honest/K10/Xch/Carry.lean); here it is stated at each value of carryX, and Xch/CarryTop.lean joins the two. It is
stated in the forms of Xch/Shown.lean. Five lemmas alone.

Words.
  the head            the library's hypothesis `P5J.AtMgA` at the older hash (Johnson/P5J/MgAtAll.lean), h; its first
                      part is `P5J.AtMg`. cF is the head's own first chain, Zp its public part
  the head's thread   `(lettersHead h H Sc test carryX …).thread` (Honest/Thread/FirstHead.lean): the structure of
                      parameters of the first chain's invariant `Thr` (Honest/Thread/Thr.lean). Border number b is the
                      point in front of cF's block number b; the closing of segment l stands at b = 14 l + `IM.nAt l`
                      + 5
  the block           blk with `Tied cF Zp l p Qc blk` (Honest/K10/SimLot.lean): cF's block at that number; Qc are the
                      closing's numbers
  the job             `CloseJob` (Honest/K10/Job.lean): a closing's parameters on the prover's side: among them
                      `stAt`, which makes the statement before "BAT", and `rows`, which makes the prover's own rows of
                      the group. The lot's job is `lotJob readers rows stAt Zp Gr Qc` (Honest/K10/Thr/HalfOfLot.lean)
  the record          `K9.recOf s` (Johnson/Desc/First/Batch/Place.lean): what the closing reads of the verifier's
                      state s
  the forms           `StepAt`, `rowWords`, `CoefOf`, `ShownAt`: Honest/K10/Xch/Shown.lean

What is proved.
  **`askZero_of_base_at_head`**
                      `askZero_of_base` (Honest/K10/Xch/Shows.lean) under `P5J.AtMg`, at the job whose statement is
                      made by `stAtZero` (Honest/K10/StAtZero.lean) off cF. Premises. hl: l < 25. T: `Tied`. hf: the
                      description's fold over cF's members in front of segment l's closing, from `start (xi w)` (start
                      and xi are variables), returns y at the rounds shown and at some columns. H: the facts
                      `CloseBase` (Johnson/Desc/K10/Honest/Base.lean) at the record of y's state. hh: the job's h is
                      the frame's group's. hr: `J.rows` returns rows R. hfit: `rowsFit` says yes of R. Conclusion, at
                      a challenge of the form ⟨[t], [], [], none⟩: the batching returns a row at t, and `askZero`
                      (Honest/K10/SimSent.lean) is some data, with its fields written out. `askZero_at_head`
                      (Honest/K10/Wipe/Speaks.lean) has the same premises and says "there are data"; here they are
                      named. The job's own numbers `J.pub.par`, at which H and hh speak, and the Q of `Tied`, at which
                      `stAtZero` is read, are two variables that nothing ties here
  **`shown_of_moved`**
                      at any thread T: `shows_at_moved` (Xch/Shows.lean) in the forms `CoefOf`, `ShownAt` and
                      `rowWords`, with the premises hr, ho, hp of `shows_at_moved`. The premise on `askZero` (hA) is
                      asked at every challenge of the form ⟨[t], [], [], none⟩; that what the first round drew has
                      this form comes from hf (`drawsFit`), by `close_draws_form` (Honest/K10/Wipe/DrawForm.lean)
  `thread_ahead`      at the head's thread the number of challenges heard before the chain (`Thread.front`) is 0
  `fold_at_thr`       wherever `Thr` holds at a border b of the head's thread, the description's fold over cF's first
                      b members, from the chain's own first state, at all rounds seen and at some columns, returns the
                      verifier's state: the last clause of `Thread.Made`
  **`shows_at_head`**
                      at each l < 25, at every value of the parameter carryX and every Said. Premises, in this order.
                      hF: `ClosingsFirst` (Thr/HalfOfLot.lean) of the prover's list of halves: at each closing's place
                      its first half has the lot's one part. hfill: the lot's stAt is `stAtZero` off cF from the
                      chain's own first state. Td: `Tied`. St: `StepAt`: the invariant and Said hold at the border,
                      the challenges fit the block's rounds, and the block has stepped from s to s'. Hb: `CloseBase`
                      at the record of s. hh: the h of Qc is the frame's group's. hlen: the main code's message length
                      is 2 ^ logEll. hcc: `closeCoins` (Honest/K10/Fast/Says.lean) returns the part's coins cc. hR,
                      hfit: the lot's job's rows at cc's carried runs are R, and `rowsFit` says yes of R. hrs: the
                      rounds as played are rB, rE, rR. hrow: the batching returns row at what rB drew. Conclusion:
                      there are coefficients Wc with `CoefOf` of the run that cc spends, and `ShownAt` holds at Wc and
                      at the tables of `rowWords D (K9.recOf s) R`

By what. `closeAsk_at_head` (Honest/K10/Wipe/AtHead.lean), `ask_of_base` (Honest/K10/AskLaw.lean); `moved_drawn`
(Honest/Thread/MovedDrawn.lean), `coefOf_cast` (Xch/Shown.lean); `closeAt_of_tied` (Honest/K10/Thr/AtThread.lean),
`tied_decides` (Honest/K10/Xch/Behind.lean). The lot's job at the stAt of hfill is, by unfolding, the job of
`askZero_of_base_at_head` at start := `ProofFile.startS Zp` and xi := the input's public instance.

The notation, and the option in front of it. 𝕋 stands for the head's thread, written out once; it declares nothing.
`set_option quotPrecheck false in` turns off, for that one command, Lean's early look through a notation's text, which
has no case for a field access; wherever 𝕋 is written the text is elaborated and checked as any term is (the head of
Honest/K10/Thr/AtThread.lean says more).

Limits. Every premise named above is a premise: none is shown here of any prover, state or run. hF and hfill are on
parameters of the prover. Hb, hh, hlen, and hR with hfit, are what the fields base, height, len and made of
`CarryDebt` (Xch/Carry.lean) ask: named there, and shown of no run. Where the invariant holds at no state of the
border, or the block accepts no step, `StepAt` holds of nothing and `shows_at_head` holds vacuously. The tables are
those of the prover's own rows R: that they are the tables of a witness's words (the field tie of `CarryDebt`), and
that a fresh table pairs with Wc (its field fresh), is not spoken of. "Show" is said of what the rounds send read in
the field, not word for word (the head of Xch/Shows.lean says why). Whether the head can be had at any files is
no lemma here. At the full size and the older hash alone. Nothing is shown of a run of the protocol. No property of
the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.Shows
import Johnson.Desc.ProofFile.Honest.K10.Xch.Shown
import Johnson.Desc.ProofFile.Honest.K10.Xch.Behind
import Johnson.Desc.ProofFile.Honest.K10.Thr.AtThread
import Johnson.Desc.ProofFile.Honest.K10.Wipe.DrawForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open Johnson.Prover.Link (drawnOf)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase ShapedAll)

/-! ## 1 The closing's data, by value, under the head -/

/-- **`askZero`'s value under the head**, at the job whose statement is made by `stAtZero` off the head's own chain: the
record is that of the state which the description's fold over the members in front of the closing reaches. -/
theorem askZero_of_base_at_head {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {W Xi : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) {l : Nat}
    (hl : l < 25) {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block TS ProofFile.Cl} (T : Tied cF Zp l p Q b)
    (J : CloseJob W) (start : Xi → TS) (xi : W → Xi) (w : W) (sn : Seen) (front : List Fmt.Drawn)
    (t : Fmt.Ext) (ca : CsAll (closeCarries J.pub)) {cols : List OpenedColumn} {y : TS × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start (xi w)) sn.rounds cols = .ok y)
    {B : BaseData} (H : CloseBase J.pub.par (K9.recOf y.1) B) (hh : J.pub.par.h = B.Gq.h)
    (R : GroupData) (hr : J.rows w front ca = .ok R) (hfit : rowsFit y.1.st B.G R = true) :
    ∃ row', Own.batch (B.S1 (K9.recOf y.1)) (K9.recOf y.1).frame.group
        ⟨Own.layoutOf (K9.recOf y.1).st B.G, OnBytes.Slice.runRows (K9.recOf y.1).st B.G⟩ (E.ofTriple t) =
          some row' ∧
      askZero { J with stAt := fun w' s f => stAtZero cF.blocksInOrder start (xi w') Q s f } w sn front
          ⟨[t], [], [], none⟩ ca = some
        { k := J.pub.par.k, h := J.pub.par.h
          c := row'.c.writeOut ((Own.layoutOf (K9.recOf y.1).st B.G).k + (Own.layoutOf (K9.recOf y.1).st B.G).logEll)
          d := row'.d
          m := closeMain (B.S1 (K9.recOf y.1)) (Own.layoutOf (K9.recOf y.1).st B.G) fun o =>
            wordAt (B.S1 (K9.recOf y.1)) R.base.ell (rowsAt B.G R (·.main)) o .main
          mu := closeMask (B.S1 (K9.recOf y.1)) (Own.layoutOf (K9.recOf y.1).st B.G) fun o =>
            wordAt (B.S1 (K9.recOf y.1)) R.zk.ell (rowsAt B.G R (·.mask)) o .mask
          keptV := closeKept (B.S1 (K9.recOf y.1)) row'.kept fun o =>
            wordAt (B.S1 (K9.recOf y.1)) R.base.ell (rowsAt B.G R (·.main)) o .main
          w := fun _ => zeroE } := by
  have e := closeAsk_at_head h hl T J start xi w sn front ⟨[t], [], [], none⟩ (fun _ => zeroE) ca hf
  obtain ⟨row', hrow, e2⟩ := ask_of_base { J with stAt := fun _ _ _ => .ok (y.1.st, y.1.live.frame.group) } H hh w
    sn front t rfl (fun _ => zeroE) ca R hr hfit
  refine ⟨row', hrow, ?_⟩
  unfold askZero
  rw [e, e2]
  rfl

/-! ## 2 At any thread, in the forms of Xch/Shown.lean -/

/-- **From the prover's side of the closing's step**, where `askZero` has `ask_of_base`'s value at every challenge of
"BAT"'s form (hA): the rounds as played show the sum and the honest round polynomials at the tables of the rows R, at
coefficients Wc that the run which the part's coins spend gives. -/
theorem shown_of_moved {V W X Pb S' Cl : Type} {Bk : ProverCoinCounts} (T : Thread Bk S' Cl V W X Pb) (J : CloseJob W)
    (blk : Block S' Cl) (hr : blk.rounds = (closeRounds J.pub.par).map (·.1))
    (ho : blk.oracles = (closeRounds J.pub.par).map (·.2))
    (hp : ∃ g, (T.hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)])
    (k : Coins Bk) (m : Mid W X) (En : Env) (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn)
    (hf : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m En ds y cols)
    (c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins)
    (hcc : closeCoins (V := V) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place J = .ok c)
    {s : Rec} {D : BaseData} (H : CloseBase J.pub.par s D)
    (hlen : 2 ^ (Own.layoutOf s.st D.G).logEll = ((D.S1 s).codes.base.getD s.frame.shape.code default).ell)
    (hh : J.pub.par.h = D.Gq.h) (R : GroupData) (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (hrs : roundsOf y.1 = rB :: rE :: rR) (hsh : ShapedAll (rB :: rE :: rR)) {row : OnBytes.GroupRow}
    (hrow : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, OnBytes.Slice.runRows s.st D.G⟩
      (drawnOf rB) = some row)
    (hA : ∀ t : Fmt.Ext, ∃ row', Own.batch (D.S1 s) s.frame.group
        ⟨Own.layoutOf s.st D.G, OnBytes.Slice.runRows s.st D.G⟩ (E.ofTriple t) = some row' ∧
      askZero J m.st.input m.shown m.st.heard ⟨[t], [], [], none⟩ (handSnd c).2.2 = some
        { k := J.pub.par.k, h := J.pub.par.h
          c := row'.c.writeOut ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll)
          d := row'.d
          m := closeMain (D.S1 s) (Own.layoutOf s.st D.G) fun o =>
            wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main
          mu := closeMask (D.S1 s) (Own.layoutOf s.st D.G) fun o =>
            wordAt (D.S1 s) R.zk.ell (rowsAt D.G R (·.mask)) o .mask
          keptV := closeKept (D.S1 s) row'.kept fun o =>
            wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main
          w := fun _ => zeroE }) :
    ∃ Wc, CoefOf (spentRun J (handSnd c)) Wc ∧
      ShownAt D s row rE rR (OnBytes.Means.tablesOf (D.S1 s) (Own.layoutOf s.st D.G) (rowWords D s R)) Wc := by
  have hf' : drawsFit ((closeRounds J.pub.par).map (·.1)) ds = true := by
    rw [← hr]
    exact hf
  obtain ⟨e, d1, gs, hds, -, -⟩ := close_draws_form J.pub.par ds hf'
  have hdr := moved_drawn T hM
  rw [hrs, hds] at hdr
  have hdr' : rB.drawn :: (rE :: rR).map (·.drawn) = ⟨[e], [], [], none⟩ :: d1 :: gs := hdr
  have eB : rB.drawn = ⟨[e], [], [], none⟩ := (List.cons.inj hdr').1
  have ex : drawnOf rB = E.ofTriple e :=
    (congrArg (fun d : Fmt.Drawn => E.ofTriple (d.elems.headD (0, 0, 0))) eB :)
  obtain ⟨row', hrow', hAz⟩ := hA e
  have hrow2 : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, OnBytes.Slice.runRows s.st D.G⟩
      (E.ofTriple e) = some row := by
    rw [← ex]
    exact hrow
  have er : row' = row := Option.some.inj (hrow'.symm.trans hrow2)
  subst er
  rw [← eB] at hAz
  have key := shows_at_moved T J blk hr ho hp k m En ds y cols hf hM c hcc H hlen hh
    (fun o => wordAt (D.S1 s) R.base.ell (rowsAt D.G R (·.main)) o .main)
    (fun o => wordAt (D.S1 s) R.zk.ell (rowsAt D.G R (·.mask)) o .mask) _ rB rE rR hrs hsh hAz hrow rfl rfl rfl rfl
    rfl (rowWords D s R) rfl
  refine ⟨_, ?_, key.1, _, key.2⟩
  exact coefOf_cast _ _

/-! ## 3 At the head's thread -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: this file's head, "The notation, and the
-- option in front of it".
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- At the head's thread the number of challenges heard before the chain is 0. -/
theorem thread_ahead : (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front = 0 := rfl

/-- **Wherever the invariant holds at a border b of the head's thread, the description's fold over the chain's first b
members**, from the chain's own first state, at all rounds seen and at some columns, returns the verifier's state. -/
theorem fold_at_thr (b : Nat) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 b k s m En) :
    ∃ cols, foldBlocks 0 (cF.blocksInOrder.take b) (ProofFile.startS Zp m.st.input.x.pub) m.seen cols = .ok (s, [], []) := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, -, -, hMd, -, -⟩ := hT'
  unfold Thread.Made at hMd
  obtain ⟨-, -, -, -, s₀, cols, hb, -, hfold⟩ := hMd
  have hb' : s₀ = ProofFile.startS Zp m.st.input.x.pub := hb
  have hfd : foldBlocks 0 (cF.blocksInOrder.take b) (ProofFile.startS Zp m.st.input.x.pub) (m.seen.drop (𝕋).front) cols =
      .ok (s, [], []) := by
    rw [← hb']
    exact hfold
  rw [thread_ahead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w, List.drop_zero] at hfd
  exact ⟨cols, hfd⟩

variable (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
  (Gr : ProofFile.Ground) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **At a stand of the head's thread with an accepted step of the closing's block, the rounds as played show the sum
and the honest round polynomials**, at the tables of the prover's own rows R and at coefficients that the run which the
part's coins spend gives. -/
theorem shows_at_head (l : Nat) (hl : l < 25) (hF : ClosingsFirst H.first readers rows stAt Zp Gr)
    (hfill : stAt = fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub)
    {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l p Qc blk)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn} {s' : TS}
    (St : StepAt 𝕋 Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s')
    {D : BaseData} (Hb : CloseBase Qc (K9.recOf s) D) (hh : Qc.h = D.Gq.h)
    (hlen : 2 ^ (Own.layoutOf (K9.recOf s).st D.G).logEll =
      ((D.S1 (K9.recOf s)).codes.base.getD (K9.recOf s).frame.shape.code default).ell)
    {cc : (closePart (V := Local W₀ Rc ProofFile.Inst Tr) (X := X)
      (foldShellT true (lotJob readers rows stAt Zp Gr Qc) foldWords)).Coins}
    (hcc : closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋).chain) (k.look (𝕋).chain) blk.place
      (lotJob readers rows stAt Zp Gr Qc) = .ok cc)
    {R : GroupData} (hR : (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R)
    (hfit : rowsFit s.st D.G R = true) {rB rE : Fmt.RoundView} {rR : List Fmt.RoundView} {row : OnBytes.GroupRow}
    (hrs : roundsOf y.1 = rB :: rE :: rR)
    (hrow : Own.batch (D.S1 (K9.recOf s)) (K9.recOf s).frame.group
      ⟨Own.layoutOf (K9.recOf s).st D.G, OnBytes.Slice.runRows (K9.recOf s).st D.G⟩ (drawnOf rB) = some row) :
    ∃ Wc, CoefOf (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) Wc ∧
      ShownAt D (K9.recOf s) row rE rR
        (OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G)
          (rowWords D (K9.recOf s) R)) Wc := by
  subst hfill
  have Hc := closeAt_of_tied h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td (b := 14 * l + IM.nAt l + 5) rfl readers
    rows _ Gr hF
  obtain ⟨-, -, -, -, -, -, hr, ho⟩ := Hc.tied
  obtain ⟨-, hsh, -, -, -⟩ := tied_decides Td St.step.2
  rw [hrs] at hsh
  obtain ⟨cols₀, hfd⟩ :=
    fold_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (14 * l + IM.nAt l + 5) St.thr.1
  exact shown_of_moved (T := 𝕋)
    (lotJob readers rows (fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub) Zp Gr Qc) blk hr ho Hc.halfAt k m
    En ds y cols St.fit St.step.1 cc hcc Hb hlen hh R rB rE rR hrs hsh hrow fun t =>
      askZero_of_base_at_head h.toAtMg hl Td
        (lotJob readers rows (fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub) Zp Gr Qc) (ProofFile.startS Zp)
        (fun u : Local W₀ Rc ProofFile.Inst Tr => u.x.pub) m.st.input m.shown m.st.heard t (handSnd cc).2.2 hfd Hb hh R hR
        hfit

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.askZero_of_base_at_head
#print axioms ProofFile.Honest.K10.shown_of_moved
#print axioms ProofFile.Honest.K10.thread_ahead
#print axioms ProofFile.Honest.K10.fold_at_thr
#print axioms ProofFile.Honest.K10.shows_at_head
