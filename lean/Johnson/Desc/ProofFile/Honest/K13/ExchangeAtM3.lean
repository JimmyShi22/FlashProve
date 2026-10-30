-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ExchangeAtM3.lean: kind K13, the members' batching: THE KIND's
SHARE OF THE EXCHANGE AT ITS PLACE (`Exchange`, Honest/Thread/Pays.lean; a share: `ExchangeOf`,
ExchangeOf.lean of this folder), at the first chain's thread (`Letters.thread`,
Honest/Thread/First.lean): A CONDITIONAL STATEMENT: behind the member's accepted step THE ITEM
"pileOne" HOLDS OF THE THREAD's WITNESS, AT EVERY CONTINUATION OF THE CHALLENGES HEARD. Definitions
of the premises, each a proposition of its own, and statements with their proofs. The words thread,
border, item, forward row, witness and fall are explained in the head of Honest/Thread/Thr.lean.

WHAT `k13_pileOne` STANDS UNDER, general in the thread's parameters L and in a reader rd:
  hp: the written list of places has the kind's place at number b. ho: the item "pile" is open
    there.
  `AtK13` (AtThread.lean of this folder): the member number b has the kind's rounds, states no
    oracle message, and the kind's half stands at its place.
  `MemberIs` (ShapeAtM3.lean of this folder): the member returns where the kind's own sub-protocol
    does, from a state without a mark of failure; and the kind's own returns wherever the member
    does. THE NINE GUARDS ON THE VERIFIER's STATE ARE NO PREMISE: `Exchange` is asked behind the
    member's accepted step, and the guards are what the kind's sub-protocol tests (`k13_from_step`,
    FromStep.lean).
  `K13Reads`: the parameters' meaning of "pile" and of "pileOne" is "all rows on the table are true"
    at rd, which reads the same in front of the member's step and behind it.
  `MatTie`: at every input that the thread's parameter `valid` admits, the matrix that rd makes of
    the thread's witness is the one that the half's reader of the index gives. It needs an equation
    between three parameters: the thread's cells of the input, the reader's matrix off cells, the
    half's `weights`. No state, no coin.
  `CoinsTie`: rd's mask entries under the slots that the verifier takes are the coins of the stretch
    that the book of coins lends the sumcheck's part. It names coins AND IS MEANT AT EVERY COIN:
    both sides are functions of one run's coins. It needs: which slots are taken; that these lie
    inside the index masks' message's mask table, on real rows (the library's reader gives 0
    elsewhere); what the thread's witness holds under them; which stretch the book of coins lends.
  `RowsTie`: WHERE THE REPLY THAT THE STATE HOLDS IS THE ONE ASKED (`ReplyIs`, FromThread.lean): the
    pile that the half's parameter makes, of the instance and the challenges heard, agrees with the
    state's in the rows' weights and column points. It needs: that these hang on the instance, the
    challenges and the reply alone, over every sub-protocol in front that lays a row. THE LAST ROW's
    WEIGHTS READ THE REPLY AS HEARD, a value that the prover sends in the clear: without the
    condition on the reply the tie would fix that sent value. THE CONDITION GAINS NO STRENGTH:
    `RowsTie` under it, with `ReplyRides`, gives `RowsTie` without it. What is won: the tie can be
    shown with no word on what was sent, and the one sentence on a sent value stands alone under its
    name.
  `ReplyRides` (FromThread.lean): at the border the thread gives `ReplyIs`. No clause of the thread
    that has a text says so; it follows where it stands among the clauses of the parameter `rides`,
    from the border behind kind K7's place on, and is carried over every member up to this one. At
    the proof file's IOP each member of another kind than K7 that is laid alone carries it: its own
    guard on the reply rejects a state behind with another reply (`IM.step_alone` with
    `IM.sameReply_eq`, Johnson/IMR/SeatForm.lean). Of a general list L.bs nothing of the sort is
    said.
WHAT `k13_pileOne_at` STANDS UNDER, at the library's own parameters, b = 355:
  h : `P5J.AtMgA`, the hypothesis under which these parameters are laid. hH: the kind's half stands
  at the member's place among the thread's halves. `MatTie`, `CoinsTie`, `RowsTie`, `ReplyRides`.
  SHOWN THERE: hp, ho (evaluations by Lean's kernel, which read no h); from h: `K13Reads`,
  `MemberIs`, the first two fields of `AtK13`, and that the full size's written number of rows is
  the plan's (`k13_rows_full`, FromThreadAt.lean: the library types its reader at the one, the half
  at the other).
Main names:
  `k13_pileOne_stand`: the share's core, at one stand at which `ReplyIs` holds.
  `k13_pileOne`: **the share**, general: from `ReplyRides`.
  `k13_exchange_iff`, `k13_exchange_of`: `Exchange` at the kind's place is the shares at "pileOne",
    "pinW" and "pinI" together.
  `castWit`, `holds_cast`, `k13ReaderAt`, `k13_reads_at`: the library's reader at the plan's number
    of rows.
  `k13_atK13_at`: a premise, shown at the library's own parameters (`k13_memberIs_at`, another, lies
    in FromThreadAt.lean).
  `k13_pileOne_at`: **the share at the library's own parameters.**
  `k13_exchange_at`: there `Exchange` follows from that share's premises and the share at "pinI".
    "pinW" costs nothing there: it holds by unfolding of these parameters, at every border
    (`k13_pinW_at`, FromThreadAt.lean): no work of the kind's.

What is not claimed. The item "pinI": at the honest parameters it is the field `ans` of `Letters`, a
parameter without text: its share is a premise of `k13_exchange_at`. At general parameters "pinW" is
any sentence. `ReplyRides`, `RowsTie`, `CoinsTie`, `MatTie` at any thread. No instance of the
premises together is typed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.AtThread
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt
import Johnson.Desc.ProofFile.Honest.K13.FromStep
import Johnson.Desc.ProofFile.Honest.K13.ExchangeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Chain Strs OpenedColumn)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where atM3 St)
open VerifiableInference.Desc.K13.Law (Wit ρg Holds RowsTrue rwBook dOf)
open VerifiableInference.Desc.K13.Honest (withClaim maskAt rowReads)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl Cl' W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M) (b : Nat) (weights : W₀ → Weights)
  (pile : PileOf Xi) (P : Where)
  (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE P.lin.matrixRows P.lin.kCol)
  (asked : Xi → E)

/-- The parameters' meaning of the two items, at a reader that the member's step leaves as it is. -/
structure K13Reads : Prop where
  /-- "pile" gives: all rows on the table are true at the reader -/
  front : ∀ w x y v, (L.Mg w).pile x y v → RowsTrue (rd x) x.2 v
  /-- that sentence gives "pileOne" -/
  behind : ∀ w x y v, RowsTrue (rd x) x.2 v → (L.Mg w).pileOne x y v
  /-- the reader reads the same at the state behind the member's step -/
  same : ∀ (p : Pp) (s : S) (t : List Nat × St) (msg : Array OracleNotice) (row : TensorRow) v,
    takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t →
    rd (p, withClaim s t.2.st msg row) v = rd (p, s) v

/-- At every input that `valid` admits, the reader's matrix off the thread's witness is the half's.
-/
def MatTie : Prop :=
  ∀ (k : Coins Bk) (s : S) (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn), L.valid w →
    (rd (L.pubOf w.x, s) (L.Q.wit k w h)).mat =
      (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile w)).mat

/-- The reader's mask entries under the taken slots are the coins that the book of coins lends. -/
def CoinsTie : Prop :=
  ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m En, Thr L.thread b k s m En →
    ∀ c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts,
      lendRow Bk (Bk.rowsOf L.thread.chain) (k.look L.thread.chain) blk.place
        (proverSideOfClaimCombination weights pile P).parts 0 = .ok c →
      ∀ t, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t →
        ∀ (h : List Fmt.Drawn) j, j < 2 * P.lin.kCol + 1 →
          ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE) =
            maskAt (rd (L.pubOf m.st.input.x, s) (L.Q.wit k m.st.input (m.st.heard ++ h)))
              (t.1.map fun i => ⟨s.out.indexMasks, i⟩) j

/-- Where the reply that the state holds is the one asked, the half's pile agrees with the state's
in what the parts read of a row. -/
def RowsTie : Prop :=
  ∀ k s m En, Thr L.thread b k s m En → ReplyIs asked m.st.input.x s → ∀ d,
    (pile m.st.input.x (m.st.heard ++ [d])).map rowReads = s.out.pending.map rowReads

variable {L b weights pile P rd asked}

/-- **The share's core, at one stand**: under the premises that the head lists but `ReplyRides`: at
a stand at which the thread holds in front AND THE REPLY THAT THE STATE HOLDS IS THE ONE ASKED:
behind the member's accepted step the item "pileOne" holds, of the thread's witness, at every
continuation. -/
theorem k13_pileOne_stand (hp : L.ps[b]? = some ⟨1, none, 3, .K13⟩)
    (ho : Item.pile ∈ L.thread.opened b) (h : AtK13 L.thread b weights pile P)
    (hI : MemberIs L.thread.bs b P Cl') (hR : K13Reads L P rd) (hM : MatTie L weights pile P rd)
    (hC : CoinsTie L b weights pile P rd) (hW : RowsTie L b pile asked) {blk : Block S Cl}
    (hb : L.thread.bs[b]? = some blk) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hT : Thr L.thread b k s m En) (hY : ReplyIs asked m.st.input.x s)
    (hd : drawsFit blk.rounds ds = true) (hS : L.thread.Stepped blk k s m En ds y cols s') :
    L.thread.Items [Item.pileOne] k s' y.2 (En.add y.1) := by
  intro ds' i hi
  obtain rfl : i = Item.pileOne := List.mem_singleton.1 hi
  obtain ⟨h0, -, -⟩ := k13_form_front L hp hT.2.2.1
  have hGs : K13Guards P s := (k13_from_step hI hb hS).1
  obtain ⟨f, hfin⟩ := hGs.fin
  -- where the prover's run stands behind
  obtain ⟨l, hl, hy⟩ := hS.1.1
  obtain ⟨p, hpl, -, -⟩ := k13_moved weights pile P blk (h.rounds blk hb) (h.oracles blk hb)
    (h.half blk hb) hl m ds hd
  obtain rfl : y = (p, _) := Except.ok.inj (hy.symm.trans hpl)
  -- the witness, at the continuation
  have hrows := k13_rows_front L rd hR.front ho hfin hT.2.2.2.1 (ds ++ ds')
  obtain ⟨t, msg, row, ht, -, rfl, hrow⟩ := k13_thread_stepped (Cl' := Cl') h hb
    (fun rs gs t' q => hI.forth blk hb s rs gs t' h0 q) hd hGs
    (rd (L.pubOf m.st.input.x, s) (L.Q.wit k m.st.input (m.st.heard ++ (ds ++ ds'))))
    (fun c hc => ⟨hW k s m En hT hY, hM k s m.st.input _ hT.2.2.2.2.2.2, hrows,
      fun t ht j hj => hC blk hb k s m En hT c hc t ht (ds ++ ds') j hj⟩) hS
  refine hR.behind _ _ _ _ ?_
  show RowsTrue (rd (L.pubOf m.st.input.x, withClaim s t.2.st msg row)) (withClaim s t.2.st msg row)
    (L.Q.wit k m.st.input (m.st.heard ++ ds ++ ds'))
  rw [List.append_assoc]
  exact k13_rows_behind rd _ s t.2.st msg row _ (hR.same _ s t msg row _ ht) hrow

/-- **THE SHARE**: under the premises that the head lists: from the thread in front and the member's
accepted step, the item "pileOne" holds behind, of the thread's witness, at every continuation. -/
theorem k13_pileOne (hp : L.ps[b]? = some ⟨1, none, 3, .K13⟩) (ho : Item.pile ∈ L.thread.opened b)
    (h : AtK13 L.thread b weights pile P) (hI : MemberIs L.thread.bs b P Cl')
    (hR : K13Reads L P rd) (hM : MatTie L weights pile P rd)
    (hC : CoinsTie L b weights pile P rd) (hW : RowsTie L b pile asked)
    (hY : ReplyRides L b asked) : ExchangeOf L.thread b [Item.pileOne] :=
  fun _ hb k s m En _ _ _ _ hT hd hS =>
    k13_pileOne_stand hp ho h hI hR hM hC hW hb hT (hY k s m En hT) hd hS

/-- `Exchange` at the kind's place is the share at the three items that the forward row owes. -/
theorem k13_exchange_iff (hp : L.ps[b]? = some ⟨1, none, 3, .K13⟩) :
    Exchange L.thread b ↔ ExchangeOf L.thread b [Item.pileOne, Item.pinW, Item.pinI] := by
  rw [exchangeOf_all, k13_owes L hp]
  exact Iff.rfl

/-- So it follows from the three shares. -/
theorem k13_exchange_of (hp : L.ps[b]? = some ⟨1, none, 3, .K13⟩)
    (h1 : ExchangeOf L.thread b [Item.pileOne]) (h2 : ExchangeOf L.thread b [Item.pinW])
    (h3 : ExchangeOf L.thread b [Item.pinI]) : Exchange L.thread b :=
  (k13_exchange_iff hp).2 ((exchangeOf_append L.thread b [Item.pileOne] [Item.pinW, Item.pinI]).2
    ⟨h1, (exchangeOf_append L.thread b [Item.pinW] [Item.pinI]).2 ⟨h2, h3⟩⟩)

/-! ## At the library's own parameters -/

/-- A matrix with mask entries, at an equal number of rows. -/
def castWit {K : Type} {n n' k : Nat} (e : n = n') (W : Wit K n k) : Wit K n' k := e ▸ W

/-- A row is true of the one exactly if it is true of the other. -/
theorem holds_cast {n n' k : Nat} (e : n = n') (W : Wit GE n k) (r : TensorRow) :
    Holds ρg (castWit e W) r ↔ Holds ρg W r := by
  subst e
  rfl

section
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₁ Rc' Tr' X' : Type}
  (hs : List (Placed (Local W₁ Rc' ProofFile.Inst Tr') (Local W₁ Rc' ProofFile.Inst Tr') X'))
  (Q : Script Bk (Local W₁ Rc' ProofFile.Inst Tr') (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₁ Rc' ProofFile.Inst Tr' → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₁ Rc' ProofFile.Inst Tr' → Prop) (rides : Nat → Local W₁ Rc' ProofFile.Inst Tr' → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **The library's reader through the book of commitment trees, at the plan's number of rows.** -/
noncomputable def k13ReaderAt :
    ProofFile.InstPub × TS → WtF → Wit GE h.𝔇.P13.lin.matrixRows h.𝔇.P13.lin.kCol :=
  fun a v => castWit (k13_rows_full h) (rwBook h.𝔇.arr h.𝔇.mat13 a v)

/-- At the library's own parameters `K13Reads` holds, at that reader. -/
theorem k13_reads_at :
    K13Reads (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) h.𝔇.P13
      (k13ReaderAt h) where
  front := fun w a y v hp r' hr =>
    (holds_cast (k13_rows_full h) _ r').2
      ((m3_pile_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w a y v).1 hp r' hr)
  behind := fun w a y v hp =>
    (m3_pileOne_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w a y v).2
      fun r' hr => (holds_cast (k13_rows_full h) _ r').1 (hp r' hr)
  same := fun p _ _ msg row v ht =>
    congrArg (castWit (k13_rows_full h)) (k13_rwBook_behind h.𝔇.arr h.𝔇.mat13 p ht msg row v)

/-- At the library's own parameters `AtK13` holds, where the kind's half stands at the member's
place among the thread's halves. -/
theorem k13_atK13_at {weights : W₁ → Weights} {pile : PileOf ProofFile.Inst}
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (hs.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13)) :
    AtK13 (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 weights
      pile h.𝔇.P13 where
  rounds := fun _ hb => (m3_member_fields h hb).1
  oracles := fun _ hb => (m3_member_fields h hb).2
  half := hH

set_option maxRecDepth 100000 in
/-- **THE SHARE AT "pileOne"**, at the library's own parameters, at the border number 355, under the
premises that the head lists. -/
theorem k13_pileOne_at {weights : W₁ → Weights} {pile : PileOf ProofFile.Inst}
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (hs.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hM : MatTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) weights
      pile h.𝔇.P13 (k13ReaderAt h))
    (hC : CoinsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      weights pile h.𝔇.P13 (k13ReaderAt h))
    (hW : RowsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      pile ProofFile.Inst.asked)
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      ProofFile.Inst.asked) :
    ExchangeOf (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355
      [Item.pileOne] :=
  k13_pileOne (Cl' := Unit) m3_place m3_pile_open
    (k13_atK13_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hH)
    (k13_memberIs_at h) (k13_reads_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
    hM hC hW hY

set_option maxRecDepth 100000 in
/-- **`Exchange` at the border number 355**, at the library's own parameters: from the premises of
`k13_pileOne_at` and the share at "pinI". -/
theorem k13_exchange_at {weights : W₁ → Weights} {pile : PileOf ProofFile.Inst}
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (hs.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hM : MatTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) weights
      pile h.𝔇.P13 (k13ReaderAt h))
    (hC : CoinsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      weights pile h.𝔇.P13 (k13ReaderAt h))
    (hW : RowsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      pile ProofFile.Inst.asked)
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      ProofFile.Inst.asked)
    (hI : ExchangeOf
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355
      [Item.pinI]) :
    Exchange
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 :=
  k13_exchange_of m3_place
    (k13_pileOne_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hH hM hC hW hY)
    (k13_pinW_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps 355) hI

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_pileOne_stand
#print axioms ProofFile.Honest.K13.k13_pileOne
#print axioms ProofFile.Honest.K13.k13_exchange_iff
#print axioms ProofFile.Honest.K13.k13_exchange_of
#print axioms ProofFile.Honest.K13.holds_cast
#print axioms ProofFile.Honest.K13.k13_reads_at
#print axioms ProofFile.Honest.K13.k13_atK13_at
#print axioms ProofFile.Honest.K13.k13_pileOne_at
#print axioms ProofFile.Honest.K13.k13_exchange_at
