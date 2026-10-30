-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/HWAtDoor.lean: kind K13 (the members' batching): **the witness holds W's text**:
wherever the first chain's thread holds at its last border, what the last chain's start reads as W
is the vector `wVec` (Johnson/Desc/ProofFile/Honest/K13/WData.lean) at the index's reader and at the
row weights `wG` that the filling `pileAnyK3` makes of the challenges heard on the first chain. The
full size, and the hash function `OnBytes.secondHashFunction`, alone. Statements with their proofs; no
definition.

What it is for. The row (Dot) at the last chain's start is made from two sentences: the witness
holds W's text, and the witness holds Omega's text. This is the first.

Main names.
  `k13_wText_at_end`: of the first chain's Script's witness, read through the last state's own book
    at the number `w₁Of`, at the thread as `lettersHead` makes it, every argument a variable.
  `k13_hW_at_door`: **of the last chain's witness (`lastWitness`) and W's reader `wvW`**, at the
    first thread as it is written (`firstThread`), at every continuation of the challenges.
  `k13_hW_at_own`: the same at the thread's own input w, with the instance and the index's reader
    named, from two equations at w (hx, hwt).

The premise R: kind K1's record `K1Seated` (Johnson/Desc/ProofFile/Honest/K1/Seated.lean) at number
356, at W's job with the data `wDataAt pileAnyK3 Zp G`. IT IS NOT SHOWN HERE. G, the ground, and
wit, the job's reader of the input, are variables: whoever spends the statements lays G as the
base's ground, shows R at the thread's Script, and shows that wit hands on the instance and the
index's weights.

How. Kind K1's law at a later border (`K1.word_is_data_at_358`, with `K1.stand_at_358`: W's number
there is 197; Johnson/Desc/ProofFile/Honest/K1/Law/WordIsDataAt.lean): each main entry of W's
message is the job's datum at the challenges heard in front of number 356. The datum at the vector's
places is `wVec`'s entry (`k13_wText_of_word`, WTextAtEnd.lean of this folder). The crossing to the
last chain's witness: `k13_wvW_at_lastWitness` (WTextAtDoor.lean).

Limits. Conditional on h (or the head at the return), on R and on the thread's invariant at border
358; that it holds there at any run is not shown here. Nothing is said of the matrix of the Script's
cells, nor that the row weights are those on the verifier's table. W IS LINEAR IN THE WEIGHTS AND
HOLDS VALUES OF THE INDEX's OWN ENTRIES: these statements speak of one run's values and are not to
be used as premises of a statement on the distribution of what a verifier sees.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.K13.WTextAtDoor
import Johnson.Desc.ProofFile.Honest.K1.Law.WordIsDataAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Sound (MsgT Mem wordsFirst)
open VerifiableInference.Desc.Third.Law (wvW w₁Of)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead HeadAtReturn FirstThreadParts IndexReaders
  firstLetters firstThread lastWitness)
open ProofFile.Honest.K1 (K1Seated PlaceIn)

/-- R is a premise that is not shown here. **Wherever the first chain's thread holds at its last
border, the Script's witness holds W's text**, at every continuation of the challenges. -/
theorem k13_wText_at_end {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr) {G : ProofFile.Ground} {first : ℕ} {blk₆ : Block TS ProofFile.Cl}
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} {own₀ : X'} {seats₀ : List (ℕ × ℕ)}
    {ms : List Mem} {rad : ℕ → ℕ}
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 356 blk₆ wit
      (K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull first (wDataAt pileAnyK3 Zp G)) own₀ .w
      (P5J.At.arr Zp) seats₀ ms rad)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k s m En)
    (ds' : List Fmt.Drawn) :
    ∀ e < 2 ^ Zp.first.lin.kCol,
      wordsFirst (P5J.At.arr Zp) s.st s.book (Q.wit k m.st.input (m.st.heard ++ ds')) (w₁Of s)
          .main ((linLayW Zp.first.codes Zp.first.lin).index e) =
        wVec Zp.first.lin (wit m.st.input).R.weights
          (wG Zp.first.lin (wHeard Zp) (pileAnyK3 Zp G) (wit m.st.input).x
            (m.st.heard.take (wHeard Zp))) e := by
  have hA : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
      (fun _ _ _ => True) 358 k s m En := ⟨hT, trivial⟩
  obtain ⟨-, hw⟩ :=
    K1.stand_at_358 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ (fun _ _ _ => True) hA
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hmsg := K1.msg_w_head h O
  have hsh : Johnson.Prover.Send.shapeAt
      (K1.wJobAt (X := X') Zp.first (K1.wGp Zp) 4 wMsgFull first (wDataAt pileAnyK3 Zp G)).P 0 =
      Zp.first.lin.w := K1.w_shape_zero Zp.first (K1.wGp Zp) 4 wMsgFull hmsg
  have hn : 0 < (VerifiableInference.Desc.K1.parW Zp.first (K1.wGp Zp) 4 wMsgFull).sent.size := by
    rw [K1.parW_sent]
    have q := K1.w_first Zp.first.lin wMsgFull hmsg
    by_contra h0
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h0)] at q
    cases q
  have eN : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.front +
      roundsTo cF.blocksInOrder 356 = wHeard Zp := by
    rw [k13_wHeard_is_rounds h]
    exact Nat.zero_add _
  have key := k13_wText_of_word h G first own₀ (wit m.st.input)
    (m.st.heard.take ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.front +
      roundsTo cF.blocksInOrder 356))
    (wordsFirst (P5J.At.arr Zp) s.st s.book (Q.wit k m.st.input (m.st.heard ++ ds'))) 197
    fun r j hr hj => by
      have W := K1.word_is_data_at_358 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ R
        (K1.wJobAt_plan Zp first (wDataAt pileAnyK3 Zp G)) (fun _ _ _ => True) hA 0 hn ds' r j hr hj
        (by rw [hsh]; exact (k13_wShape_at_head h).2)
        (by rw [hsh, k13_noPad_at_head h]; exact List.not_mem_nil)
        (by rw [hsh, (k13_wShape_at_head h).1]; rfl)
      rw [Nat.add_zero] at W
      exact W
  rw [eN, List.take_take, Nat.min_self] at key
  rw [hw]
  exact key

/-- R is a premise that is not shown here. **The last chain's witness holds W's text**, as W's
reader at the last chain's start reads it: wherever the first thread as it is written holds at its
last border, at every continuation of the challenges. -/
theorem k13_hW_at_door {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hd : HeadAtReturn files A) (first₁ : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (w : Local W₀ Rc ProofFile.Inst Tr) {G : ProofFile.Ground} {first : ℕ} {blk₆ : Block TS ProofFile.Cl}
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} {own₀ : X'} {seats₀ : List (ℕ × ℕ)}
    {ms : List Mem} {rad : ℕ → ℕ}
    (R : K1Seated (firstLetters hd first₁ w) 356 blk₆ wit
      (K1.wJobAt A.Z.first (K1.wGp A.Z) 4 wMsgFull first (wDataAt pileAnyK3 A.Z G)) own₀ .w
      (P5J.At.arr A.Z) seats₀ ms rad)
    {k : Coins A.B} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (firstThread hd first₁ w) 358 k s m En) (z : ProofFile.InstPub) (ds : List Fmt.Drawn) :
    ∀ c < 2 ^ A.Z.first.lin.kCol,
      wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) (z, s)
          (lastWitness hd first₁ reads k m.st.input (m.st.heard ++ ds)) c =
        wVec A.Z.first.lin (wit m.st.input).R.weights
          (wG A.Z.first.lin (wHeard A.Z) (pileAnyK3 A.Z G) (wit m.st.input).x
            (m.st.heard.take (wHeard A.Z))) c :=
  fun c hc => (k13_wvW_at_lastWitness hd first₁ reads w hT z _ c).trans
    (k13_wText_at_end hd.head A.H first₁.script _ _ _ _ _ _ _ _ _ w R hT ds c hc)

/-- R, hx and hwt are premises. **The same at the thread's own input w**, with the index's reader
named: hx: the job's reader of the input hands on the instance; hwt: its weights are the reader's of
the index, `reads.weights`. Both at w alone. -/
theorem k13_hW_at_own {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hd : HeadAtReturn files A) (first₁ : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (w : Local W₀ Rc ProofFile.Inst Tr) {G : ProofFile.Ground} {first : ℕ} {blk₆ : Block TS ProofFile.Cl}
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} {own₀ : X'} {seats₀ : List (ℕ × ℕ)}
    {ms : List Mem} {rad : ℕ → ℕ}
    (R : K1Seated (firstLetters hd first₁ w) 356 blk₆ wit
      (K1.wJobAt A.Z.first (K1.wGp A.Z) 4 wMsgFull first (wDataAt pileAnyK3 A.Z G)) own₀ .w
      (P5J.At.arr A.Z) seats₀ ms rad)
    (hx : (wit w).x = w.x) (hwt : (wit w).R.weights = reads.weights w.w₀)
    {k : Coins A.B} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (firstThread hd first₁ w) 358 k s m En) (z : ProofFile.InstPub) (ds : List Fmt.Drawn) :
    ∀ c < 2 ^ A.Z.first.lin.kCol,
      wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) (z, s)
          (lastWitness hd first₁ reads k w (m.st.heard ++ ds)) c =
        wVec A.Z.first.lin (reads.weights w.w₀)
          (wG A.Z.first.lin (wHeard A.Z) (pileAnyK3 A.Z G) w.x (m.st.heard.take (wHeard A.Z)))
          c := by
  have hw : m.st.input = w := by
    have hT' := hT
    unfold Thr at hT'
    exact hT'.2.2.2.2.2.2.1
  have key := k13_hW_at_door hd first₁ reads w R hT z ds
  rw [hw, hx, hwt] at key
  exact key

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_wText_at_end
#print axioms AtFullSide.K13.k13_hW_at_door
#print axioms AtFullSide.K13.k13_hW_at_own
