-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/ExchangeAllItems.lean: CONDITIONAL.

What is here. COLUMN hX OF `owesS_head_form` (Honest/Thread/GatherHeadForm.lean) AT K4's MEMBER OF GROUP
g: `ExchangeAtS` at each of the eight items that the row owes, at the first chain's thread, from the
pair `ThrS`, behind an accepted step. General in the Script Q, the index's type, the randomness' type
and the reader of the index.

OF THE EIGHT ITEMS TWO HAVE CONTENT: "own" and `wo m`, each under the premises below. TWO ARE TRUE AND
EMPTY: "planes" and "join": no run is listed there. ONE IS `rfl`: `pinW`. THREE ARE CARRIED OUT OF
`ThrS`: `pin m 0`, `constr m .small`, `pinI`: they held in front, and `BehindS` and the keeps carry
them behind the step.

  `k4IndexIs_of_reader`    `K4IndexIs` from the three sentences on the index
  `k4_exchange_all_items`  **the column**

Dark. AN IMPLICATION FROM `ThrS` AT 28 g + 4 AND AN ACCEPTED STEP: NO STATE IS KNOWN TO MEET IT AT ANY OF
THE TWELVE BORDERS. What the proof at "own" draws out of `ThrS` and is not shown: the three worths
at link m, piece 2 ("keys", "planes", "rider"), what the public item `.left m` says beside its test,
and the item `constr m .idn` (whose payer's form is `items_constr_at_thread`, under `ScriptTies`, at
border 0). `ThrS` here wants all seven items of K3's row in front.
The premises on Q are premises: no file on the trunk shows them of any Script. Q is a letter: this law
says nothing of the honest prover's Script. Nothing on hiding follows from it. Nothing on soundness,
on completeness or on any other property. THE FULL SIZE ALONE, THE FORMAT's EARLIER HASH ALONE.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeOwnBy
import Johnson.Desc.ProofFile.Honest.K4.Law.WoTopsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeOwnInput
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskOfOwn
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexLotGIs
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellIsListAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsSmallOfIndex
import Johnson.Desc.ProofFile.Honest.K4.Law.W.BookAtHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LayAtHead
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Goal.HonestTrace.ConstrAtThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.HonestTrace (Sz entryOf ridesPastAt_constr)
open OnBytes.Maker (WholeD)
open OnBytes.Road.K4 (atK4_full)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open VerifiableInference.OnPublicFiles.Flat (Holds holds_matrixOf matrixOf)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K5 (LaysCells planesAtRef)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs exchangeAtS_pin exchangeAtS_pinI
  exchangeAt_pinW)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc X₀ X' : Type}

/-- CONDITIONAL: on hA, hV, hTrace, hReader and hScript. **`K4IndexIs` at a valid input**: its trace
is that of an index; the Script's cells are that index's matrix, and the reader reads that index. -/
theorem k4IndexIs_of_reader {Bk : ProverCoinCounts} {P : OnlineProverParts W₀ Rc Cells X₀ X'} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X'}
    {pol lay KL : ByteArray}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction pol lay KL P = .ok A)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {v : Local W₀ Rc ProofFile.Inst Cells}
    (hv : ReadyInput F A.H v) (toIndex : W₀ → Option Cm.Idx) (reader : W₀ → Weights)
    (hTrace : ∀ Zq w₀ ξ tr, P.trace Zq w₀ ξ = some tr →
      ∃ i, toIndex w₀ = some i ∧ fullIn.trace Zq i ξ = some tr)
    (hReader : ∀ w₀ i, toIndex w₀ = some i → reader w₀ = ⟨entryOf i⟩)
    (hScript : ∀ i, toIndex v.w₀ = some i → Q.cells v = matrixOf i) :
    K4IndexIs Q reader v := by
  have ht := hv.2.2
  rw [atPure_trace hA] at ht
  obtain ⟨i, hi, -⟩ := hTrace _ _ _ _ ht
  refine ⟨i, ?_, fun a b => ?_⟩
  · rw [hScript i hi]
    exact holds_matrixOf i
  · rw [hReader _ _ hi]
    show algebraMap Cb.Gl.F Cb.Gl.E (((i.mat a b : ℤ) : Cb.Gl.F)) = _
    rw [map_intCast]

/-- CONDITIONAL. **Column hX of `owesS_head_form` at K4's member of group g**: at each of the eight
items that the row owes, `ExchangeAtS`. Two of the eight have content, two are empty, one is `rfl`,
three are carried out of `ThrS`: the file's head. The full size alone, the format's second hash function
alone. Nothing on hiding. -/
theorem k4_exchange_all_items (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₀ Rc Cells X₀ X'} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Cells → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Cells)
    (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st R))
    (hV : ∀ v, Vd v → ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H v)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Cells) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hb₀ : b₀ ≠ k + 1)
    -- the reader of the index, and K4's lot at it
    (reader : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot id reader (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot id reader (fun _ _ => k4LookAt)).halves A.Z A.G)
    -- on the index
    (toIndex : W₀ → Option Cm.Idx)
    (hTrace : ∀ Zq w₀ ξ tr, P.trace Zq w₀ ξ = some tr →
      ∃ i, toIndex w₀ = some i ∧ fullIn.trace Zq i ξ = some tr)
    (hReader : ∀ w₀ i, toIndex w₀ = some i → reader w₀ = ⟨entryOf i⟩)
    -- on the Script, its fields and messages alone
    (hScript : ∀ v i, Vd v → toIndex v.w₀ = some i → Q.cells v = matrixOf i)
    {S : Sz} (hSz : planesAtRef S = Sz.ref) {N Nm Ni : ℕ}
    (rd : Local W₀ Rc ProofFile.Inst Cells → Readers) (hrd : ∀ v, (rd v).cells = v.trace)
    {seat seat' : MsgAddr → Option (ℕ × ℕ)} {heard heard' : MsgAddr → ℕ}
    (L : LaysCells h Q S Vd N rd seat heard (2 * g))
    (L' : g ≠ 0 → LaysCells h Q S Vd N rd seat' heard' (2 * (g - 1)))
    {Qp : K4Pub} (hPG : Lot.k4PubG Zp g = some Qp)
    (Om : OwnMsgsForm Q Vd Nm (maskNumAt Zp m) 0
      (k4MaskTxt X' id reader k4Tokens k4LookAt Qp (Forest.elems (P5J.At.X Zp).y.fo)))
    (Oi : OwnMsgs Q Vd Ni
      (Lot.k4IndexLotG (Bk := A.B) (Rc := Rc) X' id reader k4Tokens k4LookAt Zp g).n
      (Lot.k4IndexLotG (Bk := A.B) (Rc := Rc) X' id reader k4Tokens k4LookAt Zp g).fx
      (Lot.k4IndexLotG (Bk := A.B) (Rc := Rc) X' id reader k4Tokens k4LookAt Zp g).txt)
    (hN : N ≤ roundsTo cF.blocksInOrder k) (hNm : Nm ≤ roundsTo cF.blocksInOrder k) (hNi : Ni ≤ roundsTo cF.blocksInOrder k)
    -- from the other columns
    (hB : BehindS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k)
    (hKs : ∀ s s', (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.keeps k s s' →
      s'.st = s.st) :
    ∀ i ∈ ((lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.row k).owes,
      ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k i := by
  obtain rfl : Qp = k4PubAt cF k x :=
    Option.some.inj (hPG.symm.trans (k4PubG_of Lh (k4Pub_head h Lh)))
  have hg := Lh.lt
  have hlen : ∀ {n c s mm E}, n ≤ roundsTo cF.blocksInOrder k →
      Thr (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E →
      n ≤ mm.st.heard.length := by
    intro n c s mm E hn hT
    rw [Thread.heard_length _ hT.2.1]
    show n ≤ 0 + roundsTo cF.blocksInOrder k
    rw [Nat.zero_add]
    exact hn
  have hval : ∀ {c s mm E},
      Thr (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E →
      Vd mm.st.input := fun hT =>
    (show _ = w₁ ∧ Vd _ from hT.2.2.2.2.2.2).2
  have hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread id reader
        k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm :=
    fun _ _ _ _ hT => k4MaskTie_of_own h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh
      (k4Pub_head h Lh) Om hT.1 (hval hT.1) (hlen hNm hT.1)
  have hI : Vd w₁ → K4IndexIs Q reader w₁ := fun hv =>
    k4IndexIs_of_reader hA Q (hV _ hv) toIndex reader hTrace hReader
      fun i hi => hScript _ i hv hi
  have hBk := ProofFile.Honest.K14.atPure_book_at_head h hA
  have hLend : lendsRow A.B 0 (k4Place (k4PubAt cF k x)) (k4RowIn (k4PubAt cF k x)) = true :=
    k4Lends_at_head_of h hg hPG hBk
  obtain ⟨-, HI⟩ := k4IndexTie_of_ownMsgsG h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
    (cells := id) (weights := reader) (tokens := k4Tokens) (look := k4LookAt)
    (k4Pub_head h Lh) hLend Oi (fun _ _ _ _ hT => hval hT) (fun _ _ _ _ hT => hlen hNi hT)
  obtain ⟨xl, hx, -⟩ := layAt_laid h Lh
  have hS := k4CellsSmall_of_index h hA toIndex hTrace (F0T OnBytes.secondHashFunction Zp Np cF) Vd hV
    x.2.hp.tl (k4PubAt cF k x) reader k4Tokens k4LookAt
  have hc : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∀ d, CellIsList (k4PubAt cF k x)
        (k4Wit (k4PubAt cF k x) id reader k4Tokens (k4LookAt (k4PubAt cF k x)) mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) x.2.hp.tl :=
    fun c _ mm _ hT d => cellIsList_at Lh hx (k4Pub_head h Lh) hSz L L' hrd hS c mm.st.input
      (mm.st.heard ++ d) (hval hT.1) (by
        rw [List.length_append]
        exact Nat.le_trans (hlen hN hT.1) (Nat.le_add_right _ _))
  obtain rfl := Lh.num
  obtain rfl := Lh.seg
  have Ak := atK4_full g hg
  have hop : ∀ i : VerifiableInference.Desc.First.Item,
      i ∈ ((lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.row (28 * g + 4)).asks →
      i ∈ (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.opened (28 * g + 4) :=
    fun i hi => open_k4 (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) onePass_full hi
  rw [asks_k4 (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) Ak] at hop
  intro j hj
  rw [owes_k4 (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) Ak] at hj
  unfold restK4 at hj
  rcases List.mem_cons.1 hj with rfl | hj
  · exact fun blk hb c₀ s₀ m₀ E₀ ds y cols s' hT₀ hd hS' =>
      k4_exchange_own_by h Q test carryX item n₁ n₂ b₀ Vd Rd (fun _ _ _ => True) w₁ hA ν st R hRdIs
        Said Lh id reader hM hE ho hb₀ (fun _ _ _ => trivial) hMask hc hI
        (fun hv => hVd_of_readyInput (hV _ hv)) (fun hv => hW4_of_readyInput (hV _ hv))
        blk hb c₀ s₀ m₀ E₀ ds y cols s' hT₀ hd hS'
  rcases List.mem_cons.1 hj with rfl | hj
  · exact k4_exchange_planes_head h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
  rcases List.mem_cons.1 hj with rfl | hj
  · exact k4_exchange_join_head h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh
  rcases List.mem_cons.1 hj with rfl | hj
  · refine k4_exchange_wo_index_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hA Said Lh id reader hM
      hE ho hI hMask ?_
    intro blk hbk c s mm E ds y cols s' hT hd hSt cc name endName cp hl hs
    obtain ⟨cc', hl', H⟩ := HI blk hbk c s mm E ds y cols s' hT hd hSt
    obtain rfl : cc' = cc := Except.ok.inj (hl'.symm.trans hl)
    exact H name endName cp hs
  rcases List.mem_cons.1 hj with rfl | hj
  · exact exchangeAtS_pin h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ _ 0 Said hKs
      (hop _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) hB
  rcases List.mem_cons.1 hj with rfl | hj
  · exact exchangeAtS_of _ Said (exchangeAt_pinW h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ _)
  rcases List.mem_cons.1 hj with rfl | hj
  · exact exchangeAtS_again _ _ (hop _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.head _)))))))) hB (ridesPastAtS_of _ _
        (ridesPastAt_constr h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ _ _ (by decide)))
  rcases List.mem_cons.1 hj with rfl | hj
  · exact exchangeAtS_pinI h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said hKs
      (hop _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) hB
  · cases hj

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4IndexIs_of_reader
#print axioms ProofFile.Honest.K4.W.k4_exchange_all_items
