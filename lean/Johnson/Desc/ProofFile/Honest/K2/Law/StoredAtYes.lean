-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/StoredAtYes.lean: the kind "the code switch" (K2): THE FIELD
stored OF THE RECORD `MadeAsks` (ExchangeAtMade.lean of this folder), IN ITS OWN TEXT, AT THE KIND's
OWN YES, AT EVERY WRITTEN SWITCH: at the first chain's letters at the library's head, at the exact
carry. A definition: a public test. Closed facts by Lean's kernel, with a control; statements with
their proofs.

WHICH SLOT IT IS FOR. `stored` is a limb of `ValuesLeft` (MadeValuesLeft.lean), which
`k2_exchange_of_values` leaves at each switch; `claim_at_yes` (ClaimAtYes.lean) is its sister at the
limb claim, under the same premise hA.

  `keptShapeB`, `keptShapeW`, `keptShapeW_can_fail`   at each written link a kept member has one
                    answer and no mask row; with two answers asked: no, at some member
  `link_front_facts`   `FrontFacts` and the front's oracle messages, at a link
  `reads_of_made`   where the switch's rows are made, each stored sample row of a kept message
                    reads that message's main table alone
  `says_move`       such a row says at a second statement what it says at a first, where that
                    message's table has one size at both
  `stored_core`     the field's text at the front's statement, from the thread's stand, the front's
                    facts, the walk's last step and `LockAsks`
  `stored_at_yes`   THE END

By: `kept_answers` (KeptAnswers.lean) · `stored_of_answers` (StoredOfAnswers.lean) · `one_stored`
(Johnson/Top/H0/Tw/K2C/OneStored.lean) · `both_at_switch` (AtYesRows.lean), `shape_below_at_reach`,
`samples_of_tables` (AtYesFits.lean), of other authors · `rch_at_head`, `sizes_front_at_yes`,
`frontAt_stands` (ClaimAtYes.lean) · `laid_of` (Johnson/Top/H0/K2Hands/RowsAt.lean) · `frame_fields`
(Johnson/Top/H/SwitchMapsCheck.lean) · `link_lastStep`, `head_lastStep`, `fin_lastStep`
(MembersAtWalk.lean) · `lotClosingAt_kept` (HonestAtClosing.lean) · `segmentsOf_at_front`
(SegmentsAtFront.lean) · `padded_first` (Johnson/Desc/K10/Honest/CarryOf.lean) · `value_named`,
`size_same`, `onTable_same` (Honest/K1/AnswersChain.lean).

Limits. AN IMPLICATION. hT, hOk, hst AND hty ARE PREMISES, ON THE THREAD's STAND. hA IS A PREMISE:
at `link_lockAsks`, `first_lockAsks`, `head_lockAsks`, `fin_lockAsks` it stands under their own
premises. `stored_core` and `stored_at_yes` bind the run's coins k and kk, from which the closing
has the carried coins; the witness's words at them stand in hA: one run's coins: never quoted for a
law. The field stands at the statement behind the joins; what passes it from the front's is that the
row reads one table. That the item pinKept is open with its meaning is the thread's: what pays it is
the closing's exchange: not here. NOT IN FRONT OF A LAW OVER COINS. CLOSED FACTS BY
LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. The full size; the format's second hash function. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeptAnswers
import Johnson.Desc.ProofFile.Honest.K2.Law.ClaimAtYes
import Johnson.Desc.ProofFile.Honest.K2.Law.AtYesRows
import Johnson.Desc.ProofFile.Honest.K2.Law.MembersAtWalk
import Johnson.Top.H0.K2Hands.RowsAt
import Johnson.Desc.K10.Honest.CarryOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes
open OnBytes.Slice (GE readE rdE)
open OnBytes.Means (Words Says tableSize onTable)
open Johnson.Pack (pMain pMask)
open VerifiableInference.Desc (Chain Place Strs Block fieldPrimeWord)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes frontAt one_stored SampleGoodS AnsweredStored)
open VerifiableInference.Desc.First.K2Hands (readsMain laid_of)
open VerifiableInference.Desc.First.Close (noK10)
open VerifiableInference.Desc.LinkJoin (loAt kbW)
open VerifiableInference.Desc.K2.Honest (GroupMember Left sizesAt oldWords membersTrue carryExact
  reads_off)
open VerifiableInference.Desc.K2.Honest.Returns (AlikeKept link_door head_door fin_door
  link_membersTrue_front head_membersTrue_front fin_membersTrue_front link_membersNumbered_front
  link_member_stated link_word_front link_frontTies)
open VerifiableInference.Desc.Sound (MsgT allOf EAll wordsFirst below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script lettersHead)
open IM (k2P)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- A PUBLIC TEST ON THE WRITTEN PLAN. d: 0 is the test; 1 asks for two answers, for a control. -/
def keptShapeB (d : Nat) : Bool :=
  (List.range 25).all fun l =>
    (VerifiableInference.Desc.First.Close.membersOf (loAt l)).all fun i =>
      !kbW l i || (((loAt l).get i).1.answers == 1 + d && ((loAt l).get i).1.maskRows == 0)

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL. -/
theorem keptShapeW : keptShapeB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control. -/
theorem keptShapeW_can_fail : keptShapeB 1 = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- No run is given at which the head's premise and "reached" hold together. **`FrontFacts` and the
front's oracle messages, at a link** (m < 23). -/
theorem link_front_facts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {q : P2} (hq : q.stands = .link)
    {fx : _root_.Tw.K2.Front} (hfx : frontAt q a.1.2 = some fx) :
    FrontFacts Zp m a.1.2.book fx ∧ fx.st.oracles = a.1.2.st.oracles := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hu, hst⟩ := link_member_stated h h23 a hr
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_link h.scope h.reads O (l := m + 1) (by omega)
    (by omega) f hq hfx
  refine ⟨⟨link_membersNumbered_front h h23 a hr hq hfx,
    fun i hi => member_shape_getD h (by omega) a hr hu (by omega) i (hst i hi) a2, ?_,
    link_frontTies h.scope h.reads O h23 (h.toAtMg.rch_is_reach _ a hr) hq hfx⟩, a2⟩
  intro i hi Cells' Tok' arr v part b hb j
  exact link_word_front h h23 a hr hq hfx i hi arr v part hb j

/-- **Where the switch's rows are made, each stored sample row of a kept message reads that
message's main table alone.** -/
theorem reads_of_made {St : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {pos : Positions} {y : Array E} {rows : List OnBytes.Row}
    (hm : switchRows St old T g anew pos y = some rows) :
    ∀ o ∈ (switchKept old).toList, ∀ r ∈ (St.oracles.getD o default).sampleRows.toList,
      readsMain o r = true := by
  obtain ⟨W, c, L⟩ := laid_of hm
  obtain ⟨-, -, -, -, -, -, -, f8⟩ := Johnson.Top.H.frame_fields St old T g anew W L.frame
  intro o ho r hr
  obtain ⟨a, ha⟩ := List.getElem?_of_mem ho
  have hlt : a < (switchKept old).size := by
    have := (List.getElem?_eq_some_iff.1 ha).1
    rwa [Array.length_toList] at this
  have eo : (switchKept old).getD a noId = o := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ha]
    rfl
  have hmem : ∃ k ∈ W.kept, k.old = o := by
    rw [f8]
    exact ⟨_, List.mem_map.2 ⟨a, List.mem_range.2 hlt, rfl⟩, eo⟩
  obtain ⟨k, hk, rfl⟩ := hmem
  exact L.reads k hk r hr

/-- hs IS A PREMISE. **A row that reads the message o's main table alone says at a second statement
what it says at a first**, where that table has one size at both. -/
theorem says_move (A B : Statement) (w : Words GE) {o : Nat} {r : OnBytes.Row}
    (hr : readsMain o r = true) (ht : tableSize B o .main = tableSize A o .main)
    (hs : Says rdE A r w) : Says rdE B r w := by
  have hN : VerifiableInference.Desc.First.Close.NamesOne r o := fun o' hne part e =>
    reads_off o r hr o' part e (fun h => hne h.1)
  have hz : ∀ St : Statement, onTable rdE St r w o .mask = 0 := fun St => by
    unfold onTable
    refine Finset.sum_eq_zero fun i _ => ?_
    show readE (r.coefficient o .mask i) * _ = 0
    have := reads_off o r hr o .mask i (fun h => by cases h.2)
    rw [show readE (r.coefficient o .mask i) = 0 from this, zero_mul]
  unfold Says at hs ⊢
  rw [ProofFile.Honest.K1.value_named A r o hN, hz, add_zero] at hs
  rw [ProofFile.Honest.K1.value_named B r o hN, hz, add_zero, ← hs]
  exact ProofFile.Honest.K1.onTable_same A B r w w o .main ht fun _ => rfl

/-- ALL ARE PREMISES. One run's coins: never quoted for a law. **The field's text, at the front's
statement.** F, hN, hfo: the front's facts. L, hy: the walk's last step, with what it hands
on. hA: `LockAsks` at the Script's witness's words. -/
theorem stored_core (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p : SwitchPlace} (hp : p ∈ placesW) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread (switchNo p) k s m E)
    {l : Nat} (el : p.link = l + 1) {book : TreeBook} {x : _root_.Tw.K2.Front}
    (F : FrontFacts Zp l book x)
    (hN : membersTrue x.st x.f.rows =
      (VerifiableInference.Desc.First.Close.membersOf (loAt l)).map fun i =>
      (⟨((loAt l).get i).1, kbW l i⟩ : GroupMember))
    (hfo : x.st.oracles = s.st.oracles) (ds : List Fmt.Drawn)
    {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {kk : Nat → Except String Stretch} {y : Option (Left × List OracleShape) × Nat}
    (L : LastStep freshTable own heard kk l y (membersTrue x.st x.f.rows))
    {Wl : Left} {kept : List OracleShape} (hy : y.1 = some (Wl, kept))
    (hA : LockAsks freshTable own heard kk l x
      (wordsFirst (P5J.At.arr Zp) x.st book (Q.wit k m.st.input (m.st.heard ++ ds))))
    (hG : SampleGoodS x.st) (hAn : AnsweredStored x.st)
    (once : (switchKept x.f.rows).toList.Nodup)
    (hlt : ∀ o ∈ (switchKept x.f.rows).toList, o < x.st.oracles.size)
    (hcodeK : ∀ o ∈ (switchKept x.f.rows).toList,
      (x.st.oracles.getD o default).shape.code = x.f.rows.code)
    (hread : ∀ o ∈ (switchKept x.f.rows).toList,
      ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList, readsMain o r = true) :
    ∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList,
      Says rdE x.st r (oldWords (sizesAt x.st x.f.rows x.T) x.f.rows Wl) := by
  obtain rfl : l = p.link - 1 := by omega
  obtain ⟨-, h1, h25⟩ := k2_pinKept_at hp
  obtain ⟨Sg, y', W, kept', hSg, hC, hy₁, hW, hM⟩ := L
  have e := Option.some.inj (hy₁.symm.trans hy)
  obtain rfl : W = Wl := congrArg Prod.fst e
  obtain rfl : kept' = kept := congrArg Prod.snd e
  obtain ⟨-, hE⟩ := hA Sg y' hSg hC
  have hmem : Sg ∈ segmentsOf Zp Bs.G₀ := by
    rw [segments_at_head h.toAtMg O]
    exact List.mem_of_getElem? hSg
  obtain ⟨c1, c2, c3⟩ := segmentsOf_at_front O F.ties hmem
  obtain ⟨G, HL⟩ := F.ties.lay
  have hsz : x.f.rows.layout.kept.size = x.f.rows.layout.members.size := by
    rw [HL.kept, HL.members]
    exact HL.sizes
  have shapeK : ∀ o ∈ (switchKept x.f.rows).toList, ∀ xo : Oracle, x.st.oracles[o]? = some xo →
      xo.shape.answers = 1 ∧ xo.shape.maskRows = 0 := by
    intro o ho xo hx
    obtain ⟨i, hi, hk, rfl⟩ := kept_index F.numbered hN ho
    have t := List.all_eq_true.1 (List.all_eq_true.1 keptShapeW (p.link - 1)
      (List.mem_range.2 (by omega))) i hi
    rw [hk] at t
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, Nat.add_zero] at t
    have g : x.st.oracles.getD
        (noK10 (P5J.At.seats Zp) (loAt (p.link - 1)) (P5J.At.pseats Zp) (p.link - 1) i) default =
        xo := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    have es := F.shape i hi
    rw [g] at es
    rw [es]
    exact t
  refine stored_of_answers x.st x.f.rows x.T _ hW c1 c2 c3 hsz F.ties.pow
    (fun R hR => ⟨hM R hR, (hE R hR).1⟩)
    (ProofFile.Honest.K10.LeftIs.padded_first ⟨rfl, fun _ => rfl⟩ _ _ _) once hlt ?_ hread
    hcodeK ?_ ?_ ?_
  · intro o ho
    have hx : x.st.oracles[o]? = some (x.st.oracles[o]'(hlt o ho)) :=
      Array.getElem?_eq_getElem (hlt o ho)
    exact one_stored hG hAn hx (shapeK o ho _ hx).1
  · intro o ho xo hx _
    have g : x.st.oracles.getD o default = xo := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    have hc' := hcodeK o ho
    rw [g] at hc'
    show 2 ^ ceilLog2 (x.st.codes.base.getD xo.shape.code default).ell =
      (x.st.codes.base.getD xo.shape.code default).ell
    rw [hc', ← F.ties.pow, OnBytes.Slice.ceilLog2_two_pow]
  · intro o ho xo hx hpos
    rw [(shapeK o ho xo hx).2] at hpos
    exact absurd hpos (Nat.lt_irrefl _)
  · intro o ho xo hx
    exact kept_answers h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w hp hT F
      hN hfo ds ho xo hx

/-- hOk, hst, hty, hT, A, hW AND hA ARE PREMISES. One run's coins: never quoted for a law.
NOT IN FRONT OF A LAW OVER COINS. **THE FIELD stored, IN ITS OWN TEXT, AT THE KIND's
OWN YES, AT EVERY WRITTEN SWITCH.** -/
theorem stored_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    {p : SwitchPlace} (hp : p ∈ placesW) {n : P1K2.Nums} {st : VerifiableInference.Desc.First.K2.At}
    {before : TS → Except String TS} {after : TS → TS → Except String TS}
    (hArm : SwitchArm Zp Bs.G₀ p st before after) (hlen : switchNo p ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s s₁ t : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {Ev : Env}
    (hT : ThrS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread Said (switchNo p) k s m Ev)
    (hty : ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub)
    (y₀ : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hb : before s = .ok s₁) (nm : String) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd)
    (ds : List Fmt.Drawn) {lay : OnBytes.Params.ReqLayout} {D : RowData} {Rr : Readers}
    {heard : List Fmt.Drawn} {kk : Nat → Except String Stretch} {Wl : Left}
    (hW : lotClosingAt lay (segmentsOf Zp Bs.G₀) p D Rr heard kk = .ok Wl)
    (hA : LockAsks freshTable (lotOwn segsW p D Rr heard) heard kk (p.link - 1) x
      (wordsFirst (P5J.At.arr Zp) x.st s₁.book (Q.wit k m.st.input (m.st.heard ++ ds)))) :
    ∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (S3.oracles.getD o default).sampleRows.toList,
      Says rdE S3 r (oldWords (sizesAt S3 x.f.rows x.T) x.f.rows Wl) := by
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  have hlk : p.link = p.place.link.getD 25 := beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hp)
  have hR := rch_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w (carryExact Zp (P5J.At.arr Zp)) hOk hst
    hlen hT hty y₀
  have hsz := sizes_front_at_yes h O hpS hArm hR.1 hb nm A
  obtain ⟨SF, hk⟩ := shape_below_at_reach h O hpS hArm hR.1 hb nm A.front
  obtain ⟨hG, hAn⟩ := both_at_switch h O hArm hR.1 hb nm A.front
  have K : AlikeKept x.f.rows x.st z.st := ⟨A.sent.codes, fun o ho => A.sent.old o (hk o ho)⟩
  have hS3 := reads_of_made A.made
  have eK : ∀ o ∈ (switchKept x.f.rows).toList,
      (S3.oracles.getD o default).sampleRows = (x.st.oracles.getD o default).sampleRows :=
    fun o ho => by rw [samples_of_tables A.same o, K.getD o ho]
  have hread : ∀ o ∈ (switchKept x.f.rows).toList,
      ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList, readsMain o r = true :=
    fun o ho r hr => hS3 o ho r (by rw [eK o ho]; exact hr)
  rw [segments_at_head h.toAtMg O] at hW
  obtain ⟨y, hy, ey⟩ := lotClosingAt_kept hW
  have hFront : ∀ o ∈ (switchKept x.f.rows).toList,
      ∀ r ∈ (x.st.oracles.getD o default).sampleRows.toList,
        Says rdE x.st r (oldWords (sizesAt x.st x.f.rows x.T) x.f.rows Wl) := by
    have hArm' := hArm
    rcases hArm' with ⟨rfl, -, h1, h24, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩
    · obtain rfl : s = s₁ := Except.ok.inj hb
      have h23 : p.link - 1 < 23 := by omega
      have el : p.link = (p.link - 1) + 1 := by omega
      have hno : switchNo p = 14 * p.link + 2 := ei
      have eno : switchNo p = 14 * ((p.link - 1) + 1) + 2 := by
        rw [hno, ← el]
      have hR' : h.toAtMg.rch (14 * ((p.link - 1) + 1) + 2) ((m.st.input.x.pub, s), y₀) := by
        rw [← eno]
        exact hR
      obtain ⟨hstd, -⟩ := link_door h h23 _ hR'
      have hf : frontAt (ProofFile.pAtK2 Zp (p.link - 1)) s = some x :=
        (frontAt_stands (q := k2P Zp p.place nm .link n) hstd s).trans A.front
      obtain ⟨F, hfo⟩ := link_front_facts h h23 _ hR' hstd hf
      rw [el] at hy
      exact stored_core h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hp hT.1 el F
        (link_membersTrue_front h h23 _ hR' hstd hf) hfo ds
        (link_lastStep h h23 _ hR' hstd hf hy) ey hA hG hAn SF.once hk SF.keptCode hread
    · obtain rfl : s = s₁ := Except.ok.inj hb
      have e24 : p.link = 23 + 1 := by
        rw [hlk, ep]
        rfl
      have hR' : h.toAtMg.rch 339 ((m.st.input.x.pub, s), y₀) := by
        rw [← ei]
        exact hR
      obtain ⟨hstd, -⟩ := head_door h _ hR'
      have hf : frontAt (ProofFile.pAtK2 Zp 23) s = some x :=
        (frontAt_stands (q := k2P Zp p.place nm .head n) hstd s).trans A.front
      obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ _ hR')).fold
      obtain ⟨Bs', base', O'⟩ := h.laid.opened
      obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_head h.scope h.reads O' f hstd hf
      rw [e24] at hy hA
      exact stored_core h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hp hT.1 e24
        (head_frontFacts h _ hR' hstd hf) (head_membersTrue_front h _ hR' hstd hf) a2 ds
        (head_lastStep h _ hR' hstd hf hy) ey hA hG hAn SF.once hk SF.keptCode hread
    · have e25 : p.link = 24 + 1 := by
        rw [hlk, ep]
        rfl
      have hR' : h.toAtMg.rch 353 ((m.st.input.x.pub, s), y₀) := by
        rw [← ei]
        exact hR
      obtain ⟨hstd, -⟩ := fin_door h _ hR' hb
      have hf : frontAt (ProofFile.pAtK2 Zp 24) s₁ = some x :=
        (frontAt_stands (q := k2P Zp p.place nm .finish n) hstd s₁).trans A.front
      obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ _ hR')).fold
      obtain ⟨Bs', base', O'⟩ := h.laid.opened
      obtain ⟨-, -, -, a4, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O' f hb hstd hf
      rw [e25] at hy hA
      exact stored_core h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hp hT.1 e25
        (fin_frontFacts h _ hR' hb hstd hf) (fin_membersTrue_front h _ hR' hb hstd hf) a4 ds
        (fin_lastStep h _ hR' hb hstd hf hy) ey hA hG hAn SF.once hk SF.keptCode hread
  intro o ho r hr
  have hr' : r ∈ (x.st.oracles.getD o default).sampleRows.toList := by
    rw [← eK o ho]
    exact hr
  rw [hsz]
  refine says_move x.st S3 _ (hread o ho r hr') ?_ (hFront o ho r hr')
  refine ProofFile.Honest.K1.size_same x.st S3 o (A.same.codes.trans A.sent.codes) ?_ .main
  rw [A.same.shape o, K.same o ho]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.keptShapeB
#print axioms ProofFile.Honest.K2.Law.keptShapeW
#print axioms ProofFile.Honest.K2.Law.keptShapeW_can_fail
#print axioms ProofFile.Honest.K2.Law.link_front_facts
#print axioms ProofFile.Honest.K2.Law.reads_of_made
#print axioms ProofFile.Honest.K2.Law.says_move
#print axioms ProofFile.Honest.K2.Law.stored_core
#print axioms ProofFile.Honest.K2.Law.stored_at_yes
