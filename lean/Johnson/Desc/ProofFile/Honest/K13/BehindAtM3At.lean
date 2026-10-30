-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/BehindAtM3At.lean: kind K13, the members' batching: THE PREMISES
OF `k13_thread_behind` (BehindAtM3.lean of this folder) ON THE TABLE AND ON THE MEANING, AT THE
LIBRARY's OWN PARAMETERS (`FirstThread.lettersAt`, Honest/Thread/FirstAt.lean): the full size.
Statements with their proofs: two evaluations by Lean's kernel on the written lists; calls of the
library's own lemmas.
Main names:
  `m3_rowB`: the library's test on the table at the kind's row (`rowM3B`,
    Johnson/Desc/K13/Law/AtTableRow.lean) accepts at number 355 of the written list of places, at
    the list of further public items of the library's own meaning (`mgMore`,
    Johnson/Desc/Sound/MgAllAt.lean).
  `m3_noPub`: at that list no public item is open at the border number 355.
  `pubM3_base`: **`PubM3` at the library's composed meaning over its closed base, at every data**:
    by `fillsK13C_base` (Johnson/Desc/AtSeats/FillsAtBase.lean) and `mgAll_inOrder_base`
    (Johnson/Desc/Sound/MgBase.lean). `pubM3_at`: so at the library's own parameters.
  `rowM3_at`: **`RowM3` there**, from two equations on the plan's numbers.
  `counts_at`: **the two equations**: by the plan's numbers as many trees and as many oracle
    messages stand behind the kind's sub-protocol as in front of it: since it states no oracle
    message: by the library's `counts_at_quiet` (Johnson/Desc/AtSeats/CountsAtSend.lean), `N_at` and
    `places_paid` (Johnson/P5J/PlacesPaid.lean).
  `k13_thread_form_at`: **THE FIRST CLAUSE OF `Behind` AT NUMBER 355, FROM THE HYPOTHESIS UNDER
    WHICH THE PARAMETERS ARE LAID, AND FROM NOTHING ELSE.**
  `k13_thread_behind_at`: **`Behind` at number 355 of the first chain's thread at these
    parameters.**

The premises that stay in `k13_thread_behind_at`. The hypothesis under which the parameters are
laid. `rides` and `keeps`, which have no text: asked as `Behind` asks them, under the thread in
front and the member's accepted step.

What is not claimed. That the hypothesis under which the parameters are laid can be met. The two
premises that stay. That the thread holds at any run, or that the member's step accepts. The two
evaluations by the kernel run over the written list of 358 places; they have not been tried at a
second proof checker. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.ProofFile.Honest.K13.BehindAtM3
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt
import Johnson.Desc.AtSeats.FillsAtBase
import Johnson.Desc.K13.Law.AtTableRow
import Johnson.Desc.AtSeats.CountsAtFour
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Block Chain OpenedColumn Strs)
open VerifiableInference.Desc.First (pubSets)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (atM3 whereOf)
open VerifiableInference.Desc.K13.Law (dOf RowM3 rowM3B rowM3_of_test fillsK13C_base)
open VerifiableInference.Desc.K13.Honest (withClaim PubM3 pubM3_of_fills)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgMore mgAll_more_base
  mgAll_inOrder_base)
open OnBytes.Maker (WholeD)
open P5J (AtMgA mgAtAll CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt Script WtF)

set_option maxRecDepth 1000000 in
/-- The library's test on the table at the kind's row accepts. -/
theorem m3_rowB : rowM3B mgMore P5J.At.links P5J.At.ps 355 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- No public item is open at the border in front of the kind's place. -/
theorem m3_noPub : ((pubSets mgMore P5J.At.links P5J.At.ps)[355]?).getD [] = [] := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What the promise's step reads of the meaning, at the library's composed meaning over its
closed base: at every data.** -/
theorem pubM3_base {Xi Pp Tok : Type} {rows cols nR : ℕ} {Xp : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi Pp Tok rows cols nR Xp) : PubM3 Dm.P13 Dm.N (mgAll Dm mgBase) :=
  pubM3_of_fills (fillsK13C_base Dm) fun p s s' => by
    rw [mgAll_inOrder_base, mgAll_inOrder_base]

/-- So at the library's own parameters. -/
theorem pubM3_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    PubM3 h.𝔇.P13 h.𝔇.N (mgAtAll h) := pubM3_base h.𝔇

/-- **What is asked of the table**, from two equations on the plan's numbers. -/
theorem rowM3_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (N : VerifiableInference.Desc.First.Numbers)
    (hNt : N.treesAt P5J.At.ps[355 + 1]? = N.treesAt P5J.At.ps[355]?)
    (hNm : N.msgsAt P5J.At.ps[355 + 1]? = N.msgsAt P5J.At.ps[355]?) :
    RowM3 N (mgAtAll h).more P5J.At.links P5J.At.ps 355 := by
  have e : (mgAtAll h).more = mgMore := mgAll_more_base h.𝔇
  rw [e]
  exact rowM3_of_test mgMore _ _ 355 m3_rowB N hNt hNm

/-- **By the plan's numbers as many trees and oracle messages stand behind a sub-protocol number 355
that states no oracle message as in front of it.** -/
theorem counts_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (ho : ∀ blk, cF.blocksInOrder[355]? = some blk → blk.oracles.flatten = []) :
    (P5J.At.N Zp cF).treesAt P5J.At.ps[355 + 1]? = (P5J.At.N Zp cF).treesAt P5J.At.ps[355]? ∧
      (P5J.At.N Zp cF).msgsAt P5J.At.ps[355 + 1]? = (P5J.At.N Zp cF).msgsAt P5J.At.ps[355]? := by
  have hps := P5J.At.places_paid h.scope h.reads h.laid
  have hn : P5J.At.ps.Nodup := HashBuild.places_nodup_full
  cases hb : cF.blocksInOrder[355]? with
  | none =>
    have e : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder)[355]? = none := by
      show (cF.blocksInOrder.map (·.place))[355]? = none
      rw [List.getElem?_map, hb]
      rfl
    rw [hps, m3_place] at e
    cases e
  | some blk =>
    rw [P5J.At.N_at h.scope h.reads h.laid]
    exact VerifiableInference.Desc.K1.counts_at_quiet _ _ _ cF.blocksInOrder _ hps hn 355 blk hb (ho blk hb)

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- What is asked of the table, at these parameters. -/
theorem m3_rowM3 : RowM3 (P5J.At.N Zp cF) (mgAtAll h).more P5J.At.links P5J.At.ps 355 :=
  rowM3_at h _
    (counts_at h fun blk hb => by rw [(m3_member_fields h hb).2]; simp).1
    (counts_at h fun blk hb => by rw [(m3_member_fields h hb).2]; simp).2

/-- No public item is open in front, at these parameters. -/
theorem m3_noPub_at : ((pubSets (mgAtAll h).more P5J.At.links P5J.At.ps)[355]?).getD [] = [] := by
  rw [show (mgAtAll h).more = mgMore from mgAll_more_base h.𝔇]
  exact m3_noPub

/-- **THE FIRST CLAUSE OF `Behind` AT THE KIND's MEMBER, AT THE LIBRARY's OWN PARAMETERS**: from the
thread's form in front and the member's accepted step: the form behind. -/
theorem k13_thread_form_at {blk : Block TS ProofFile.Cl}
    (hb : (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.bs[355]? =
      some blk) {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hF : Thread.Form
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s m)
    (hS : Thread.Stepped
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread blk k s m En ds
      y cols s') :
    Thread.Form
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread (355 + 1) k s'
      y.2 :=
  k13_thread_form_behind (Cl' := Unit)
    (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (m3_rowM3 h) (pubM3_at h)
    (m3_noPub_at h) (fun rs gs t' => (k13_memberIs_at h).back _ hb s rs gs t') hF hS

/-- **`Behind` at the kind's member, at the library's own parameters.** hrides, hkeeps: the two
clauses that have no text, as `Behind` asks them. -/
theorem k13_thread_behind_at
    (hrides : ∀ blk,
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.bs[355]? =
        some blk → ∀ k s m En ds y cols s',
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s m
        En → drawsFit blk.rounds ds = true →
      Thread.Stepped
        (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread blk k s m En
        ds y cols s' → rides (355 + 1) y.2.st.input s')
    (hkeeps : ∀ blk,
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.bs[355]? =
        some blk → ∀ k s m En ds y cols s',
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s m
        En → drawsFit blk.rounds ds = true →
      Thread.Stepped
        (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread blk k s m En
        ds y cols s' → keeps 355 s s') :
    Behind (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 :=
  k13_thread_behind (Cl' := Unit)
    (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (m3_rowM3 h) (pubM3_at h)
    (m3_noPub_at h) (fun _ hb s rs gs t' => (k13_memberIs_at h).back _ hb s rs gs t') hrides hkeeps

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.m3_rowB
#print axioms ProofFile.Honest.K13.m3_noPub
#print axioms ProofFile.Honest.K13.pubM3_base
#print axioms ProofFile.Honest.K13.pubM3_at
#print axioms ProofFile.Honest.K13.rowM3_at
#print axioms ProofFile.Honest.K13.counts_at
#print axioms ProofFile.Honest.K13.m3_rowM3
#print axioms ProofFile.Honest.K13.m3_noPub_at
#print axioms ProofFile.Honest.K13.k13_thread_form_at
#print axioms ProofFile.Honest.K13.k13_thread_behind_at
