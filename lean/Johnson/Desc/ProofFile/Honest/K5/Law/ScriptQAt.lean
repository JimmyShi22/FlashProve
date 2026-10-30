-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ScriptQAt.lean: CONDITIONAL: UNDER THE LIBRARY's HEAD, WITH THE
THREAD T A VARIABLE: the ties of an attention segment's own rounds (kind K5) at a stand (K5Script,
Honest/K5/Law/Script.lean) OUT OF THE TWO EQUATIONS ON THE SCRIPT ALONE (K5ScriptQ,
Honest/K5/Law/ScriptQ.lean); and the member's debts in one statement with these in the ties' stead.
Definitions, and statements with their proofs.

  slotsForm, fs5, fs5_slots   a form, and the list of that one form, that names n slots from ν on
  CoinsFew       the book lends the row no more coins than n
  names5_of      under CoinsFew that list names each slot under which a coin of the row lies
  hereAtt_T      at every stand of the kind's border the open part is an attention segment's, and
                 its ledger has room for the kind's slots
  addrAt_T       **AddrAt is no premise under the head**: at fs5, under LedgerIs
  k5Script_of_Q_T  **K5Script from K5ScriptQ, LedgerIs, CoinsFew and the third field's text**
  k5_owes_all_Q  all of the member's debts in one statement (k5_owes_all_T,
                 Honest/K5/Law/RidesT.lean), its premise K5Script struck for these

WHAT STAYS, BY NAME. The head · K5AtT and K5RidersT (what is spent of T's letters) · g is below 12 ·
PlanAt (facts on the public plan) · x₁ is the place of the segment's lookup on the calls · K5Seated
· T's chain has the number 0 · T's valid inputs meet Vd · N is at most the number of challenges
heard at the border · on the witness: K5ScriptQ: TWO EQUATIONS ON THE SCRIPT, cells, THE BOOK AND
PUBLIC LETTERS: SHOWN NOWHERE · that T's witness, read by wt, is the Script's · LedgerIs: at the
border in front the ledger's next free slot is ν₅: SHOWN NOWHERE · CoinsFew: the book lends the row
no more coins than the kind takes slots · the third field's text (the key points: it reads no
Script) · and k5_owes_all_T's other premises, as they stand there.

Limits. The library's full size and head alone. The head is a hypothesis. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ScriptQ
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesT
import Johnson.Desc.K5.Honest.Law.AddrTieFs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Aff)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Strs Chain)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (K3Pts slotsOf script segAt_front seatSO)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open H2K5.Honest (K5Keeps addrTie_head_fs front_at_head)
open ProofFile.Honest.FirstThread (Script WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

/-! ## 1 A list of forms that names the slots -/

/-- A form that names the n slots from ν on, each with the coefficient 0. IT IS A LIST OF NAMES: it
is evaluated nowhere, and no statement here reads a coefficient of it. -/
def slotsForm (ν n : Nat) : Aff :=
  { slots := ((List.range n).map fun j => (ν + j, zeroE)).toArray }

/-- The list of that one form. -/
def fs5 (ν n : Nat) : List Aff := [slotsForm ν n]

/-- What it names. -/
theorem fs5_slots {ν n : Nat} {f : Aff} (hf : f ∈ fs5 ν n) {z : Nat × E}
    (hz : z ∈ f.slots.toList) : ∃ j, j < n ∧ z.1 = ν + j := by
  obtain rfl := List.mem_singleton.1 hf
  have hz' : z ∈ (List.range n).map fun j => (ν + j, zeroE) := hz
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz'
  exact ⟨j, List.mem_range.1 hj, rfl⟩

/-- The book lends the row no more coins than n. It is a definition: a premise's form. -/
def CoinsFew (Bk : ProverCoinCounts) (Z : Seat5) (n : Nat) : Prop := ∀ k : Coins Bk, (coins5 Bk k Z).length ≤ n

/-- It names each slot under which a coin of the row lies. CONDITIONAL on CoinsFew. -/
theorem names5_of {Bk : ProverCoinCounts} {Z : Seat5} {ν n : Nat} (h : CoinsFew Bk Z n) :
    Names5 Bk Z ν (fs5 ν n) := fun k j hj =>
  ⟨slotsForm ν n, List.mem_singleton.2 rfl, (ν + j, zeroE),
    (List.mem_map.2 ⟨j, List.mem_range.2 (Nat.lt_of_lt_of_le hj (h k)), rfl⟩ :
      (ν + j, zeroE) ∈ (List.range n).map fun j => (ν + j, zeroE)), rfl⟩

/-! ## 2 Under the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : VerifiableInference.Desc.First.Item → T.ι} {pb : T.P → ProofFile.InstPub}
  {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (R : K5AtT h T g it pb wt ans test carryX cq)
include R

/-- **At every stand of the kind's border the open part is an attention segment's.** CONDITIONAL:
the head; the structure; g is below 12; the plan's facts. -/
theorem hereAtt_T (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a) {k : Coins Bk}
    {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr T (borderOf g) k s m E) :
    ∃ att, s.here = .att att ∧ att.F.next + slotsOf (script a.own) ≤ att.F.ns := by
  obtain ⟨att, _, e, _, _, _, hf⟩ := (readyO_T h R hg Pl hT).open_
  exact ⟨att, e, hf.2.1⟩

/-- **AddrAt is no premise under the head.** CONDITIONAL: as hereAtt_T; x₁ is the place of the
segment's lookup on the calls; LedgerIs. -/
theorem addrAt_T (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {ν₅ : Nat}
    (hL5 : LedgerIs T (borderOf g) ν₅) :
    AddrAt h T (borderOf g) x₁ a (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      (fs5 ν₅ (slotsOf (script a.own))) := by
  intro k s m E hT pt hpt w
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  obtain ⟨att, e, hfree⟩ := hereAtt_T h R hg Pl hT
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨blk, _, hb, _, _⟩ := k5_member h hg
  have hr := reach_T h R (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  obtain ⟨_, _, _, Fa, _, _, _⟩ := front_at_head h hL hg Pl.plan hx (honest (mgAtAll h) ans test)
    rfl rfl _ _ (open8_at hg) hr hu hon e
  have led : seatSO.ledger s = some att.F := by
    show (match s.here with
      | .att a => some a.F
      | _ => none) = _
    rw [e]
  have hns : att.F.ns ≤ a.ns := (Fa.ledger att.F led).2.1
  have hF : pt.F = att.F := by
    have e2 := Option.some.inj ((segAt_front e).symm.trans hpt)
    rw [← e2]
    rfl
  have hν : att.F.next = ν₅ := by
    rw [← hF]
    exact hL5 k s m E hT pt hpt
  refine addrTie_head_fs h hL hg Pl.plan hx (honest (mgAtAll h) ans test) rfl rfl _ _
    (open8_at hg) hr hu hon e hpt w _ fun f hf z hz => ?_
  obtain ⟨j, hj, ez⟩ := fs5_slots hf hz
  omega

/-- **K5Script from the two equations on the Script.** CONDITIONAL: see the head. -/
theorem k5Script_of_Q_T (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁)
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N ν₅ : Nat} {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (hw : ∀ k v hd, wt (T.wit k v hd) = Q.wit k v hd) (hc : T.chain = 0)
    (hv : ∀ v, T.valid v → Vd v) (hN : N ≤ T.front + roundsTo T.bs (borderOf g))
    (HQ : K5ScriptQ h Q Vd N x₁ a cells Z5 ν₅) (hL5 : LedgerIs T (borderOf g) ν₅)
    (hfew : CoinsFew Bk Z5 (slotsOf (script a.own)))
    (hK : ∀ k s m E, Thr T (borderOf g) k s m E → ∀ att, s.here = .att att →
      ∃ g', att.g = some g' ∧
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
        ∀ ds n, drawsFit blk.rounds ds = true → Z5.keyAt (m.st.heard ++ ds.take n) = g'.zk) :
    K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v) :=
  k5Script_of_Q wt hw hc hv hN HQ hL5 (addrAt_T h R hg Pl hx hL5) (names5_of hfew) hK

/-- **ALL OF THE MEMBER's DEBTS IN ONE STATEMENT, THE PREMISES ON THE WITNESS ON THE SCRIPT ALONE.**
CONDITIONAL: see the head. -/
theorem k5_owes_all_Q (Rr : K5RidersT h T g it pb wt ans test carryX cq) {n : Nat} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → T.keeps (borderOf g) s s')
    (Rd : ∀ w s s', T.rides (borderOf g) w s → K5Keeps s s' → T.rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hidx : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g)))
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N ν₅ : Nat}
    (hw : ∀ k v hd, wt (T.wit k v hd) = Q.wit k v hd) (hc : T.chain = 0)
    (hv : ∀ v, T.valid v → Vd v) (hN : N ≤ T.front + roundsTo T.bs (borderOf g))
    (HQ : K5ScriptQ h Q Vd N x₁ a cells Z5 ν₅) (hL5 : LedgerIs T (borderOf g) ν₅)
    (hfew : CoinsFew Bk Z5 (slotsOf (script a.own)))
    (hK : ∀ k s m E, Thr T (borderOf g) k s m E → ∀ att, s.here = .att att →
      ∃ g', att.g = some g' ∧
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
        ∀ ds n, drawsFit blk.rounds ds = true → Z5.keyAt (m.st.heard ++ ds.take n) = g'.zk)
    (hP : Z5.P = ⟨a.S, a.own⟩) (hV : IdnOwed T.valid cells Z5) :
    (Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      RidesPast T (borderOf g)) ∧ ∀ fall, Accepted T fall (borderOf g) :=
  k5_owes_all_T h R Rr hg Pl.plan Hs hfit hb Kp Rd hans hidx
    (k5Script_of_Q_T h R hg Pl hx hw hc hv hN HQ hL5 hfew hK) hP hV

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.fs5_slots
#print axioms ProofFile.Honest.K5.names5_of
#print axioms ProofFile.Honest.K5.hereAtt_T
#print axioms ProofFile.Honest.K5.addrAt_T
#print axioms ProofFile.Honest.K5.k5Script_of_Q_T
#print axioms ProofFile.Honest.K5.k5_owes_all_Q
