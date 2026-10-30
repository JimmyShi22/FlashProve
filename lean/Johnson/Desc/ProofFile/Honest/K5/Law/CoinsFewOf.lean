-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/CoinsFewOf.lean: THE BOOK LENDS THE ROW OF AN ATTENTION
SEGMENT's OWN ROUNDS (kind K5: the label of that sub-protocol in the description) NO MORE COINS THAN
THE KIND TAKES SLOTS (CoinsFew, Honest/K5/Law/ScriptQAt.lean): DRAWN FROM: THE LENDING RETURNS.
Definitions of propositions, and statements with their proofs.

  scalars_le     the scalars that the parts of a list of stages send are at most the scalars that
                 wait and the slots that the stages take (slotsOf, the verifier's own count)
  scalars_eq, closed_script   they are as many where no scalars wait at the end; at the kind's own
                 list of stages none does
  Lends5         at every run's coins the book's lending to K5's row returns
  coins5_length  where the lending returns, the coins are as many as the row's parts send scalars
  coins5_are     **so they are as many as the kind takes slots**
  coinsFew_of_lent   **Lends5 gives CoinsFew**
  k5_owes_all_lent   all of the member's debts in one statement (k5_owes_all_Q), its premise
                 CoinsFew struck for Lends5

IT IS A TRADE: a premise on how many coins the book lends is paid by a premise that the lending
returns. The second has a source: one return of the frame's ready (k5_lent,
Honest/K5/Law/Lent.lean). The tie on the mask row (K5Script.maskTie, Honest/K5/Law/Script.lean)
speaks only where the lending returns; Lends5 ASKS that it returns, at every run's coins, at the
chain's number 0: that is more than the tie takes.

Limits. That the lending returns anywhere is not shown. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ScriptQAt
import Johnson.Desc.ProofFile.Honest.K5.Law.Coins

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Strs Chain)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (K3Pts slotsOf script)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5Keeps shapes shapesOf PartShape)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-! ## 1 The count -/

/-- The parts' scalars are at most the scalars that wait and the stages' slots. No premise. -/
theorem scalars_le : ∀ (st : List P.Stage) (lead : Nat),
    ((shapesOf lead st).map (·.scalars)).sum ≤ lead + slotsOf st
  | [], _ => Nat.zero_le _
  | .scalars n :: l, lead => by
    have ih := scalars_le l (lead + n)
    show ((shapesOf (lead + n) l).map (·.scalars)).sum ≤ lead + (n + slotsOf l)
    omega
  | .sum vs e :: l, lead => by
    have ih := scalars_le l 0
    show (lead + VerifiableInference.Desc.Part.MaskedSum.ownSlots
        (vs ++ [.point OnBytes.zeroE (e.dY + 1)]) + e.n) +
        ((shapesOf 0 l).map (·.scalars)).sum ≤
      lead + (VerifiableInference.Desc.Part.MaskedSum.ownSlots
        (vs ++ [.point OnBytes.zeroE (e.dY + 1)]) + e.n + slotsOf l)
    omega
  | .batch _ :: l, lead => by
    have ih := scalars_le l 0
    show lead + ((shapesOf 0 l).map (·.scalars)).sum ≤ lead + (0 + slotsOf l)
    omega
  | .point _ :: l, lead => by
    have ih := scalars_le l 0
    show lead + ((shapesOf 0 l).map (·.scalars)).sum ≤ lead + (0 + slotsOf l)
    omega

/-- **Where no scalars wait at the end they are as many.** CONDITIONAL: the verifier's own test
"no scalars wait at the end" (closed, Johnson/Desc/First/Att/K5Returns.lean) says yes; none waits in
front of an empty list. -/
theorem scalars_eq : ∀ (st : List P.Stage) (lead : Nat), P.closed st = true → (lead = 0 ∨ st ≠ []) →
    ((shapesOf lead st).map (·.scalars)).sum = lead + slotsOf st
  | [], _, _, h => by
    rcases h with rfl | h
    · rfl
    · exact absurd rfl h
  | .scalars n :: l, lead, hc, _ => by
    have hc' : (!l.isEmpty && P.closed l) = true := hc
    rw [Bool.and_eq_true] at hc'
    have hl : l ≠ [] := fun e => by
      rw [e] at hc'
      exact absurd hc'.1 (by decide)
    have ih := scalars_eq l (lead + n) hc'.2 (Or.inr hl)
    show ((shapesOf (lead + n) l).map (·.scalars)).sum = lead + (n + slotsOf l)
    omega
  | .sum vs e :: l, lead, hc, _ => by
    have ih := scalars_eq l 0 hc (Or.inl rfl)
    show (lead + VerifiableInference.Desc.Part.MaskedSum.ownSlots
        (vs ++ [.point OnBytes.zeroE (e.dY + 1)]) + e.n) +
        ((shapesOf 0 l).map (·.scalars)).sum =
      lead + (VerifiableInference.Desc.Part.MaskedSum.ownSlots
        (vs ++ [.point OnBytes.zeroE (e.dY + 1)]) + e.n + slotsOf l)
    omega
  | .batch _ :: l, lead, hc, _ => by
    have ih := scalars_eq l 0 hc (Or.inl rfl)
    show lead + ((shapesOf 0 l).map (·.scalars)).sum = lead + (0 + slotsOf l)
    omega
  | .point _ :: l, lead, hc, _ => by
    have ih := scalars_eq l 0 hc (Or.inl rfl)
    show lead + ((shapesOf 0 l).map (·.scalars)).sum = lead + (0 + slotsOf l)
    omega

/-- At the kind's own list of stages no scalars wait at the end. No premise. -/
theorem closed_script (x : OnBytes.Params.AttentionRounds) : P.closed (script x) = true :=
  P.closed_append _ _ (by simp) rfl

/-! ## 2 Where the lending returns -/

variable {W₀ Rc Xi Tr X : Type}

/-- **At every run's coins the book's lending to K5's row returns.** It is a definition: a premise's
form. -/
def Lends5 (W₀ Rc Xi X : Type) {Tr : Type} (Bk : ProverCoinCounts) (cells : Tr → Cells) (Z : Seat5) : Prop :=
  ∀ k : Coins Bk, ∃ u, lendRow Bk (Bk.rowsOf 0) (k.look 0) Z.place
    (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = .ok u

/-- **Where the lending returns, the coins are as many as the row's parts send scalars.** -/
theorem coins5_length {Bk : ProverCoinCounts} {cells : Tr → Cells} {Z : Seat5} {k : Coins Bk}
    {rows : List (Addr × Due)}
    {u : RowCoins (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts}
    (h : lendRow Bk rows (k.look 0) Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = .ok u) :
    (coins5 Bk k Z).length = ((shapes Z.P.x).map (·.scalars)).sum := by
  have hn : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.length =
      (shapes Z.P.x).length := by
    have e := congrArg List.length (half_cut (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z)
    rw [List.length_map] at e
    rw [e]
    exact List.length_map _
  have e1 : coins5 Bk k Z = K5.spentOf _ u := by
    rw [spent_same, spentOf_row Bk _ _ _ _ _ u h, hn]
    rfl
  rw [e1, spentOf_length]
  have e2 := spentNo_take (V := Local W₀ Rc Xi Tr) (X := X) Z.place (chalOf Z) (jobs Z.P)
    (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace)) (shapes Z.P.x) 0
    (shapes Z.P.x).length
  rw [List.take_length, ← k5Half_parts, ← hn, List.take_length] at e2
  exact e2

/-- **Where the lending returns, the coins are as many as the kind takes slots.** -/
theorem coins5_are {Bk : ProverCoinCounts} {cells : Tr → Cells} {Z : Seat5} {k : Coins Bk}
    {rows : List (Addr × Due)}
    {u : RowCoins (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts}
    (h : lendRow Bk rows (k.look 0) Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = .ok u) :
    (coins5 Bk k Z).length = slotsOf (script Z.P.x) := by
  rw [coins5_length h]
  have e := scalars_eq (script Z.P.x) 0 (closed_script Z.P.x) (Or.inl rfl)
  rw [Nat.zero_add] at e
  exact e

/-- **Lends5 gives CoinsFew.** -/
theorem coinsFew_of_lent {Bk : ProverCoinCounts} {cells : Tr → Cells} {Z : Seat5}
    (h : Lends5 W₀ Rc Xi X Bk cells Z) : CoinsFew Bk Z (slotsOf (script Z.P.x)) := fun k => by
  obtain ⟨u, hu⟩ := h k
  rw [coins5_length hu]
  have := scalars_le (script Z.P.x) 0
  rw [Nat.zero_add] at this
  exact this

/-! ## 3 The member's debts -/

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

/-- **ALL OF THE MEMBER's DEBTS IN ONE STATEMENT, CoinsFew STRUCK FOR Lends5.** CONDITIONAL: as
k5_owes_all_Q. -/
theorem k5_owes_all_lent (R : K5AtT h T g it pb wt ans test carryX cq)
    (Rr : K5RidersT h T g it pb wt ans test carryX cq) {n : Nat} (hg : g < 12)
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
    (hlent : Lends5 W₀ Rc ProofFile.Inst X Bk cells Z5)
    (hK : ∀ k s m E, Thr T (borderOf g) k s m E → ∀ att, s.here = .att att →
      ∃ g', att.g = some g' ∧
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
        ∀ ds n, drawsFit blk.rounds ds = true → Z5.keyAt (m.st.heard ++ ds.take n) = g'.zk)
    (hP : Z5.P = ⟨a.S, a.own⟩) (hV : IdnOwed T.valid cells Z5) :
    (Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      RidesPast T (borderOf g)) ∧ ∀ fall, Accepted T fall (borderOf g) := by
  have hfew : CoinsFew Bk Z5 (slotsOf (script a.own)) := by
    have e := coinsFew_of_lent hlent
    rw [hP] at e
    exact e
  exact k5_owes_all_Q h R Rr hg Pl hx Hs hfit hb Kp Rd hans hidx hw hc hv hN HQ hL5 hfew hK hP hV

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.scalars_le
#print axioms ProofFile.Honest.K5.scalars_eq
#print axioms ProofFile.Honest.K5.closed_script
#print axioms ProofFile.Honest.K5.coins5_length
#print axioms ProofFile.Honest.K5.coins5_are
#print axioms ProofFile.Honest.K5.coinsFew_of_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_lent
