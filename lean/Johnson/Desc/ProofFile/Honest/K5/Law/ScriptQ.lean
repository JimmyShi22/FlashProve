-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ScriptQ.lean: CONDITIONAL: WHAT THE HONEST SIDE OF AN ATTENTION
SEGMENT's OWN ROUNDS (kind K5) SPENDS OF THE SCRIPT (Script, Honest/Thread/First.lean), AS EQUATIONS
ON THE SCRIPT ALONE; and the ties at a stand (K5Script, PlanesTie, Honest/K5/Law/Script.lean) out of
them. Definitions of propositions, and statements with their proofs. The thread T is a variable.

  coins5         the coins that the book lends K5's row: of the book and a run's coins alone
  K5ScriptQ      **two equations on Q, cells, the book and the head's public letters**: eMask: at
                 the address of mask entry number ν₅ + j the witness's messages hold coin number j;
                 eCells: inside every matrix but the lookup's planes' they hold the trace's cell
  K5PlanesQ      the like inside the matrix of the lookup's planes: apart
  LedgerIs       at the border in front the ledger's next free slot is ν₅
  AddrAt         at every stand of that border, at every witness: the library's tie of the two
                 readings by address (AddrTie, Johnson/Desc/First/Att/K05DataMats.lean)
  Names5         the forms at which AddrAt is asked name each slot under which a coin lies
  parts_count    the row has as many parts as there are shapes
  k5Script_of_Q  **K5ScriptQ, LedgerIs, AddrAt, Names5 and the third field's text give K5Script**
  planesTie_of_Q K5PlanesQ and AddrAt give PlanesTie

NONE OF THE FORMS IS SHOWN HERE, AND NOTHING SHOWS THAT THEY CAN BE MET. What is shown: premises at
a stand follow from premises on the Script, by the library's own road (AddrTie; matsOfData_eq) and
the frame's law on what a row spends (spentOf_row, Honest/Law/Rule/Spent.lean).

Limits. The library's full size and head alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.TiesFit
import Johnson.Desc.ProofFile.Honest.K5.Law.Plays
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.First.Att.K05DataMats
import Johnson.Desc.First.Att.Door.Law.K5RestMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT dataQ seatTab matsOfData)
open VerifiableInference.Desc.First.Look (sigListCalls seatCalls valAt)
open VerifiableInference.Desc.First.Att.P (K3Pts AddrTie matsOfMsg matsOfData_eq)
open VerifiableInference.OnPublicFiles (attMs)
open H2K5.Door (seatAll)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

variable {Z₀ : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z₀ D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- The coins that the book lends K5's row, as a function of the book and a run's coins alone. -/
def coins5 (Bk : ProverCoinCounts) (k : Coins Bk) (Z : Seat5) : List E :=
  rowSpent Bk (k.look 0) Z.place (H2K5.Honest.shapes Z.P.x).length 0

/-- **WHAT K5 SPENDS OF THE SCRIPT: TWO EQUATIONS ON Q, cells, THE BOOK AND PUBLIC LETTERS ALONE.**
Vd: which inputs are spoken of. N: how many challenges must have been heard. x₁: the place of the
segment's lookup on the calls. A: the group's plan. ν₅: the number of K5's first scalar in the
segment. No state, no thread, no part. The two guards (Vd v; N challenges heard) stand in both
equations: they make the premise weaker; at eMask neither is expected to be needed by whoever shows
it. It is a definition: a premise's form. -/
structure K5ScriptQ (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat)
    (x₁ : VerifiableInference.Desc.First.Look.Place) (A : OnBytes.Attention.Plan)
    (cells : Tr → Cells) (Z : Seat5) (ν₅ : Nat) : Prop where
  /-- at the address of the mask entry number ν₅ + j the witness's messages hold coin number j -/
  eMask : ∀ k v hd, Vd v → N ≤ hd.length → ∀ j, j < (coins5 Bk k Z).length →
    (valAt h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link)
      (seatCalls h.𝔇.sent x₁.link)
      (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr (Q.wit k v hd))
      (.mask (ν₅ + j))).getD 0 = Reading.gl.val ((coins5 Bk k Z).getD j zeroE)
  /-- inside every matrix but the lookup's planes' the witness's messages hold the trace's cell -/
  eCells : ∀ k v hd, Vd v → N ≤ hd.length → ∀ i r c, i ≠ Z.P.S.cf.NAs + 2 →
    r < (A.seam.tl.mats.getD i {}).m → c < (A.seam.tl.mats.getD i {}).k →
    matsOfMsg x₁ A.seam.tl h.𝔇.sent h.𝔇.l3.rad
        (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr (Q.wit k v hd)) i r c =
      Reading.gl.val (cellAt Z.P.S Z.link (cells v.trace) i r c)

/-- The like inside the matrix of the lookup's planes: apart. -/
def K5PlanesQ (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat)
    (x₁ : VerifiableInference.Desc.First.Look.Place) (A : OnBytes.Attention.Plan)
    (cells : Tr → Cells) (Z : Seat5) : Prop :=
  ∀ k v hd, Vd v → N ≤ hd.length → ∀ r c,
    r < (A.seam.tl.mats.getD (Z.P.S.cf.NAs + 2) {}).m →
    c < (A.seam.tl.mats.getD (Z.P.S.cf.NAs + 2) {}).k →
    matsOfMsg x₁ A.seam.tl h.𝔇.sent h.𝔇.l3.rad
        (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr (Q.wit k v hd))
        (Z.P.S.cf.NAs + 2) r c =
      Reading.gl.val (cellAt Z.P.S Z.link (cells v.trace) (Z.P.S.cf.NAs + 2) r c)

variable (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb)
  (b : Nat)

/-- At the border in front the ledger's next free slot is ν₅. A premise's form. -/
def LedgerIs (ν₅ : Nat) : Prop :=
  ∀ k s m E, Thr T b k s m E → ∀ a, segAt? s = some a → a.F.next = ν₅

/-- At every stand of the border in front, at every witness: the library's tie of the two readings
by address (AddrTie), at the forms fs. A premise's form. -/
def AddrAt (x₁ : VerifiableInference.Desc.First.Look.Place) (A : OnBytes.Attention.Plan)
    (own : List (Nat × Nat)) (fs : List Aff) : Prop :=
  ∀ k s m E, Thr T b k s m E → ∀ a, segAt? s = some a → ∀ w : WtF,
    AddrTie x₁ A.seam.tl h.𝔇.sent h.𝔇.l3.rad ((s.link?.map (·.arrayOf)).getD #[])
      (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr w)
      (dataQ own a (seatTab h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms w)) fs

/-- The forms fs name each slot under which a coin of the row lies. A premise's form. -/
def Names5 (Bk : ProverCoinCounts) (Z : Seat5) (ν₅ : Nat) (fs : List Aff) : Prop :=
  ∀ (k : Coins Bk) j, j < (coins5 Bk k Z).length → ∃ f ∈ fs, ∃ y ∈ f.slots.toList, y.1 = ν₅ + j

variable {h Q T b}

/-- The row has as many parts as there are shapes. No premise. -/
theorem parts_count (cells : Tr → Cells) (Z : Seat5) :
    (k5Half (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells Z).parts.length =
      (H2K5.Honest.shapes Z.P.x).length := by
  have e := congrArg List.length
    (half_cut (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells Z)
  rw [List.length_map] at e
  rw [e]
  exact List.length_map _

/-- At a stand of the border, at every continuation, N challenges have been heard. -/
theorem heard_enough {N : Nat} (hN : N ≤ T.front + roundsTo T.bs b) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr T b k s m E)
    (ds : List Fmt.Drawn) : N ≤ (m.st.heard ++ ds).length := by
  rw [List.length_append, T.heard_length hT.2.1]
  omega

/-- **K5Script from the two equations on Q.** wt: the reading of the thread's witness as the
library's. CONDITIONAL: on every form that it names; none is shown. -/
theorem k5Script_of_Q {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {A : OnBytes.Attention.Plan}
    {cells : Tr → Cells} {Z : Seat5} {ν₅ : Nat} {own : List (Nat × Nat)} {fs : List Aff}
    {blk : Block TS ProofFile.Cl} (wt : T.Wt → WtF)
    (hw : ∀ k v hd, wt (T.wit k v hd) = Q.wit k v hd) (hc : T.chain = 0)
    (hv : ∀ v, T.valid v → Vd v) (hN : N ≤ T.front + roundsTo T.bs b)
    (HQ : K5ScriptQ h Q Vd N x₁ A cells Z ν₅) (hL : LedgerIs T b ν₅)
    (hA : AddrAt h T b x₁ A own fs) (hn : Names5 Bk Z ν₅ fs)
    (hK : ∀ k s m E, Thr T b k s m E → ∀ att, s.here = .att att →
      ∃ g, att.g = some g ∧ K3Pts A.fs g.zx g.zy g.zk (OnBytes.Slice.readV (g.zx ++ g.zy)) ∧
        ∀ ds n, drawsFit blk.rounds ds = true → Z.keyAt (m.st.heard ++ ds.take n) = g.zk) :
    K5Script T b cells Z A blk own (fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v)) := by
  refine ⟨?_, ?_, hK⟩
  · intro k s m E hT a c ha hl ds j hj
    have e1 : K5.spentOf _ c = coins5 Bk k Z := by
      rw [spent_same, spentOf_row Bk _ _ _ _ _ c hl, hc, parts_count]
      rfl
    rw [e1] at hj ⊢
    obtain ⟨f, hf, y, hy, ey⟩ := hn k j hj
    have t := (hA k s m E hT a ha (Q.wit k m.st.input (m.st.heard ++ ds))).mask f hf y hy
    rw [ey] at t
    show (dataQ own a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
      (wt (T.wit k m.st.input (m.st.heard ++ ds))))).mask (a.F.next + j) = _
    rw [hw, hL k s m E hT a ha]
    exact t.symm.trans
      (HQ.eMask k _ _ (hv _ hT.2.2.2.2.2.2) (heard_enough hN hT ds) j hj)
  · intro k s m E hT a ha ds i r c h1 h2 h3
    have e := matsOfData_eq x₁ A.seam.tl h.𝔇.sent h.𝔇.l3.rad
      (hA k s m E hT a ha (Q.wit k m.st.input (m.st.heard ++ ds)))
    show _ = matsOfData A.seam.tl _ (dataQ own a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
      (wt (T.wit k m.st.input (m.st.heard ++ ds))))) i r c
    rw [hw]
    exact (HQ.eCells k _ _ (hv _ hT.2.2.2.2.2.2) (heard_enough hN hT ds) i r c h1 h2 h3).symm.trans
      (congrFun (congrFun (congrFun e i) r) c)

/-- **PlanesTie from the third equation.** CONDITIONAL: on the two forms that it names. -/
theorem planesTie_of_Q {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {A : OnBytes.Attention.Plan}
    {cells : Tr → Cells} {Z : Seat5} {own : List (Nat × Nat)} {fs : List Aff} (wt : T.Wt → WtF)
    (hw : ∀ k v hd, wt (T.wit k v hd) = Q.wit k v hd) (hv : ∀ v, T.valid v → Vd v)
    (hN : N ≤ T.front + roundsTo T.bs b) (HP : K5PlanesQ h Q Vd N x₁ A cells Z)
    (hA : AddrAt h T b x₁ A own fs) :
    PlanesTie T b cells Z A own (fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v)) := by
  intro k s m E hT a ha ds r c h1 h2
  have e := matsOfData_eq x₁ A.seam.tl h.𝔇.sent h.𝔇.l3.rad
    (hA k s m E hT a ha (Q.wit k m.st.input (m.st.heard ++ ds)))
  show _ = matsOfData A.seam.tl _ (dataQ own a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
    (wt (T.wit k m.st.input (m.st.heard ++ ds))))) (Z.P.S.cf.NAs + 2) r c
  rw [hw]
  exact (HP k _ _ (hv _ hT.2.2.2.2.2.2) (heard_enough hN hT ds) r c h1 h2).symm.trans
    (congrFun (congrFun (congrFun e (Z.P.S.cf.NAs + 2)) r) c)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.parts_count
#print axioms ProofFile.Honest.K5.heard_enough
#print axioms ProofFile.Honest.K5.k5Script_of_Q
#print axioms ProofFile.Honest.K5.planesTie_of_Q
