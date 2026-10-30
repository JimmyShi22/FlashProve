-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AtT.lean: THE PREMISES ON THE LETTERS OF A `Thread` T
(Honest/Thread/Thr.lean), AS ONE STRUCTURE, under which the debts of the member at an attention
segment's own rounds (kind K5) are stated WITH T A VARIABLE; and that the first chain's `Thread` at
the library's own letters (`thrAt`, Honest/K5/Law/Ready.lean) meets it.

Every field says what ONE LETTER of T is: by an equation, by an "if and only if", or (T.begun) by
an implication from it: at the border b := `borderOf g` in front of the member, at the border behind
it, or at the items of the member's row. No field speaks of a run, a state that is reached, or a
yes.

THREE OF T's LETTERS ARE TYPES (the items' `ι`, what is handed `P`, the witnesses' `Wt`). The
structure takes a map for each: it: the table's items as T's; pb: what is handed, read as the
instance's public part; wt: T's witness, read as the library's. At `thrAt` all three are the
identity.

  `asked7`, `owed6`   the items that the kind's row asks and owes, as the table writes them
  `K5AtT`            THE STRUCTURE
  `k5AtT_thrAt`      CONDITIONAL (g is below 12): `thrAt` meets the structure, by unfolding and the
                     two equations on its row (`asks_k5`, `owes_k5`, Honest/K5/Law/Exchange.lean)

WHAT THE STRUCTURE DOES NOT HOLD, because other named premises do: the member, the half in T.hs, and
T.ahead (`K5Seated`, Honest/K5/Law/Seated.lean) · T.keeps, T.rides at the border (Kp, Rd) · T.valid
(`IdnOwed`, Honest/K5/Law/IdnAt.lean) · T.fits (a test with code, which reads T.start, T.row, T.bs,
T.taken, T.fixed, T.near, T.ahead). NAMED IN NONE OF THESE: T.φ, T.chain, T.wit, T.strs, T.stored,
T.table. Other premises of this folder's laws name four of them: T.φ (hstop,
Honest/K5/Law/StepsLaid.lean), T.chain (hc: T.chain = 0), T.wit (`K5Script`,
Honest/K5/Law/Script.lean), T.strs (`K5RidersT`, Honest/K5/Law/RidersT.lean).

Limits. A definition: a premise's form; nothing is claimed of it. The hypothesis `P5J.AtMgA` stands
in its fields (the library's filling and numbers are made of it) and is not shown here. T is a
variable among the `Thread`s at the first chain's own types. At the library's full size and the
format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Exchange

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain First.Pub)
open VerifiableInference.Desc.First (Item onAt openSets pubSets start)
open VerifiableInference.Desc.Sound (mgBase mgAll)
open ProofFile.Honest.FirstThread (Script WtF honest noStrs)
open P5J (AtMgA mgAtAll TS CellsM)

/-- The seven items that the kind's row, read forward, asks at the segment number l. -/
def asked7 (l : Nat) : List Item :=
  [.constr l .idn, .worth l 2 "planes", .worth l 2 "keys", .worth l 2 "rider", .pin l 0, .pinW,
    .constr l .small]

/-- The six items that it owes. -/
def owed6 (l : Nat) : List Item :=
  [.formsT l 3 "own", .formsT l 2 "planes", .formsT l 2 "join", .pin l 0, .pinW, .constr l .small]

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}

/-- **THE STRUCTURE: WHAT IS SPENT OF T's LETTERS AT THE KIND's MEMBER OF GROUP g.** T: the
`Thread`, a variable. it, pb, wt: the three maps of the file's head. ans, test: the two letters of
the honest side's meaning. carryX, cq: the two fields in which the items' meaning leaves the
library's filling: the carried word's sentence; the stored table's decoder, the constant "the
input's cells". It is a definition: a premise's form. Nothing is claimed of it. -/
structure K5AtT
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (g : Nat) (it : Item → T.ι) (pb : T.P → ProofFile.InstPub) (wt : T.Wt → WtF)
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull) : Prop where
  /-- T.bs: the description's own flat list -/
  bs : T.bs = cF.blocksInOrder
  /-- T.ft: the label of the chain's first own tree -/
  ft : T.ft = 0
  /-- T.begun: the chain's first state is the description's, at the instance's public part -/
  begun : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp w.x.pub
  /-- T.handed: what is handed reads as the instance's public part -/
  handed : ∀ k w hd, pb (T.handed k w hd) = w.x.pub
  /-- T.form at the two borders: no mark of failure -/
  form : ∀ b, b = borderOf g ∨ b = borderOf g + 1 → ∀ a, T.form b a = a.2.failed.isNone
  /-- T.formP at the two borders: the table's promise there, at the honest letters over the
  library's filling, at the table's own open sets, at no strings -/
  formP : ∀ b, b = borderOf g ∨ b = borderOf g + 1 → ∀ a, T.formP b a ↔
    onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links P5J.At.ps[b]?
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD [])
      (((pubSets (honest (mgAtAll h) ans test).more P5J.At.links P5J.At.ps)[b]?).getD [])
      (pb a.1, a.2) noStrs
  /-- T.row at the border: what it asks and what it owes -/
  asks : (T.row (borderOf g)).asks = (asked7 (2 * g + 1)).map it
  owes : (T.row (borderOf g)).owes = (owed6 (2 * g + 1)).map it
  /-- T.means at the items of the row: the table's own sentence, at the honest letters over the
  library's filling with the two fields laid -/
  means : ∀ i, i ∈ asked7 (2 * g + 1) ∨ i ∈ owed6 (2 * g + 1) → ∀ w a y v,
    T.means w (it i) a y v ↔
      Item.holds (P5J.At.N Zp cF)
        (honest (mgAll { h.𝔇 with decT := fun _ _ => some (cq w), cr1 := carryX } mgBase) ans test)
        i (pb a.1, a.2) y (wt v)

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **THE FIRST CHAIN's `Thread` AT THE LIBRARY's OWN LETTERS MEETS THE STRUCTURE**, at the three
maps the identity. CONDITIONAL: g is below 12 (for the two equations on the row). The hypothesis h
stands in the letters. -/
theorem k5AtT_thrAt {g : Nat} (hg : g < 12) :
    K5AtT h (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) g
      (fun i => i) (fun p => p) (fun v => v) ans test carryX Q.cells :=
  { bs := rfl
    ft := rfl
    begun := fun _ _ _ _ e => e
    handed := fun _ _ _ => rfl
    form := fun _ _ _ => rfl
    formP := fun _ _ _ => Iff.rfl
    asks := by
      rw [asks_k5 h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg]
      exact (List.map_id' _).symm
    owes := by
      rw [owes_k5 h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg]
      exact (List.map_id' _).symm
    means := fun _ _ _ _ _ _ => Iff.rfl }

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5AtT_thrAt
