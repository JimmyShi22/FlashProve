-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FourOfTable.lean: THE CLAUSES «four» AND «ents4» OF A LINK's Ok AT A STATE THAT IS REACHED IN FRONT OF THE BATCHING AND AT WHICH THE TABLE's PROMISE HOLDS, AT ALL 25 LINKS: FourOfPromise.lean's
PREMISE hB (beside this file) DRAWN FROM THE PROMISE, BY LEAN. A closed fact by the kernel with a negative line, and a theorem: a join.

Why. FourOfPromise.lean asks hB: at the state in front of the batching a ledger is open and has its sizes. Its page said that the table's promise says so there. That was a citation. Here the terms are composed.

What is said.
  `frontAt l`: the number in the full list of the place in front of which link l's batching stands: 14 l + 9; at the head's link 347.
  `frontB`, `front_full` [BY THE KERNEL]: at each l < 25 the place at that number is of link l and its piece's number is hearN fullList l + 1. `front_off`: one number further it is so at no link.
  `ledger_at_front`: so the promise at that number gives: a ledger is open and `Sized` (`ledger_of_promise`, LedgerAsked.lean; `ledgerOk_iff`, SizedRides.lean).
  `four_of_table`: **l < 25 · in scope · IM.Open · hp · a.1 reached at frontAt l · the promise `onT Nm (mgAll 𝔇 mgBase) fullList (flatPlacesOf fullList true) (fun s => (z, s)) (frontAt l) a` ⊢ `OkCore`'s clauses four and
    ents4, to the letter, at `fixed9 φ a.1`.**

Limits. The promise and «reached» are premises. At the composed meaning mgAll 𝔇 mgBase and the full list. The premises are not shown to be satisfiable. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FourOfPromise
import Johnson.Desc.First.Link.Law.LedgerAsked

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The number of the place in front of which link l's batching stands. -/
def frontAt (l : ℕ) : ℕ := if l = 24 then 347 else 14 * l + 9

/-- The place at number k l is of link l, and it is the batching's. -/
def frontB (k : ℕ → ℕ) (l : ℕ) : Bool :=
  ((flatPlacesOf fullList true)[k l]?).any fun p =>
    p.link == some l && p.piece == hearN fullList l + 1

set_option maxRecDepth 1000000 in
/-- **(W) At all 25 links.** -/
theorem front_full : (List.range 25).all (frontB frontAt) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** One number further: at no link. -/
theorem front_off : (List.range 25).any (frontB fun l => frontAt l + 1) = false := by
  decide +kernel

variable {F : Frame} {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **THE PROMISE IN FRONT OF A BATCHING GIVES hB.** -/
theorem ledger_at_front (Nm : Numbers) (z : P) {l : ℕ} (hl : l < 25) (a : S × F.E.Str)
    (ha : onT Nm (mgAll 𝔇 mgBase) fullList (flatPlacesOf fullList true) (fun s : S => (z, s))
      (frontAt l) a) : ∃ G', a.1.fork? = some G' ∧ Sized G' := by
  have h := List.all_eq_true.1 front_full l (List.mem_range.2 hl)
  unfold frontB at h
  cases hp : (flatPlacesOf fullList true)[frontAt l]? with
  | none =>
    rw [hp] at h
    exact nomatch h
  | some p =>
    rw [hp] at h
    have hq : (p.link == some l && p.piece == hearN fullList l + 1) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    exact (ledgerOk_iff a.1).1 (ledger_of_promise 𝔇 Nm fullList (flatPlacesOf fullList true) z
      (frontAt l) l 1 p ledFit_full hp hq.1 hq.2 (Or.inl rfl) a ha)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Fd : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **four AND ents4 FROM «REACHED» AND THE TABLE's PROMISE, AT ALL 25 LINKS.** -/
theorem four_of_table (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL Fd Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {q : Q} (a : S × F.E.Str)
    (h : Reach 0 c.blocksInOrder start (frontAt l) (q, a.1)) (Nm : Numbers) (z : P)
    (ha : onT Nm (mgAll 𝔇 mgBase) fullList (flatPlacesOf fullList true) (fun s : S => (z, s))
      (frontAt l) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    (∀ v tlb g, (fixed9 φ a.1).2 = some v → (π (fixed9 φ a.1).1).1 = some tlb →
      tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1) ∧
      ∀ tlb g, (π (fixed9 φ a.1).1).1 = some tlb → tlb.heard = some g →
        ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row := by
  have hB := ledger_at_front 𝔇 Nm z hl a ha
  by_cases h24 : l = 24
  · subst h24
    exact four_of_promise_head hS hR O hp (z := q) h hB π φ u hπ
  · have e : frontAt l = 14 * l + 9 := if_neg h24
    rw [e] at h
    exact four_of_promise hS hR O hp (by omega : l < 24) (z := q) h hB π φ u hπ

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.front_full
#print axioms VerifiableInference.Desc.LinkJoin.front_off
#print axioms VerifiableInference.Desc.LinkJoin.ledger_at_front
#print axioms VerifiableInference.Desc.LinkJoin.four_of_table
