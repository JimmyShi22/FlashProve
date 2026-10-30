-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09Cap.lean: TWO LIGHT FIELDS OF A LINK's LIST OF DEBTS (`LinkOwes`,
Johnson/Desc/First/Link/Law/LinkOwes.lean) THAT HAD NO PAYING TERM, AT THE SEATED TERM: caller.hcap
("the batching's piece's error is the cap at 128") and numbers.hd (d ≤ 2 ^ 60); AND THE SEATED
PIECE's FIRST TREE AS THE TABLE's OWN COUNT, at every place but the last. Statements and proofs:
calls of `atRow_more` (Johnson/Desc/Kinds/Law/RowAtConst.lean) and of
`base_treesAt` (Johnson/Desc/Sound/PieceFence.lean), in the make of `k10_cap_at` and
`k10_base_at`, which speak at K10's places alone.

  `row_cap_at`: every piece of `h.row 𝔏` but the last has the cap of 128 bits a round as its error.
  `row_base_at`: its first tree is `(At.N Zp cF).treesAt At.ps[k]?`.
  `batch_lt`: the numbers of K9's five places of each of the 25 segments are not the last: the
kernel.
  `owesCaller_at`: **`OwesCaller (atRec qb b₁) (atRec qq b₂) (atRec qe b₃)`, WHOLE**, where qb is
the
    row's piece at a number that is not the last.
  `hd_pick`: numbers.hd AT THE PICK d := 2 ^ 60. d is the payer's to choose (the list binds it by
    "there is"); the other field that names it (hok: the runs' terms' exponents lie below d) is
    weakest at the greatest d that hd allows; the piece's error is the cap whatever d is.
  `low_at_row`: **so the closed test `lowAtB 𝔇.N q.base k` of the fifth tie IS the test at the
table's
    count**, the form in which it was evaluated (true at 100 of 100 places: a run, no theorem).
Limits. That the exponents lie below 2 ^ 60 is not shown here. No soundness statement.

-/
import Johnson.Desc.Kinds.Law.RowAtConst
import Johnson.Desc.Sound.PieceFence
import Johnson.Desc.First.BookFitTold
import Johnson.Desc.First.Link.Law.AtRecPays
import Johnson.Desc.First.Link.Law.FifthTieLow
import Johnson.IMR.EndFive
import Johnson.Desc.ProofFile.Law.KindPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S bookFit bookFit_withTold)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (OwesCaller caller_atRec atRec batchIx lowAtB plF)
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more atRow_blocks atRow_told)
open _root_.Run (ckP)
open _root_.Iop (Err)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Every piece of the row but the last has the cap as its error.** -/
theorem row_cap_at (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ) (hk : k + 1 < cF.blocksInOrder.length) :
    ∀ q, (h.row 𝔏)[k]? = some q → q.err = Err.cap 128 (uLT (ckP .two) q.ds) :=
  fun q hq => (atRow_more h 𝔏 q₁ q₂ q₃ k q hq hk).2

/-- **Its first tree is the table's own count at the place.** -/
theorem row_base_at (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ) (hk : k + 1 < cF.blocksInOrder.length)
    (hp : k ≤ At.ps.length) :
    ∀ q, (h.row 𝔏)[k]? = some q → q.base = (At.N Zp cF).treesAt At.ps[k]? := by
  intro q hq
  have hM := (atRow_more h 𝔏 q₁ q₂ q₃ k q hq hk).1
  have hfit : bookFit (At.N Zp cF) At.ps (toldOf (cF.blocksInOrder.map (held (P := ProofFile.InstPub)))) =
      true := by
    rw [atRow_told]
    exact bookFit_withTold _ At.ps (toldOf cF.blocksInOrder) (ProofFile.Law.flatPlaces_nodup fullLinks true)
  exact base_treesAt hM (atRow_blocks h) (At.N Zp cF) At.ps hfit hp

set_option maxRecDepth 100000 in
/-- K9's five places of each segment are not the last of 358. -/
theorem batch_lt : ∀ m, m < 25 → batchIx m + 4 + 1 < 358 := by decide

/-- **`OwesCaller`, WHOLE, AT THE CARRIAGE's PIECES OVER THE SEATED ROW.** -/
theorem owesCaller_at (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ) (hk : k + 1 < cF.blocksInOrder.length)
    (b₁ b₂ b₃ : Block S ProofFile.Cl) (qb qq qe) (hb : (h.row 𝔏)[k]? = some qb)
    (_ : (h.row 𝔏)[k + 1]? = some qq) (_ : (h.row 𝔏)[k + 1 + 1]? = some qe) :
    OwesCaller (atRec qb b₁) (atRec qq b₂) (atRec qe b₃) :=
  caller_atRec b₁ b₂ b₃ qb qq qe (row_cap_at h 𝔏 q₁ q₂ q₃ k hk qb hb)

/-- numbers.hd at the pick. -/
theorem hd_pick : (2 : ℕ) ^ 60 ≤ 2 ^ 60 := le_rfl

/-- **The fifth tie's closed test at the piece's first tree is the test at the table's count.** -/
theorem low_at_row (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ) (hk : k + 1 < cF.blocksInOrder.length)
    (hp : k ≤ At.ps.length) (q) (hq : (h.row 𝔏)[k]? = some q)
    (T : lowAtB (At.N Zp cF) ((At.N Zp cF).treesAt At.ps[k]?) k = true) :
    lowAtB (At.N Zp cF) q.base k = true := by
  rw [row_base_at h 𝔏 q₁ q₂ q₃ k hk hp q hq]
  exact T

end P5J

#print axioms P5J.row_cap_at
#print axioms P5J.row_base_at
#print axioms P5J.owesCaller_at
#print axioms P5J.low_at_row
