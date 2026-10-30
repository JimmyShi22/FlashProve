-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortNumbersC.lean: THE FIELD Anumbers (`OwesNumbers`) OF A LINK's LAW
AT THE SORT's LETTERS AND d := p.rows, ON THE SECOND ROAD: THE CLAUSE hlen ("the runs' claims are
at most the plan's number") IS DRAWN FROM THE PUBLIC SENTENCE C' := `rowsLen`
(Batch/Law/RowsLen.lean: rowsFit and lenFit), NOT FROM THE LETTER Kx. A structure of sentences, and
theorems: assemblies. Beside SortNumbers.lean, which stands as it is.
The sentence stands by its one name.

Why. On the first road (SortNumbers.lean) all four clauses that the numbers ask beside the named Ok
stand in Kx, and so are owed at every reached state in front of the batching (the field Aready);
the fourth, hlen, comes down there to facts on the maker's plans that the head pins nowhere. On the
second road hlen is proved from the batching's own yes (Batch/Law/LenOfYes.lean: len_hR1_link) as a
half of the public sentence that inMoves_rows takes out of the promise. THE BARE PROMISE MUST THEN
NOT HOLD hlen, else the proof is a circle: so Kx holds three clauses alone.

What is said.
  `NumbersThree q`: NumbersOk less hlen: funs, heard, hmS, in the same texts.
  `numbersOk_of`: NumbersOk len q from NumbersThree q and lenFit len q (lenFit is hlen's text).
  `numbers_layersC`, `numbers_attC`, `numbers_headC`: **OwesNumbers at the promise fun q => (‹the
    named Ok› q ∧ Kx q) ∧ rowsLen p.rows pi8 (the link's own runs' number) q**, from hd : p.rows ≤
    2 ^ 60 · hK : Kx q gives NumbersThree q · hP : PlainE at the lookup's entries.

Limits. BOOK-KEEPING. NOTHING IS SHOWN OF ANY STATE. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortNumbers
import Johnson.Desc.First.Batch.Law.RowsLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {β : Type}

/-- **NumbersOk LESS hlen.** -/
structure NumbersThree (q : Q β) : Prop where
  /-- the stated functions are there -/
  funs : ((pi8 q.1).2).isSome = true
  /-- what the digits' lookup returned is there -/
  heard : ∀ tlb, (pi8 q.1).1 = some tlb → tlb.heard.isSome = true
  /-- the symbols' arrays have the rows that their sizes ask -/
  hmS : ∀ tlb, (pi8 q.1).1 = some tlb → ∀ mu, mu < tlb.NM →
    (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m

/-- The four from the three and the public sentence. -/
theorem numbersOk_of {len : Q β → ℕ} {q : Q β} (N : NumbersThree q) (h : lenFit len q) :
    NumbersOk len q :=
  ⟨N.funs, N.heard, N.hmS, h⟩

/-- **Anumbers AT A LAYERS' LINK, WITH hlen OUT OF THE PUBLIC SENTENCE.** -/
theorem numbers_layersC {m : ℕ} {L : Link S Claim} (hL : SegAt m .layers L) (u : HTailF2)
    (ψ : S → β) (p4 : OnBytes.Desc.First.K4.Par)
    (nU : Array ℕ) (tlD : HTailF2) (Kx : Q β → Prop)
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (p : Where) (hd : p.rows ≤ 2 ^ 60) (hK : ∀ q, Kx q → NumbersThree q)
    (hP : ∀ s y, (k9OnA s = true ∧ (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsLen
      p.rows pi8 (fun q => lenRuns q (rlOf L (tmL p4 entUnit tmFour t3) (lenL p4 l3)))) q) (fixed9
      (phiAll u ψ) s)) → ∀ o ∈ [(1, "objects"), (6, "objects")], PlainE (tmL p4 entUnit tmFour t3)
      (lenL p4 l3) (fixed9 (phiAll u ψ) s) y o) :
    OwesNumbers L (phiAll u ψ) (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsLen p.rows
      pi8 (fun q => lenRuns q (rlOf L (tmL p4 entUnit tmFour t3) (lenL p4 l3)))) q) (tmL p4 entUnit
      tmFour t3) (lenL p4 l3) p.rows :=
  numbers_layers hL u ψ _ p4 entUnit tmFour t3 l3 p.rows hd fun s hs => by
    obtain ⟨tlb, funs, v, E⟩ := eqTake_of hs.2.1.1.core
      (numbersOk_of (hK _ hs.2.1.2) (rowsLen_len hs.2.2)) (rowsLen_rows hs.2.2)
    exact ⟨tlb, funs, v, fun y => ⟨E y, hP s y hs⟩⟩

/-- **Anumbers AT AN ATTENTION LINK, WITH hlen OUT OF THE PUBLIC SENTENCE.** -/
theorem numbers_attC {m : ℕ} {L : Link S Claim} (hL : SegAt m .attention L) (u : HTailF2)
    (ψ : S → β) (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (nU : Array ℕ) (tlD : HTailF2) (Kx : Q β → Prop)
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (p : Where) (hd : p.rows ≤ 2 ^ 60) (hK : ∀ q, Kx q → NumbersThree q)
    (hP : ∀ s y, (k9OnA s = true ∧ (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧ (rowsLen
      p.rows pi8 (fun q => lenRuns q (rlOf L (tmA rd c entUnit tmFour t3) (lenA rd c l3)))) q)
      (fixed9 (phiAll u ψ) s)) → ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")],
      PlainE (tmA rd c entUnit tmFour t3) (lenA rd c l3) (fixed9 (phiAll u ψ) s) y o) :
    OwesNumbers L (phiAll u ψ) (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧ (rowsLen p.rows
      pi8 (fun q => lenRuns q (rlOf L (tmA rd c entUnit tmFour t3) (lenA rd c l3)))) q) (tmA rd c
      entUnit tmFour t3) (lenA rd c l3) p.rows :=
  numbers_attention hL u ψ _ rd c entUnit tmFour t3 l3 p.rows hd fun s hs => by
    obtain ⟨tlb, funs, v, E⟩ := eqTake_of hs.2.1.1.core
      (numbersOk_of (hK _ hs.2.1.2) (rowsLen_len hs.2.2)) (rowsLen_rows hs.2.2)
    exact ⟨tlb, funs, v, fun y => ⟨E y, hP s y hs⟩⟩

/-- **Anumbers AT THE HEAD's LINK, WITH hlen OUT OF THE PUBLIC SENTENCE.** -/
theorem numbers_headC {m : ℕ} {L : Link S Claim} (hL : SegAt m .head L) (u : HTailF2)
    (ψ : S → β) (hS : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (nU : Array ℕ) (tlD : HTailF2) (Kx : Q β → Prop)
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (p : Where) (hd : p.rows ≤ 2 ^ 60) (hK : ∀ q, Kx q → NumbersThree q)
    (hP : ∀ s y, (k9OnA s = true ∧ (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q ∧
      (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf L (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS
      iU3 p6 kap l3)))) q) (fixed9 (phiAll u ψ) s)) → ∀ o ∈ [(2, "objects"), (2, "planes"), (7,
      "objects")], PlainE (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) (fixed9
      (phiAll u ψ) s) y o) :
    OwesNumbers L (phiAll u ψ) (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q ∧
      (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf L (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS
      iU3 p6 kap l3)))) q) (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) p.rows :=
  numbers_head hL u ψ _ hS iU3 p6 kap entUnit tmFour t3 l3 p.rows hd fun s hs => by
    obtain ⟨tlb, funs, v, E⟩ := eqTake_of hs.2.1.1.core
      (numbersOk_of (hK _ hs.2.1.2) (rowsLen_len hs.2.2)) (rowsLen_rows hs.2.2)
    exact ⟨tlb, funs, v, fun y => ⟨E y, hP s y hs⟩⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.numbersOk_of
#print axioms VerifiableInference.Desc.LinkJoin.numbers_layersC
#print axioms VerifiableInference.Desc.LinkJoin.numbers_attC
#print axioms VerifiableInference.Desc.LinkJoin.numbers_headC
