-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortNumbers.lean: THE FIELD Anumbers OF WHAT IS LEFT OF A LINK's LAW
(`CoreRest2`, LinkRestAtSort2.lean; `CoreLeft`): `OwesNumbers` AT THE SORT's CHOSEN
LETTERS AND AT d := p.rows, BROUGHT DOWN TO FOUR NAMED CLAUSES ON THE FIXED PART (`NumbersOk`), ONE
CLOSED NUMBER AND THE LOOKUP ARGUMENT's ENTRIES' DUTY. A structure of sentences, and theorems:
assemblies.

WHY: A GAP IN THE NAMED Ok, FOUND BY HOLDING THE FIELD's ONLY PAYERS AGAINST THE LETTERS.
numbers_layers, numbers_attention, numbers_head (LinkLawAt.lean) take, at every state s with
the book-keeping in front of the batching (k9OnA s) and Ok (fixed9 φ s), the structure EqTake
(ExpsAt.lean): six fields. Of these the named Ok with rowsFit gives three: "a snapshot is there"
(the core's clause snap), "the smallness test's record is there" (there), and the second number
(planClaimsF + top8 ≤ d + 1: that is what rowsFit says, at d := p.rows). The rest has no clause: it
is gathered here, by name.

`NumbersOk len q`: FOUR CLAUSES.
  funs: the stated functions are there.
  heard: what the digits' lookup returned is there (without it the four values are none, not four).
  hmS: the symbols' arrays have the rows that their sizes ask ("Fits" speaks of m and k, not of mS).
  hlen: THE FIRST NUMBER: the runs' claims, len q of them, are at most the plan's number. BY A
    SEARCH NO THEOREM ENDS IN IT; IT CAN BE FALSE.

What is said.
  `eqTake_of`: EqTake at tm4 := tmFour and d := rows, from the core, NumbersOk and rowsFit.
  `numbers_layers3`, `numbers_att3`, `numbers_head3`: **the field Anumbers, at Ok := fun q => (‹the
    named Ok› q ∧ Kx q) ∧ rowsFit p.rows pi8 q and d := p.rows**, from: hd : p.rows ≤ 2 ^ 60 · hK :
    Kx q gives NumbersOk at the link's own runs' lengths · hP : PlainE at the lookup's entries.

WHAT FOLLOWS. Kx (a free letter in LinkRestAtSort3 | 4) must hold NumbersOk beside K3's promise: so
Aready owes it too, at what is fixed in front of the batching.

Limits. BOOK-KEEPING. NOTHING IS SHOWN OF ANY STATE. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSort2
import Johnson.Desc.First.Link.Law.LinkLawAt
import Johnson.Desc.First.Batch.Law.K8All

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

/-- **WHAT THE NUMBERS ASK OF THE FIXED PART BESIDE THE NAMED Ok.** -/
structure NumbersOk (len : Q β → ℕ) (q : Q β) : Prop where
  /-- the stated functions are there -/
  funs : ((pi8 q.1).2).isSome = true
  /-- what the digits' lookup returned is there -/
  heard : ∀ tlb, (pi8 q.1).1 = some tlb → tlb.heard.isSome = true
  /-- the symbols' arrays have the rows that their sizes ask -/
  hmS : ∀ tlb, (pi8 q.1).1 = some tlb → ∀ mu, mu < tlb.NM →
    (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m
  /-- the runs' claims are at most the plan's number -/
  hlen : ∀ v, q.2 = some v → len q ≤ v.F.planClaimsF

/-- EqTake from the core, NumbersOk and rowsFit. -/
theorem eqTake_of {nU : Array ℕ} {tlD : HTailF2} {q : Q β} {len : Q β → ℕ} {rows : ℕ}
    (C : OkCore nU tlD q) (N : NumbersOk len q) (R : rowsFit rows pi8 q) :
    ∃ tlb funs v, ∀ y, EqTake tmFour q y (len q) rows tlb funs v := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 C.snap
  obtain ⟨tlb, ht⟩ := Option.isSome_iff_exists.1 C.there
  obtain ⟨funs, hf⟩ := Option.isSome_iff_exists.1 N.funs
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 (N.heard tlb ht)
  have h1 : pi8 q.1 = (some tlb, some funs) := Prod.ext ht hf
  exact ⟨tlb, funs, v, fun y => ⟨h1, hv, N.hmS tlb ht,
    ⟨vals4 pi8 (ent4 pi8) q y, vals4_length pi8 _ q y tlb v g ht hv hg, fun _ => rfl⟩,
    N.hlen v hv, Nat.le_succ_of_le (R v tlb funs hv h1)⟩⟩

/-- **Anumbers AT A LAYERS' LINK, AT d := p.rows.** -/
theorem numbers_layers3 {m : ℕ} {L : Link S Claim} (hL : SegAt m .layers L) (u : HTailF2)
    (ψ : S → β) (p4 : OnBytes.Desc.First.K4.Par)
    (nU : Array ℕ) (tlD : HTailF2) (Kx : Q β → Prop)
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (p : Where) (hd : p.rows ≤ 2 ^ 60)
    (hK : ∀ q, Kx q → NumbersOk (fun q => lenRuns q (rlOf L (tmL p4 entUnit tmFour t3) (lenL p4
      l3))) q)
    (hP : ∀ s y, (k9OnA s = true ∧ (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsFit
      p.rows pi8) q) (fixed9 (phiAll u ψ) s)) → ∀ o ∈ [(1, "objects"), (6, "objects")], PlainE (tmL
      p4 entUnit tmFour t3) (lenL p4 l3) (fixed9 (phiAll u ψ) s) y o) :
    OwesNumbers L (phiAll u ψ) (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows
      pi8) q) (tmL p4 entUnit tmFour t3) (lenL p4 l3) p.rows :=
  numbers_layers hL u ψ _ p4 entUnit tmFour t3 l3 p.rows hd fun s hs => by
    obtain ⟨tlb, funs, v, E⟩ := eqTake_of hs.2.1.1.core (hK _ hs.2.1.2) hs.2.2
    exact ⟨tlb, funs, v, fun y => ⟨E y, hP s y hs⟩⟩

/-- **Anumbers AT AN ATTENTION LINK, AT d := p.rows.** -/
theorem numbers_att3 {m : ℕ} {L : Link S Claim} (hL : SegAt m .attention L) (u : HTailF2)
    (ψ : S → β) (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (nU : Array ℕ) (tlD : HTailF2) (Kx : Q β → Prop)
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (p : Where) (hd : p.rows ≤ 2 ^ 60)
    (hK : ∀ q, Kx q → NumbersOk (fun q => lenRuns q (rlOf L (tmA rd c entUnit tmFour t3) (lenA rd c
      l3))) q)
    (hP : ∀ s y, (k9OnA s = true ∧ (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧ (rowsFit
      p.rows pi8) q) (fixed9 (phiAll u ψ) s)) → ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"),
      (6, "objects")], PlainE (tmA rd c entUnit tmFour t3) (lenA rd c l3) (fixed9 (phiAll u ψ) s) y
      o) :
    OwesNumbers L (phiAll u ψ) (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows
      pi8) q) (tmA rd c entUnit tmFour t3) (lenA rd c l3) p.rows :=
  numbers_attention hL u ψ _ rd c entUnit tmFour t3 l3 p.rows hd fun s hs => by
    obtain ⟨tlb, funs, v, E⟩ := eqTake_of hs.2.1.1.core (hK _ hs.2.1.2) hs.2.2
    exact ⟨tlb, funs, v, fun y => ⟨E y, hP s y hs⟩⟩

/-- **Anumbers AT THE HEAD's LINK, AT d := p.rows.** -/
theorem numbers_head3 {m : ℕ} {L : Link S Claim} (hL : SegAt m .head L) (u : HTailF2)
    (ψ : S → β) (hS : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (nU : Array ℕ) (tlD : HTailF2) (Kx : Q β → Prop)
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (p : Where) (hd : p.rows ≤ 2 ^ 60)
    (hK : ∀ q, Kx q → NumbersOk (fun q => lenRuns q (rlOf L (tmH hS iU3 p6 kap entUnit tmFour t3)
      (lenH
      hS iU3 p6 kap l3))) q)
    (hP : ∀ s y, (k9OnA s = true ∧ (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q ∧
      (rowsFit p.rows pi8) q) (fixed9 (phiAll u ψ) s)) → ∀ o ∈ [(2, "objects"), (2, "planes"), (7,
      "objects")], PlainE (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) (fixed9
      (phiAll u ψ) s) y o) :
    OwesNumbers L (phiAll u ψ) (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q ∧
      (rowsFit p.rows pi8) q) (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) p.rows
      :=
  numbers_head hL u ψ _ hS iU3 p6 kap entUnit tmFour t3 l3 p.rows hd fun s hs => by
    obtain ⟨tlb, funs, v, E⟩ := eqTake_of hs.2.1.1.core (hK _ hs.2.1.2) hs.2.2
    exact ⟨tlb, funs, v, fun y => ⟨E y, hP s y hs⟩⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.eqTake_of
#print axioms VerifiableInference.Desc.LinkJoin.numbers_layers3
#print axioms VerifiableInference.Desc.LinkJoin.numbers_att3
#print axioms VerifiableInference.Desc.LinkJoin.numbers_head3
