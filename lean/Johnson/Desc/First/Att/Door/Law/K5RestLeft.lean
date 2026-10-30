-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5RestLeft.lean: kind K5: WHAT IS LEFT OF K5Rest (K5AtMgPaid.lean: 41 fields) AT THE COMPOSED MEANING's CLOSED CONSTANT, ONCE THE FIELDS "BY THE MAKE" (K5RestMake.lean: sixteen), "FROM AN OPENING" (K5RestOpen.lean: six, and three
tagged [P] beside), ON PUBLIC DATA (K5RestPublic.lean: five; tiePub with K5RestCells.lean), bodyIdn (K5RestIdn.lean) AND cells (K5RestCells.lean: under three conditions on public data) ARE THEOREMS THERE: EIGHT FIELDS, AND K5Rest FROM THEM.
SymsOK follows from the field cells' condition tie (K5RestCells.lean: syms_of_tie).

Main names:
  `K5RestLeft`: eight fields TEXT FOR TEXT out of K5Rest, cut by program, docstrings and tags with them: low · lowI · low0 · seatsPlan · shapesPlan · memAt · sent · someMem.
  `K5RestLeftAll`: that structure at the closed letters (K5RestMake.lean's head lists them).
  `rest_of_left`: **K5RestAll from K5RestLeftAll**, at Zof := zofAll h g, under the head at the second hash function, g < 12, the four equations that fix a · x₁ · Lk · blk, K5Table.openQ's text, PadsAll h (once per head) and ∃ idx, K5CellsCond h a x₁ idx. A structure instance: 41 fields: 8 handed through, 33 theorems.
Is it empty here? K5RestLeftAll · PadsAll · K5CellsCond ARE SHOWN AT NOTHING. EVERY ONE OF THEM IS A SENTENCE ON PUBLIC DATA: NO WITNESS AND NO VERIFIER's STATE IS LEFT IN WHAT IS OWED: tests at the composed meaning's closed data [C] and on public data [P].
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5RestPublic
import Johnson.Desc.First.Att.Door.Law.K5RestCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask lookAt sigListCalls keptAt CellsAre)
open VerifiableInference.Desc.K9 (RunOf readerOf)
open VerifiableInference.Desc.K13.Law (DataK13)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open OnBytes.Road.L5 (dimOf Zs cellsA)
open P5J (AtMgA mgAtAll TS)

section
variable (D : PubData) (Dn : Sent) (ms : List Mem) (Ld : Laid) (Ms : List OracleShape)
  (bs g : ℕ) (a : Attention.Plan) (x : Look.Place) (pl : VerifiableInference.Desc.Place) (rad : OracleShape → Nat) (O : List Item)
  (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)

/-- **What no theorem pays of K5Rest at the closed constant, beside the conditions of its field cells: eight fields.** -/
structure K5RestLeft : Prop where
  /-- [C] seated_fenced (PieceSeated.lean): the open set's sampled tenants lie below the base. -/
  low : ∀ t ∈ sampledIn D.N O, t.1 < bs
  /-- [C] The same for the index masks' tenant. -/
  lowI : D.N.index.1 < bs
  /-- [C] The same for the first sending's tenants. -/
  low0 : ∀ t ∈ D.N.sent (2 * g + 1) 0, t.1 < bs
  /-- [C] TWO TESTS ON PUBLIC DATA (the kind's own; STATED AT THE COMPOSED DATA's dS: RUN NOWHERE AT THAT TERM): the seats. -/
  seatsPlan : seatsPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ld
    (psOf (sigListCalls Dn rad x.link) seat (readMsgs Dn x a.seam.tl)) (D.N.sent x.link 0) (D.N.msgsAt (some pl)) = true
  /-- [C] The shapes. -/
  shapesPlan : shapesPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ms
    (qsOf (sigListCalls Dn rad x.link) (readMsgs Dn x a.seam.tl)) (D.N.msgsAt (some pl)) = true
  /-- [C] THE COMPOSED MEANING's list of members: each message that the law reads is a member at its seat. -/
  memAt : ∀ (fs : List Aff) (j : Fin (sigListCalls Dn rad x.link).length),
    ReadMsg (ReadAddr a.seam.tl fs) Dn x.link j.val → MemAt ms (sigListCalls Dn rad x.link) seat j
  /-- [C] THE COMPOSED MEANING's numbers: the seats lie in the segment's first sending. -/
  sent : ∀ i, seat i ∈ D.N.sent (2 * g + 1) 0
  /-- [C] The composed meaning's list of members (someB | listSits_some, Johnson/P5J/Rad3Seat3At.lean; tests evaluated, not proved: Rad3Seat3Tests.lean): for each member of the caller's list some member of ms is alike: one entry (shape and radius), one seat. (The caller's list itself is no sending of ms.) -/
  someMem : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls Dn rad x.link, seat⟩, i⟩ : Mem)

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The eight at the closed letters. -/
abbrev K5RestLeftAll (Ld : Laid) (Ms : List OracleShape) (bs g : ℕ) (a : Attention.Plan) (x₁ : Look.Place)
    (pl : VerifiableInference.Desc.Place) (O : List Item) : Prop :=
  K5RestLeft h.𝔇.pubD h.𝔇.sent h.𝔇.ms Ld Ms bs g a x₁ pl h.𝔇.l3.rad O (seatAll h x₁)

/-- **K5Rest at the closed letters, from the eight and the three conditions of the field cells.** -/
theorem rest_of_left {Fr : Frame} {Ld : Laid} {Ms : List OracleShape} {bs g : ℕ} {a : Attention.Plan} {x₁ : Look.Place}
    {pl : VerifiableInference.Desc.Place} {O : List Item} {Q : List Pub} {Lk : Link S Claim} {blk : Block S Claim}
    (hg : g < 12) (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (hLk : P5J.At.lk Zp (2 * g + 1) = some Lk)
    (hb : k5AtN (P5J.At.X Zp) (2 * g + 1) g (beforeAll Zp g) = some blk)
    (hQ : ∀ q ∈ Q, q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨ q = .more (some (2 * g + 1)) "ledger.treesAre" ∨
      q = .more (some (2 * g + 1)) "K5.lookLeft")
    (hO : PadsAll h) (C : ∃ idx, K5CellsCond h a x₁ idx)
    (U : K5RestLeftAll h Ld Ms bs g a x₁ pl O) :
    K5RestAll (Fr := Fr) h Ld Ms bs g (beforeAll Zp g) a x₁ pl O Q Lk ProofFile.sameReply blk "planes" (zofAll h g) where
  nsOf := nsOf_all h hg ha
  baseP := baseP_all g Q hQ
  baseIn := baseIn_all
  baseMakes := baseMakes_all _ _
  decTq := decTq_all h
  smpq := smpq_all h
  rwq := rwq_all h
  low := U.low
  lowI := U.lowI
  low0 := U.low0
  tiePub := tiePubCells_all h hg ha hx C
  guard := (seatedOk_guard_all h hg hb).2
  seatsPlan := U.seatsPlan
  shapesPlan := U.shapesPlan
  memAt := U.memAt
  sent := U.sent
  smpIs := smpIs_all h x₁
  objIs := (objIs_gstIs_all h hg hLk).1
  gstIs := (objIs_gstIs_all h hg hLk).2
  constrIs := constrIsPlus_all h Ld Ms
  bodySmall := bodySmall_all h (scope_all h).1 g
  digitsBack := fun _ n _ _ _ _ _ _ _ _ w _ _ _ _ _ hd' => (digits_all h n _ _ _ _ w).mp hd'
  bodyBack := fun π n p _ i s att hd G _ _ _ w _ _ _ _ _ hb => (body_all h n p i π s att hd G _ _ w).mp hb
  cells := cells_all h hO hg ha hx C
  bodyIdn := bodyIdn_all h ha
  someMem := U.someMem
  smpBySeat := smpBySeat_all h
  runsIs := runsIs_all h
  mHIs := mHIs_all h
  rdIs := rdIs_all h
  lkAt := hLk
  statesAt := statesAt_all h hg ha hLk
  sameOut := sameOut_all
  seated := hb
  seatedOk := (seatedOk_guard_all h hg hb).1
  lmIs := lmIs_all h ha hx
  posG := posG_all h hg ha hb
  planesAt := planesAt_all h hg ha hLk
  colsFit := colsFit_all h ha hx
  clForm := clForm_lot
  planesOkAt := planesOkAt_all h ha hx

end

end H2K5.Door

#print axioms H2K5.Door.rest_of_left
