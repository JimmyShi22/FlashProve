-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/Rad3Seat3At.lean: TWO PARAMETERS OF THE FIRST TABLE's COMPOSED MEANING (MgData.rad3 · MgData.seat3, Johnson/Desc/Sound/MgAll.lean) AS CLOSED TERMS OFF THE PUBLIC PARAMETERS; THE NAMED TESTS THAT GUARD THEM, IN THE SPENDERS' OWN COIN; AND EACH TEST's LAW. Definitions and theorems. Whether the terms are the right ones is the lookups' files' (Johnson/Desc/First/Look/) to show.
  At.sentAt Zp: what the planner sends, as the lookups read it: the closed letters' own codes, shape, layout and built links' lists of arrays (sent_is: IT IS the composed meaning's MgData.sent at the closed letters: rfl).
  At.seat3At Zp := fun l dg j => if dg then seatT ps l j else seatCallsT ps (sentAt Zp) l j, ps := the first chain's seats (Johnson/P5T/SeatsAt.lean): BY ROLE.
  At.rad3At Zp lay := fun sh => the radius of the first sampled entry with the shape sh in the first chain's rows of sendings; 0 where there is none. ONE SOURCE WITH ms: the same rows (rowsAt? Zp.pol lay Zp.KL) of which msAt makes the table's members.
THE TWO DEFAULTS ((0, 0) · 0) ANSWER IN SILENCE: WHAT GUARDS THEM:
  someB ms L seat: every place i of the list L has a member y of ms with y's entry (SHAPE AND RADIUS) = L's at i and y's seat = seat i. Its law some_of_someB ends in the sentence "Alike" (Johnson/Desc/Sound/PinMove.lean) at the list as one sending; listSits_some: in the lookups' structure ListSits' field "some", to the letter.
  sentB N l ts n seat: every seat i below n stands in N.sent l t for a t of ts. sent_of_sentB · listSits_sent (ts := [0]).
  fits_of_some: the field "fits" follows from "some" and the same sentence at the table's own members: an entry and a seat are all that it reads.
  radOneB rows: one shape, one radius, over the first chain's sampled entries: A DIAGNOSIS, NO PREMISE: someB holds the radius too.
  NEGATIVE TESTS (two examples): someB rejects an empty ms at a list of one entry; sentB rejects an empty list of moments.

Limits. The full size's closed letters. The tests on these terms (Johnson/P5J/Rad3Seat3Tests.lean) are EVALUATED, NOT PROVED, at the release's full-size public files: see that file's Limits. The digits' structure (DigSits) is not imported: its fields "some" | "sent" are meant to follow from some_of_someB | sent_of_sentB by unfolding, at ts := [2, 0, 1]: not held by Lean here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LettersRec
import Johnson.P5T.SeatsAt
import Johnson.Desc.First.Look.K3CallsFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open OnBytes
open VerifiableInference.Desc.Sound (Mem Sending Alike SeatFits)
open VerifiableInference.Desc.First (Numbers)

/-- **THE TEST "some"**: general in the members, the list and the seats. -/
def someB (ms : List Mem) (L : List (OracleShape × ℕ)) (seat : ℕ → ℕ × ℕ) : Bool :=
  (List.finRange L.length).all fun i =>
    ms.any fun y => decide (y.1.l.get y.2 = L.get i) && decide (y.1.seat y.2 = seat i.1)

/-- **Its law.** -/
theorem some_of_someB (ms : List Mem) (L : List (OracleShape × ℕ)) (seat : ℕ → ℕ × ℕ)
    (h : someB ms L seat = true) (i : Fin L.length) :
    ∃ y ∈ ms, Alike y ⟨⟨L, fun j => seat j.1⟩, i⟩ := by
  have h1 := List.all_eq_true.1 h i (List.mem_finRange i)
  obtain ⟨y, hy, h2⟩ := List.any_eq_true.1 h1
  obtain ⟨h3, h4⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  exact ⟨y, hy, of_decide_eq_true h3, of_decide_eq_true h4⟩

/-- **THE TEST "sent"**: every seat below n stands in N.sent l t for a t of ts. -/
def sentB (N : Numbers) (l : ℕ) (ts : List ℕ) (n : ℕ) (seat : ℕ → ℕ × ℕ) : Bool :=
  (List.range n).all fun i => ts.any fun t => (N.sent l t).contains (seat i)

/-- **Its law.** -/
theorem sent_of_sentB (N : Numbers) (l : ℕ) (ts : List ℕ) (n : ℕ) (seat : ℕ → ℕ × ℕ)
    (h : sentB N l ts n seat = true) (i : ℕ) (hi : i < n) : ∃ t ∈ ts, seat i ∈ N.sent l t := by
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  obtain ⟨t, ht, h2⟩ := List.any_eq_true.1 h1
  exact ⟨t, ht, List.contains_iff_mem.1 h2⟩

/-- **"fits" follows from "some"**, where the table's own members fit. -/
theorem fits_of_some {Xi : Type} (G : VerifiableInference.Desc.FileDescription Xi) (cs : Codes)
    (ms : List Mem) (L : List (OracleShape × ℕ)) (seatT : Fin L.length → ℕ × ℕ)
    (hf : ∀ y ∈ ms, SeatFits G cs y.1.l y.1.seat)
    (hs : ∀ i, ∃ y ∈ ms, Alike y ⟨⟨L, seatT⟩, i⟩) : SeatFits G cs L seatT := by
  intro i
  obtain ⟨y, hy, e1, e2⟩ := hs i
  have e1' : y.1.l.get y.2 = L.get i := e1
  have e2' : y.1.seat y.2 = seatT i := e2
  have h := hf y hy y.2
  rw [e1', e2'] at h
  exact h

/-- A DIAGNOSIS: one shape, one radius. -/
def radOneB (es : List (OracleShape × ℕ)) : Bool :=
  es.all fun a => es.all fun b => a.1 != b.1 || a.2 == b.2

example : someB [] [(default, 0)] (fun _ => (0, 0)) = false := by decide
example (N : Numbers) : sentB N 0 [] 1 (fun _ => (0, 0)) = false := rfl

end P5T

namespace VerifiableInference.OnPublicFiles
open OnBytes
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers)

/-- **The lookups' field ListSits.some, from the test.** -/
theorem listSits_some (x : Desc.First.Look.Place) (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ)
    (seat : ℕ → ℕ × ℕ) (ms : List Mem)
    (h : P5T.someB ms (sigListCalls D rad x.link) seat = true) :
    ∀ i, ∃ y ∈ ms, Alike y ⟨callsSending x D rad (fun j => seat j.1), i⟩ :=
  fun i => P5T.some_of_someB ms _ seat h i

/-- **The lookups' field ListSits.sent, from the test.** -/
theorem listSits_sent (x : Desc.First.Look.Place) (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ)
    (seat : ℕ → ℕ × ℕ) (N : Numbers) (m : ℕ)
    (h : P5T.sentB N m [0] (sigListCalls D rad x.link).length seat = true) :
    ∀ i : Fin (sigListCalls D rad x.link).length, seat i.1 ∈ N.sent m 0 := by
  intro i
  obtain ⟨t, ht, h1⟩ := P5T.sent_of_sentB N m [0] _ seat h i.1 i.2
  obtain rfl : t = 0 := List.mem_singleton.1 ht
  exact h1

end VerifiableInference.OnPublicFiles

namespace P5J.At
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (Sent)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- What the planner sends, as the lookups read it: off the closed letters. -/
def sentAt : Sent := ⟨cs Zp, shape Zp, layout Zp, Zp.made.p.built.links.map (·.arrayOf)⟩

/-- **seat3**: link, sort of lookup (true: on the digits), member's number: its tree and tenant. -/
def seat3At : ℕ → Bool → ℕ → ℕ × ℕ := fun l dg j =>
  if dg then P6T.seatT (pseats Zp) l j else P6T.seatCallsT (pseats Zp) (sentAt Zp) l j

/-- The first chain's sampled entries (shape, radius), in the rows' order: of the same rows as ms. -/
def sampledAt (lay : ByteArray) : List (OracleShape × ℕ) :=
  (P5T.firstRows ((P5T.rowsAt? Zp.pol lay Zp.KL).getD [])).flatMap (·.sampled)

/-- **rad3**: a shape's radius. -/
def rad3At (lay : ByteArray) : OracleShape → ℕ := fun sh =>
  (((sampledAt Zp lay).find? (·.1 == sh)).map (·.2)).getD 0

/-- **sentAt IS the composed meaning's own "what the planner sends" at the closed letters.** -/
theorem sent_is {pp : Inst.Model.ScalesAndPolicy}
    (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
      OnBytes.Flat.numsFull pp))
    (hs : Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
    (lay : ByteArray)
    (hL : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
    (hN : VerifiableInference.Desc.Sound.SeatsNamed (arr Zp) (N Zp cF) (Meaning.sizesOf (X Zp))
      (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))))
    (hG : VerifiableInference.Desc.Sound.GroupsSeated (ms Zp lay) (N Zp cF)) {nR : ℕ}
    (𝔇₀ : VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    (𝔇At o Zp Np cF E hs lay hL hN hG 𝔇₀).sent = sentAt Zp := rfl

end P5J.At

#print axioms P5J.At.sent_is
#print axioms P5T.some_of_someB
#print axioms P5T.sent_of_sentB
#print axioms P5T.fits_of_some
#print axioms VerifiableInference.OnPublicFiles.listSits_some
#print axioms VerifiableInference.OnPublicFiles.listSits_sent
