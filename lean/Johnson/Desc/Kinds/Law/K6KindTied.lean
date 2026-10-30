-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6KindTied.lean (it asks Seated (Desc/Sound/K6Tied.lean);
general in a condition Rch beside the table's
promise: it ends in KindTiedR): THE OUTPUT HEAD'S KIND'S SHARE OF THE CHAIN OF
PROMISES AT
THE FULL CHAIN (Johnson/Desc/Sound/TiedPlaces.lean: KindTied ... K6: at every place of kind K6 the
piece there, with the table's extractor laid in, is tied), from the tie at sub-protocol 341
(Law/K6TiedAtObject.lean: k6_tied_cut_full).

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  k6_once_full: the full chain's flat list of places holds the kind K6 at number 341 and nowhere
      else (a test with code over the closed list, evaluated by the kernel).
  kindTied_K6_full: if the piece at number 341 is seated and meets the bill (K6DueAt):
      KindTied N Mg linksFull (the driver's places) (the table's extractors) l K6.

Every letter under "there is" (in the premise hall): bef, bS, B: tied to q by Seated; num: read
by one field of the bill alone.
What it does not say. THAT THE PIECE AT NUMBER 341 OF THE DESCRIPTION'S OWN LIST IS SEATED, OR
THAT THE BILL IS MET. KindTied ends in TiedAt, where the law's own relations stand under "there
are": WHAT THE READING IS WORTH TO THE CHAIN IS WHAT THE BILL'S items CAN BE PAID FOR AT THE TABLE'S
OWN MEANING, and a member is wanted beside such theorems: until then this is a share payable in
form, no more. THE FULL CHAIN ALONE: for the small chain nothing is said. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.K6TiedAtObject
import Johnson.Desc.Sound.TiedPlaces
import Johnson.Desc.Sound.TiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Item Numbers Meaning pubFit pubOfItems sampledIn start
  readsOpen)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT onQ meansQ relQ insQ outsQ
  extQAt openQ pubQ insL Fenced TiedByR SigFields rowsApart ridersK6 linksFull head_full mark_full
  len_full place342_full reads_full apart_full riders341_full Along RoundIs KindTiedR)
open _root_.Iop (Err)

namespace AtTable

variable {rows cols : Nat} (cs : OnBytes.Codes) {Xi P Tok : Type} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
  (c₀ : Fin rows → Fin cols → GE) (msR : List Mem) (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (Wp : OnBytes.Model.Verify.Public)
  (pl : ℕ → ℕ × Bool × ℕ × ℕ) (Fr : Frame) (tokOf : P × S → Tok)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

set_option maxRecDepth 1000000 in
/-- The test, with code. -/
theorem k6_once_fullB : ((First.flatPlacesOf linksFull true).zipIdx.all fun x =>
    !(Decidable.decide (x.1.kind = .K6)) || x.2 == 341) = true := by decide +kernel

/-- **The full chain holds the kind K6 once.** -/
theorem k6_once_full (i : ℕ) (a : Place) (hi : (First.flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = .K6) : i = 341 := by
  have h := List.all_eq_true.1 k6_once_fullB (a, i) (List.mem_zipIdx_iff_getElem?.2 hi)
  simpa [hk] using h

/-- **The kind's share of the chain of promises, at the full chain.** -/
theorem kindTied_K6_full (Rch : ℕ → (P × S) × Fr.E.Str → Prop)
    (l : List (Piece (_root_.Run.ckP .two) Fr (P × S) Claim
      (Wit (Fin rows → Fin cols → GE) Tok MsgT)))
    (hfit : pubFit Mg.more linksFull (First.flatPlacesOf linksFull true) = true)
    (hSig : SigFields cs G arr smp msR decT Mg)
    (hall : ∀ q, l[341]? = some q → ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim)
      (num : Fmt.TreeSource → Nat), Seated Wp .two Fr q 24 bef B bS ∧
        K6DueAt cs G arr smp decT msR N s seat Wp pl Fr Mg linksFull 341 Rch bS num q) :
    KindTiedR N Mg linksFull (First.flatPlacesOf linksFull true) Rch
      (fun i => extQAt cs G arr smp msR decT c₀ tokOf N linksFull
        (First.flatPlacesOf linksFull true) (fun a => a) i) l .K6 := by
  intro i q a hq ha hk
  obtain rfl := k6_once_full i a ha hk
  obtain ⟨bef, bS, B, num, Hs, D⟩ := hall q hq
  exact (k6_tied_cut_full cs G arr smp decT c₀ msR N s seat Wp pl Fr tokOf Mg Rch bef bS B
      num q Hs hfit hSig D).tiedAtR

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_once_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.kindTied_K6_full
