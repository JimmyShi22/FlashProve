-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K09Cond.lean: THE BATCHING KIND's ONE NAMED CONDITION (`K9Cond`) AND
WHAT FOLLOWS FROM IT: the kind's share of the chain of promises in the second form (`KindTiedR …
.K9`, Johnson/Desc/Sound/TiedR.lean), and the tie of the 25 places of the frame's sub-protocol
behind a batching, which are of the kind «frame» and whose law is the link's. With the closed facts
on the written list `P5J.fullLinks` (its list of places is
`flatPlacesOf fullLinks true`). Definitions, theorems, evaluations.

What is said.
  `K9Cond Nm Mg links pl Rch E pcs`: three fields: len: the list of pieces is at least as long as
    the list of places; three: `ThreeAsks` (ThreeTiedR.lean) at every link: the laws of the
    batching's piece, of the piece behind it and of the one equation's, between the promise with
    «reached» at the four borders, at relations of the payer's choice, and five debts a piece at
    these relations; shut: `ShutAsksR` (K9KindTiedR.lean) at every link. `k09_tied`: **`KindTiedR Nm
    Mg links pl Rch E pcs .K9` from `K9Cond` and the Bool on the written list.** `k09_behind`:
    **from the same condition: `TiedAtR` at the place behind each batching.** `k9Fit_links`: the
    kernel's yes of that Bool at the list `P5J.fullLinks`. `k9Count_links`: 75 places there are
    of the kind K9. `batchAt_links`: the batchings' numbers there: 14 m + 9; the head's: 347.

Limits. BOOK-KEEPING: AN IMPLICATION. `K9Cond` IS THE DEBT: nothing of it is paid here; that it can
be met at a real «reached» is shown nowhere (two readers: meetable by its shape). All seven letters
are free: whoever states it as a hypothesis lays terms in. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.ThreeTiedR
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf)
open _root_.Run (ckP)

variable {P W : Type} {F : Frame}

/-- **THE BATCHING KIND's ONE NAMED CONDITION.** -/
structure K9Cond (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop)
    (E : ℕ → (P × S) × F.E.Str → (P × S) × F.E.Str → W → W)
    (pcs : List (Piece (ckP .two) F (P × S) Claim W)) : Prop where
  /-- the list of pieces is at least as long as the list of places -/
  len : pl.length ≤ pcs.length
  /-- at every link: the three pieces' laws and five debts a piece -/
  three : ∀ m < links.length, ∀ qb qq qe, pcs[batchAt links pl m]? = some qb →
    pcs[batchAt links pl m + 1]? = some qq → pcs[batchAt links pl m + 1 + 1]? = some qe →
    ThreeAsks Nm Mg links pl Rch (batchAt links pl m) qb qq qe (E (batchAt links pl m))
      (E (batchAt links pl m + 1)) (E (batchAt links pl m + 1 + 1))
  /-- at every link: what the shutting's tie takes -/
  shut : ∀ m < links.length, ∀ qs, pcs[batchAt links pl m + 4]? = some qs →
    ShutAsksR Nm Mg links pl Rch (batchAt links pl m + 4) qs (E (batchAt links pl m + 4))

variable {Nm : Numbers} {Mg : Meaning P W} {links : List ModelPart} {pl : List Place}
  {Rch : ℕ → (P × S) × F.E.Str → Prop}
  {E : ℕ → (P × S) × F.E.Str → (P × S) × F.E.Str → W → W}
  {pcs : List (Piece (ckP .two) F (P × S) Claim W)}

/-- **THE KIND's SHARE.** -/
theorem k09_tied (hfit : k9Fit links pl = true) (C : K9Cond Nm Mg links pl Rch E pcs) :
    KindTiedR Nm Mg links pl Rch E pcs .K9 :=
  k9_kindTiedR' Nm Mg links pl Rch E pcs hfit C.len C.three C.shut

/-- **THE PLACE BEHIND EACH BATCHING** (of the kind «frame»): tied, from the same condition. -/
theorem k09_behind (C : K9Cond Nm Mg links pl Rch E pcs) (m : ℕ) (hm : m < links.length)
    (hb : batchAt links pl m + 1 + 1 < pl.length)
    (q : Piece (ckP .two) F (P × S) Claim W) (hq : pcs[batchAt links pl m + 1]? = some q) :
    TiedAtR Nm Mg links pl (fun a => a) Rch (batchAt links pl m + 1)
      (q.withMap (E (batchAt links pl m + 1))) := by
  have hl := C.len
  obtain ⟨b₁, b₂, b₃, R0, R1, R1', R2, R3, hqb, hqq, hqe, hEb, hEq, hEe, H⟩ :=
    C.three m hm pcs[batchAt links pl m] q pcs[batchAt links pl m + 1 + 1]
      (List.getElem?_eq_getElem (by omega)) hq (List.getElem?_eq_getElem (by omega))
  exact (three_tied_pubR Nm Mg links pl Rch _ b₁ b₂ b₃ _ _ _ hqb hqq hqe _ _ _ hEb hEq hEe R0 R1
    R1' R2 R3 H).2.1

set_option maxRecDepth 1000000 in
/-- **THE BOOL's YES AT THE LIST `P5J.fullLinks`.** -/
theorem k9Fit_links : k9Fit P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- 75 places there are of the kind K9. -/
theorem k9Count_links :
    ((flatPlacesOf P5J.fullLinks true).filter fun p => p.kind == .K9).length = 75 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **THE BATCHINGS' NUMBERS THERE.** -/
theorem batchAt_links : (List.range 25).map (batchAt P5J.fullLinks
    (flatPlacesOf P5J.fullLinks true)) =
      (List.range 25).map fun m => if m = 24 then 347 else 14 * m + 9 := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k09_tied
#print axioms VerifiableInference.Desc.LinkJoin.k09_behind
#print axioms VerifiableInference.Desc.LinkJoin.k9Fit_links
#print axioms VerifiableInference.Desc.LinkJoin.k9Count_links
#print axioms VerifiableInference.Desc.LinkJoin.batchAt_links
