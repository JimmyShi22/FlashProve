-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/ReturnsStep.lean: conditional: `hearV_returns_fit`
(Honest/K3/Shape/ReturnsFit.lean) in the forms of the places where it is called: at the library's
sub-protocols of the kind "lookup", from the library's two tests of a step on form (`Block.Fits`,
Johnson/Top/H0/StepLaws/StepLaws.lean) or from the step's acceptance. Theorems; two tests by
evaluation.

Terms. Honest/K3/GLOSSARY.md: see there hearing, round, entry, sub-protocol, step, window (of the
ledger's slots) and face. In this file: entries are declared bare (`bare es`) if each round's
declaration holds its entry and nothing else (`bare` has the text of the library's `Tape.plain`,
Johnson/Desc/First/Tape/TapeFits.lean: the tie: `bare_eq_plain`, Honest/K3/Law/TiesSealedForms.lean
[not in this library]; and it is `es.map declOf`, Honest/K3/Law/Statements.lean, written out); the
three sub-protocols are `blockVia` (Johnson/Desc/First/Look/Via/Via.lean), `blockV`
(Johnson/Desc/First/Look/Via/Rounds.lean) and `lookupKind` (Johnson/Desc/First/Look/K3LookupGeneral.lean).

What is shown.
  `rounds_blockVia`, `rounds_blockV`, `rounds_blockG`: the declared rounds of the three
    sub-protocols are the planner's entries, declared bare: by `rfl`.
  `fit_of_fits`, `fit_of_step`: the library's test on the rounds, out of `Block.Fits`; out of an
    acceptance of `Block.step`.
  `hearV_returns_at`: at any sub-protocol whose declared rounds are a list of entries declared bare:
    from `Block.Fits`: the hearing returns on the rounds that the decision is shown.
  `hearV_returns_fitsVia`, `hearV_returns_fitsG`: the same at `blockVia` and at `lookupKind`.
  `hearV_returns_stepVia`, `hearV_returns_stepG`: the same from the step's acceptance.
  `roundsFit_blank`, `fits_blank`, `hearV_returns_at_blank`: an instance of the hypotheses together,
    by proof, at every face and every list of entries that passes `entriesFit` (Rounds.lean): the
    blank rounds pass `Block.Fits` at such a sub-protocol.
  two tests by evaluation: `nzAll` accepts a sample that is not 0 at the round "PSC Y" and rejects
    0.

Hypotheses that remain, in `hearV_returns_at`.
  `hok`: the face passes its own test.
  `W`: the window in front: the lookup's slots are there and free (`Win`,
    Honest/K3/Shape/Window.lean).
  `hr`: the sub-protocol's declared rounds are es, declared bare.
  `hfit`: `entriesFit f es`.
  `h`: `Block.Fits`.

Users. Honest/K3/Law/Thread/MemberDecides.lean imports this file.

Limits. At `lookupKind` the decision calls `hearG`, not `hearV`: that `hearG` returns where `hearV` does
is not shown in this folder. Shown in: the library's Johnson/Top/H/K3Via/BridgeEntries.lean
(`hearV_hearG`), conditional on the place's planner's entries passing `entriesFit` and each of them
the test `staticT`; it is not called here. And the own test of `lookupKind` on the plan does not hold
`entriesFit` (those of `blockVia` and `blockV` do): there it is a public test that somebody must
evaluate. It says that the hearing returns: between it and the seated decision's return stand the
seat's three readings in front, "several calls" and the writing into the older structure
(`toHeard`): these are not spoken of. The rounds of the instance are no honest prover's.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.ReturnsFit
import Johnson.Desc.First.Look.Via.Via
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block OpenedColumn roundsFit noDigest itemOf drawsMarkedNonzeroHaveNonzeroWords step_iff)
open VerifiableInference.Desc.Part.MaskedSum (entry)
open VerifiableInference.Desc.K3 (hearV entriesV entriesFit blockV lookupKind SeatV SeatG PG)
open VerifiableInference.Desc.K3.Law (blockVia)
open VerifiableInference.Desc.First.Look (P Guest)

local notation "KFace" => VerifiableInference.Desc.K3.Face

/-- A list of entries, each declared bare: no stored part and no tree is opened. -/
abbrev bare (es : List Fmt.Entry) : List Fmt.DeclaredRound := es.map fun e => { entry := e }

/-! ## The spellings -/

theorem rounds_blockVia {S Cl : Type} (seat : VerifiableInference.Desc.K3.Seat S Cl)
    (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat)) (p : P)
    (guests : List (Guest S Cl)) :
    (blockVia seat piece laid before p guests).rounds = bare (p.entries.getD []) := rfl

theorem rounds_blockV {S Cl : Type} (seat : SeatV S Cl) (before : List (Nat × Nat)) (bits : Nat)
    (guests : List (Guest S Cl)) (p : PG) :
    (blockV seat before bits guests p).rounds = bare (p.entries.getD []) := rfl

theorem rounds_blockG {S Cl : Type} (seat : SeatG S Cl) (before : List (Nat × Nat)) (bits : Nat)
    (guests : List (Guest S Cl)) (p : PG) :
    (lookupKind seat before bits guests p).rounds = bare (p.entries.getD []) := rfl

/-- The library's test on the rounds is the first of its two tests of a step on form. Conditional on
these two. -/
theorem fit_of_fits {S Cl : Type} {blk : Block S Cl} {ft : Nat} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} (h : blk.Fits ft rs cols) : roundsFit blk.rounds rs = true := h.1

/-- Conditional on the step's acceptance. -/
theorem fit_of_step {S Cl : Type} {blk : Block S Cl} {ft : Nat} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {n : Nat} (h : blk.step ft s rs cols = .ok (s', n)) :
    roundsFit blk.rounds rs = true := ((step_iff ft blk s s' rs cols n).1 h).1.1

/-! ## The main theorems -/

/-- **The hearing returns on the rounds that the decision is shown.** Conditional on the face's own
test, the window, the sub-protocol's declared rounds being es declared bare, `entriesFit` and
`Block.Fits`. An instance: `hearV_returns_at_blank` (by proof). -/
theorem hearV_returns_at {S Cl : Type} (f : KFace) (hok : f.ok = true) {F : Fork}
    (W : Win F.next F.next (F.next + f.slots) F) {blk : Block S Cl} {es : List Fmt.Entry}
    (hr : blk.rounds = bare es) (hfit : entriesFit f es = true) {ft : Nat} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} (h : blk.Fits ft rs cols) :
    ∃ g G, hearV f F (rs.map noDigest) = some (g, G) :=
  hearV_returns_fit f hok W hfit (by
    have h1 := h.1
    rw [hr] at h1
    exact h1)

/-- At the seated lookup's sub-protocol. Conditional on the like. No instance of these hypotheses is
exhibited in this file. -/
theorem hearV_returns_fitsVia {S Cl : Type} (f : KFace) (hok : f.ok = true) {F : Fork}
    (W : Win F.next F.next (F.next + f.slots) F) (seat : VerifiableInference.Desc.K3.Seat S Cl)
    (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat)) (p : P)
    (guests : List (Guest S Cl)) (hfit : entriesFit f (p.entries.getD []) = true) {ft : Nat}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (h : (blockVia seat piece laid before p guests).Fits ft rs cols) :
    ∃ g G, hearV f F (rs.map noDigest) = some (g, G) :=
  hearV_returns_at f hok W (rounds_blockVia seat piece laid before p guests) hfit h

/-- At the general lookup's sub-protocol, whose decision calls another hearing: see this file's
head. Conditional on the like. No instance of these hypotheses is exhibited in this file. -/
theorem hearV_returns_fitsG {S Cl : Type} {F : Fork} (seat : SeatG S Cl)
    (before : List (Nat × Nat)) (bits : Nat) (guests : List (Guest S Cl)) (p : PG)
    (hok : p.face.ok = true) (W : Win F.next F.next (F.next + p.face.slots) F)
    (hfit : entriesFit p.face (p.entries.getD []) = true) {ft : Nat} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} (h : (lookupKind seat before bits guests p).Fits ft rs cols) :
    ∃ g G, hearV p.face F (rs.map noDigest) = some (g, G) :=
  hearV_returns_at p.face hok W (rounds_blockG seat before bits guests p) hfit h

/-- From the step's acceptance. Conditional on the like. No instance of these hypotheses is
exhibited in this file. -/
theorem hearV_returns_stepVia {S Cl : Type} (f : KFace) (hok : f.ok = true) {F : Fork}
    (W : Win F.next F.next (F.next + f.slots) F) (seat : VerifiableInference.Desc.K3.Seat S Cl)
    (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat)) (p : P)
    (guests : List (Guest S Cl)) (hfit : entriesFit f (p.entries.getD []) = true) {ft : Nat}
    {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat}
    (h : (blockVia seat piece laid before p guests).step ft s rs cols = .ok (s', n)) :
    ∃ g G, hearV f F (rs.map noDigest) = some (g, G) :=
  hearV_returns_fitsVia f hok W seat piece laid before p guests hfit
    ((step_iff ft _ s s' rs cols n).1 h).1

/-- From the step's acceptance, at the general lookup's sub-protocol. Conditional on the like.
No instance of these hypotheses is exhibited in this file. -/
theorem hearV_returns_stepG {S Cl : Type} {F : Fork} (seat : SeatG S Cl)
    (before : List (Nat × Nat)) (bits : Nat) (guests : List (Guest S Cl)) (p : PG)
    (hok : p.face.ok = true) (W : Win F.next F.next (F.next + p.face.slots) F)
    (hfit : entriesFit p.face (p.entries.getD []) = true) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat}
    (h : (lookupKind seat before bits guests p).step ft s rs cols = .ok (s', n)) :
    ∃ g G, hearV p.face F (rs.map noDigest) = some (g, G) :=
  hearV_returns_fitsG seat before bits guests p hok W hfit ((step_iff ft _ s s' rs cols n).1 h).1

/-! ## An instance of the hypotheses together -/

theorem items_blank (n : Nat) :
    (List.replicate n (Fmt.ItemValue.e (0, 0, 0))).map itemOf = List.replicate n Fmt.Item.e := by
  rw [List.map_replicate]
  rfl

/-- **At plain entries, declared bare, the blank rounds pass the library's test on the rounds.**
Conditional on the entries being plain; an instance: `plain_entriesV` (by proof). -/
theorem roundsFit_blank : ∀ (es : List Fmt.Entry), (∀ e ∈ es, Plain e) →
    roundsFit (bare es) (es.map blankR) = true
  | [], _ => rfl
  | e :: es, hP => by
    have P := hP e (List.mem_cons_self ..)
    have ih := roundsFit_blank es fun x hx => hP x (List.mem_cons_of_mem _ hx)
    show ((blankR e).vals.map itemOf ==
        ({ entry := e } : Fmt.DeclaredRound).items.filter (· != .root) &&
      (blankR e).drawn.elems.length == e.drawE && (blankR e).drawn.poss.length == e.poss &&
      (blankR e).drawn.trits.length == e.trits && (blankR e).drawn.poss.all (· < 2 ^ e.logN) &&
      (blankR e).drawn.trits.all (fun t => t == -1 || t == 0 || t == 1) &&
      drawsMarkedNonzeroHaveNonzeroWords { entry := e } (blankR e) && roundsFit (bare es) (es.map blankR)) = true
    rw [cut_plain P, nz_blank P, ih, P.poss, P.trits]
    show ((List.replicate (e.msg / 24) (Fmt.ItemValue.e (0, 0, 0))).map itemOf ==
      List.replicate (e.msg / 24) Fmt.Item.e &&
      (List.replicate e.drawE ((1 : UInt64), (0 : UInt64), (0 : UInt64))).length == e.drawE &&
      true && true && true && true && true && true) = true
    rw [items_blank, List.length_replicate]
    simp

/-- Entries that pass `entriesFit` are plain. Conditional on that test. -/
theorem plain_of_fit {f : KFace} {es : List Fmt.Entry} (hfit : entriesFit f es = true) :
    ∀ e ∈ es, Plain e := by
  intro e hm
  have P := plain_entriesV f { e with work := 0 } (by
    rw [← fit_eq hfit]
    exact List.mem_map.2 ⟨e, hm, rfl⟩)
  exact ⟨P.answers, P.roots, P.poss, P.trits, P.msg, P.kind⟩

theorem groups_bare (ft : Nat) : ∀ (es : List Fmt.Entry) (Rs : List Fmt.Drawn),
    (VerifiableInference.Desc.groupsOf ft (bare es) Rs).flatMap id = []
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: es, _ :: Rs => groups_bare ft es Rs

/-- Rounds that are declared bare read no column. Conditional on their being so declared. -/
theorem want_bare {S Cl : Type} {blk : Block S Cl} {es : List Fmt.Entry}
    (hr : blk.rounds = bare es) (ft : Nat) (rs : List Fmt.RoundView) : blk.want ft rs = [] := by
  unfold Block.want
  rw [hr]
  exact groups_bare ft es _

/-- **The blank rounds pass the library's two tests of a step on form**, with no column. Conditional
on the declared rounds being es declared bare, and on `entriesFit`. -/
theorem fits_blank {S Cl : Type} {f : KFace} {blk : Block S Cl} {es : List Fmt.Entry}
    (hr : blk.rounds = bare es) (hfit : entriesFit f es = true) (ft : Nat) :
    blk.Fits ft (es.map blankR) [] := by
  refine ⟨by rw [hr]; exact roundsFit_blank es (plain_of_fit hfit), ?_⟩
  rw [want_bare hr]
  rfl

/-- **An instance of the hypotheses of `hearV_returns_at` together**: at every face that passes its
own test, every list of entries that passes `entriesFit`, every sub-protocol that declares them
bare, and every count in front. Conditional on these tests alone. -/
theorem hearV_returns_at_blank {S Cl : Type} (f : KFace) (hok : f.ok = true) (first : Nat)
    {blk : Block S Cl} {es : List Fmt.Entry} (hr : blk.rounds = bare es)
    (hfit : entriesFit f es = true) (ft : Nat) :
    ∃ g G, hearV f (ledgerR first f.slots) ((es.map blankR).map noDigest) = some (g, G) :=
  hearV_returns_at f hok (win_at first f.slots) hr hfit (fits_blank hr hfit ft)

/-! ## The one test with code of these files can reject -/

#guard nzAll [entry "PSC Y" 2 1 1] [⟨[.e (0, 0, 0), .e (0, 0, 0)], ⟨[(1, 0, 0)], [], [], none⟩⟩]
#guard !nzAll [entry "PSC Y" 2 1 1] [⟨[.e (0, 0, 0), .e (0, 0, 0)], ⟨[(0, 0, 0)], [], [], none⟩⟩]

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.rounds_blockVia
#print axioms ProofFile.Honest.K3.Shape.rounds_blockV
#print axioms ProofFile.Honest.K3.Shape.rounds_blockG
#print axioms ProofFile.Honest.K3.Shape.fit_of_fits
#print axioms ProofFile.Honest.K3.Shape.fit_of_step
#print axioms ProofFile.Honest.K3.Shape.hearV_returns_at
#print axioms ProofFile.Honest.K3.Shape.hearV_returns_fitsVia
#print axioms ProofFile.Honest.K3.Shape.hearV_returns_fitsG
#print axioms ProofFile.Honest.K3.Shape.hearV_returns_stepVia
#print axioms ProofFile.Honest.K3.Shape.hearV_returns_stepG
#print axioms ProofFile.Honest.K3.Shape.items_blank
#print axioms ProofFile.Honest.K3.Shape.roundsFit_blank
#print axioms ProofFile.Honest.K3.Shape.plain_of_fit
#print axioms ProofFile.Honest.K3.Shape.groups_bare
#print axioms ProofFile.Honest.K3.Shape.want_bare
#print axioms ProofFile.Honest.K3.Shape.fits_blank
#print axioms ProofFile.Honest.K3.Shape.hearV_returns_at_blank
