-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsParts.lean: the kind "lookup" (K3): what each
reader of the verifier's state answers behind an accepting step of the description's own member at a
lookup on the digits of a layers' or an attention link, in terms of what it answers in front.
Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the shape of a ledger is `ledSh`
(Johnson/Desc/First/Shape/Parts.lean); the shape of the smallness test's structure is `tailSh`
(Johnson/Desc/First/Shape/Tail.lean). The state bears no mark if `failed = none`.

What is shown.
  `setPlan`: code on the ledger's shape: the plan's number of claims is laid (helper: `ledSh_plan`).
  `DigitsHere`: the state behind, field by field, by the sort of the link that is open.
  `digits_here_of`: `DigitsHere` from the equation in the state's own setters, which `digits_state`
    (Honest/K3/Law/Thread/StateBehindDigits.lean) gives.
  `digits_parts`: reader by reader, at the state sj' behind the step:
    fork?: its shape behind is `lookUpd` (Honest/K3/Shape/Ops.lean) of the face at its shape in
      front, with the plan's number of claims laid.
    tl?: four fields of its shape change: one more fold sampled; the ledger's count in front and
      behind; what was heard, which is `lookHeardSh` (Honest/K3/Shape/HeardOps.lean) of the lookup's
      shape, the ledger's count in front and its number of owed claims in front.
    As in front: lookHeard?, look?, funs?, link?, rowsOwed, st, out, check, book, roots, req.
    The state behind bears no mark.

Hypotheses that remain. All but the last are those of `digits_state`.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the digits.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `hq`: what stands behind the lookup without a round is `quietDigits used claims`
    (Johnson/Desc/First/Look/K3Whole.lean).
  `h`: the member's step accepts from sj to sj'.
  `hSz`: the ledger in front has its three arrays at their size; this is a test on its shape
    (`sizedB`, Johnson/Desc/First/Shape/Parts.lean).
  `hF`, `e`: (in `digits_here_of`) a ledger is open in front; the state behind is the one in front
    with the structure and two ledgers written in.

Follows. This file is the counterpart, at the digits, of Honest/K3/Law/Thread/CallsParts.lean.

Imported: Johnson/Desc/First/Shape/Parts.lean and Johnson/Desc/First/Shape/Tail.lean.

Users. Honest/K3/Law/Thread/CarriesDigits.lean calls `digits_parts` and `digits_here_of`;
Honest/K3/Law/Thread/K3KeepsSh.lean [not in this library] calls `ledSh_plan`.

Limits. Not at the digits of the head's own link: another step stands behind the lookup there. From
an acceptance alone. On the verifier's side alone. The definition `DigitsHere` of this file has the
same text as `DigitsArms` (Honest/K3/Law/KeepsDefs.lean), under another name; likewise the statement
of this file's `digits_here_of` is that of `digits_arms_of` (Honest/K3/Law/Thread/K3Keeps.lean). The
tie of the two definitions: `digitsHere_iff` (Honest/K3/Law/Thread/TiesHere.lean
[not in this library]). No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehindDigits
import Johnson.Desc.ProofFile.Honest.K3.Shape.Walk
import Johnson.Desc.ProofFile.Honest.K3.Shape.HeardTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork HTailF2)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf quietAt quietDigits)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (LedSh ledSh tailSh heardAll sizedB sized_of_B)
open ProofFile.Honest.K3.Shape (lookUpd lookHeardSh hearVia_sh hearVia_heard)

local notation "FS" => VerifiableInference.Desc.First.S

/-- The plan's number of claims, laid in the ledger's shape. -/
def setPlan (L : LedSh) (c : Nat) : LedSh :=
  LedSh.mk L.ns L.shown L.factors L.got L.owed c L.trees L.next L.coefs L.claims L.drawn L.handed
    L.shut

theorem ledSh_plan (G : Fork) (c : Nat) : ledSh { G with planClaimsF := c } = setPlan (ledSh G) c :=
  rfl

/-- The state behind, field by field: one case for each sort of link that can be open. -/
def DigitsHere (sj sj' : FS) (tl' : HTailF2) (G' : Fork) : Prop :=
  (∃ a, sj.here = .lay a ∧ sj' = { sj with here := .lay { a with tl := tl', F := G' } }) ∨
  (∃ a, sj.here = .att a ∧ sj' = { sj with here := .att { a with tl := tl', F := G' } }) ∨
  ∃ a, sj.here = .head a ∧ a.opened = true ∧
    sj' = { sj with here := .head { a with tl := tl', F := G' } }

/-- **`DigitsHere` from the equation in the state's own setters.** -/
theorem digits_here_of {sj sj' : FS} {F G G' : Fork} {tl' : HTailF2} (hF : sj.fork? = some F)
    (e : sj' = ((sj.putTl tl').putFork G).putFork G') : DigitsHere sj sj' tl' G' := by
  subst e
  unfold S.fork? at hF
  cases hh : sj.here with
  | lay a =>
    refine Or.inl ⟨a, hh, ?_⟩
    simp [S.putTl, S.putFork, hh]
  | att a =>
    refine Or.inr (Or.inl ⟨a, hh, ?_⟩)
    simp [S.putTl, S.putFork, hh]
  | head a =>
    rw [hh] at hF
    have hF' : (if a.opened = true then some a.F else none) = some F := hF
    cases ho : a.opened with
    | false =>
      rw [ho] at hF'
      exact nomatch hF'
    | true =>
      refine Or.inr (Or.inr ⟨a, hh, ho, ?_⟩)
      simp [S.putTl, S.putFork, hh, ho]
  | between =>
    rw [hh] at hF
    exact nomatch hF
  | fin a =>
    rw [hh] at hF
    exact nomatch hF
  | mem a =>
    rw [hh] at hF
    exact nomatch hF

/-- **Reader by reader, behind the accepting step of the description's own member at a lookup on the
digits.** Conditional on what this file's head lists. No instance of these hypotheses is exhibited
in this file. -/
theorem digits_parts (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (used claims : Nat)
    (hq : quietAt Z.p.X s.link true = some (quietDigits used claims)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n))
    (hSz : ∀ F, sj.fork? = some F → sizedB (ledSh F) = true) :
    ∃ tl F, sj.tl? = some tl ∧ sj.fork? = some F ∧
      sj'.fork?.map ledSh = some (setPlan (lookUpd (faceOf s.shape) (ledSh F)) claims) ∧
      sj'.tl?.map tailSh = some { tailSh tl with
        foldDrawn := (tailSh tl).foldDrawn + 1, slotA := (ledSh F).next,
        slotB := (lookUpd (faceOf s.shape) (ledSh F)).next,
        heard := some (lookHeardSh s.shape F.next F.owed.size) } ∧
      sj'.lookHeard? = sj.lookHeard? ∧ sj'.look? = sj.look? ∧ sj'.funs? = sj.funs? ∧
      sj'.link? = sj.link? ∧ sj'.rowsOwed = sj.rowsOwed ∧ sj'.st = sj.st ∧ sj'.out = sj.out ∧
      sj'.check = sj.check ∧ sj'.book = sj.book ∧ sj'.roots = sj.roots ∧ sj'.req = sj.req ∧
      sj'.failed = none := by
  obtain ⟨tl, F, H, G, htl, a1, _, _, _, a5, _, e, hf⟩ := digits_state o pol lay KL Fd Z Bs base ch
    A B O s hs hd lot m hb hbs hm hmp hpk used claims hq ft sj sj' n rs c h
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _⟩ := site_facts _ _ x s hsx
  have hS := sized_of_B (hSz F a1)
  have e1 := (hearVia_sh hS f2 a5).2
  have e2 := hearVia_heard hS f2 a5
  have eT : tailSh { tl with
      foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some H } =
      { tailSh tl with
        foldDrawn := (tailSh tl).foldDrawn + 1, slotA := (ledSh F).next,
        slotB := (lookUpd (faceOf s.shape) (ledSh F)).next,
        heard := some (lookHeardSh s.shape F.next F.owed.size) } := by
    rw [← e1, ← e2]
    rfl
  have eF : ledSh { G with planClaimsF := claims } =
      setPlan (lookUpd (faceOf s.shape) (ledSh F)) claims := by rw [ledSh_plan, e1]
  refine ⟨tl, F, htl, a1, ?_⟩
  rcases digits_here_of a1 e with ⟨a, hh, rfl⟩ | ⟨a, hh, rfl⟩ | ⟨a, hh, ho, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hf⟩
    · simp [S.fork?, eF]
    · simp [S.tl?, eT]
    · simp [S.lookHeard?, hh]
    · simp [S.look?, hh]
    · simp [S.funs?, hh]
    · simp [S.link?, hh]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hf⟩
    · simp [S.fork?, eF]
    · simp [S.tl?, eT]
    · simp [S.lookHeard?, hh]
    · simp [S.look?, hh]
    · simp [S.funs?, hh]
    · simp [S.link?, hh]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hf⟩
    · simp [S.fork?, ho, eF]
    · simp [S.tl?, ho, eT]
    · simp [S.lookHeard?, hh, ho]
    · simp [S.look?, hh, ho]
    · simp [S.funs?, hh, ho]
    · simp [S.link?, hh, ho]

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.ledSh_plan
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_here_of
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_parts
