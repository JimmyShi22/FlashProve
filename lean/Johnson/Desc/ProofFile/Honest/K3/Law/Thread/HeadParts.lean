-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadParts.lean: the kind "lookup" (K3): what each reader
of the verifier's state answers behind an accepting step of the description's own member at the
lookup on the digits of the head's link, in terms of what it answers in front. One theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: the shape of a ledger is `ledSh`
(Johnson/Desc/First/Shape/Parts.lean); the shape of the smallness test's structure is `tailSh`
(Johnson/Desc/First/Shape/Tail.lean). The state bears no mark if `failed = none`.

What is shown.
  `headDigits_parts`: reader by reader, at the state sj' behind the step:
    fork?: its shape behind is `lookUpd` (Honest/K3/Shape/Ops.lean) of the face at its shape in
      front.
    tl?: four fields of its shape change, as at the digits of the other links.
    The claim on the weights is laid in the link's own part: no reader named here sees it.
    As in front: lookHeard?, look?, funs?, link?, rowsOwed, st, out, check, book, roots, req.
    The state in front and the state behind stand in the head's link, which is open. The state
      behind bears no mark.

Hypotheses that remain. All but the last are those of `headDigits_state`
(Honest/K3/Law/Thread/StateBehindHead.lean).
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the digits.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `hq`: what stands behind the lookup without a round is `quietHead`
    (Johnson/Desc/First/Look/K3Whole.lean).
  `h`: the member's step accepts from sj to sj'.
  `hSz`: the ledger in front has its three arrays at their size; this is a test on its shape
    (`sizedB`, Johnson/Desc/First/Shape/Parts.lean).

Follows. This file is the counterpart of Honest/K3/Law/Thread/CallsParts.lean and
Honest/K3/Law/Thread/DigitsParts.lean.

Imported: Johnson/Desc/First/Shape/Parts.lean and Johnson/Desc/First/Shape/Tail.lean.

Users. Honest/K3/Law/Thread/CarriesHeadDigits.lean calls `headDigits_parts`.

Limits. From an acceptance alone. On the verifier's side alone. Of the claim that is laid nothing is
said. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehindHead
import Johnson.Desc.ProofFile.Honest.K3.Shape.Walk
import Johnson.Desc.ProofFile.Honest.K3.Shape.HeardTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork HTailF2)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf quietAt quietHead)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ledSh tailSh heardAll sizedB sized_of_B)
open ProofFile.Honest.K3.Shape (lookUpd lookHeardSh hearVia_sh hearVia_heard)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **Reader by reader, behind the accepting step of the description's own member at the lookup on
the digits of the head's link.** Conditional on what this file's head lists. No instance of these
hypotheses is exhibited in this file. -/
theorem headDigits_parts (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n))
    (hSz : ∀ F, sj.fork? = some F → sizedB (ledSh F) = true) :
    ∃ tl F a₀ a', sj.tl? = some tl ∧ sj.fork? = some F ∧
      sj.here = .head a₀ ∧ a₀.opened = true ∧ sj'.here = .head a' ∧ a'.opened = true ∧
      sj'.fork?.map ledSh = some (lookUpd (faceOf s.shape) (ledSh F)) ∧
      sj'.tl?.map tailSh = some { tailSh tl with
        foldDrawn := (tailSh tl).foldDrawn + 1, slotA := (ledSh F).next,
        slotB := (lookUpd (faceOf s.shape) (ledSh F)).next,
        heard := some (lookHeardSh s.shape F.next F.owed.size) } ∧
      sj'.lookHeard? = sj.lookHeard? ∧ sj'.look? = sj.look? ∧ sj'.funs? = sj.funs? ∧
      sj'.link? = sj.link? ∧ sj'.rowsOwed = sj.rowsOwed ∧ sj'.st = sj.st ∧ sj'.out = sj.out ∧
      sj'.check = sj.check ∧ sj'.book = sj.book ∧ sj'.roots = sj.roots ∧ sj'.req = sj.req ∧
      sj'.failed = none := by
  obtain ⟨tl, F, H, G, a, claim, htl, a1, _, _, _, a5, eh, ho, e, hf⟩ := headDigits_state o pol lay
    KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk hq ft sj sj' n rs c h
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
  cases hh : sj.here with
  | head a₀ =>
    have hF' : (if a₀.opened = true then some a₀.F else none) = some F := by
      have := a1
      unfold S.fork? at this
      rw [hh] at this
      exact this
    cases ho₀ : a₀.opened with
    | false =>
      rw [ho₀] at hF'
      exact nomatch hF'
    | true =>
      simp only [S.putTl, S.putFork, hh, ho₀, if_true] at eh e
      obtain rfl := VerifiableInference.Desc.First.Here.head.inj eh
      subst e
      refine ⟨tl, F, a₀, _, htl, a1, rfl, ho₀, rfl, ho, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, hf⟩
      · simp [S.fork?, e1]
      · simp [S.tl?, eT]
      · simp [S.lookHeard?, hh, ho₀]
      · simp [S.look?, hh, ho₀]
      · simp [S.funs?, hh, ho₀]
      · simp [S.link?, hh, ho₀]
  | lay a₀ =>
    simp [S.putTl, S.putFork, hh] at eh
  | att a₀ =>
    simp [S.putTl, S.putFork, hh] at eh
  | between =>
    simp [S.putTl, S.putFork, hh] at eh
  | fin a₀ =>
    simp [S.putTl, S.putFork, hh] at eh
  | mem a₀ =>
    simp [S.putTl, S.putFork, hh] at eh

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.headDigits_parts
