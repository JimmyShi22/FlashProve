-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CallsParts.lean: the kind "lookup" (K3): what each
reader of the verifier's state answers behind an accepting step of the description's own member at a
lookup on the calls, in terms of what it answers in front: the ledger's shape and the shape of what
was heard are given as code on the shape in front; every other reader answers as in front.
One theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: the shape of a ledger is `ledSh`
(Johnson/Desc/First/Shape/Parts.lean); the shape of a heard structure is `heardAll`
(Johnson/Desc/First/Shape/Tail.lean). The state bears no mark if `failed = none`.

What is shown.
  `calls_parts`: reader by reader, at the state sj' behind the step:
    fork?: its shape behind is `lookUpd` (Honest/K3/Shape/Ops.lean) of the face at its shape in
      front, by `hearVia_sh` (Honest/K3/Shape/Walk.lean).
    lookHeard?: its shape behind is `lookHeardSh` (Honest/K3/Shape/HeardOps.lean) of the lookup's
      shape, the ledger's count in front and its number of owed claims in front, by `hearVia_heard`
      (Honest/K3/Shape/HeardTop.lean).
    look?: the same in a layers' link and in an attention link; as in front in the head's link.
    As in front: tl?, funs?, link?, rowsOwed, st, out, check, book, roots, req.
    The state behind bears no mark. The sort of the link that is open stays: `CallsHere`
      (Honest/K3/Law/KeepsDefs.lean) says it.

Hypotheses that remain. The first five lines are those of `calls_here`
(Honest/K3/Law/Thread/StateHere.lean).
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the calls.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `h`: the member's step accepts from sj to sj'.
  `hSz`: the ledger in front has its three arrays at their size; this is a test on its shape
    (`sizedB`, Johnson/Desc/First/Shape/Parts.lean).

Imported: Johnson/Desc/First/Shape/Parts.lean and Johnson/Desc/First/Shape/Tail.lean.

Users. The theorem is for whoever carries a projection of the state onto its shape over that step,
component by component. Honest/K3/Law/Thread/CarriesCalls.lean imports this file; it calls
`calls_here` (StateHere.lean), not `calls_parts`.

Limits. From an acceptance alone: no statement of this file says that the step accepts. On the
verifier's side alone. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateHere
import Johnson.Desc.ProofFile.Honest.K3.Shape.Walk
import Johnson.Desc.ProofFile.Honest.K3.Shape.HeardTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ledSh heardAll sizedB sized_of_B)
open ProofFile.Honest.K3.Shape (lookUpd lookHeardSh hearVia_sh hearVia_heard)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **Reader by reader, behind the accepting step of the description's own member at a lookup on the
calls.** Conditional on what this file's head lists. No instance of these hypotheses is exhibited in
this file. -/
theorem calls_parts (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n))
    (hSz : ∀ F, sj.fork? = some F → sizedB (ledSh F) = true) :
    ∃ F H G, sj.fork? = some F ∧ CallsHere sj sj' H G ∧
      sj'.fork?.map ledSh = some (lookUpd (faceOf s.shape) (ledSh F)) ∧
      sj'.lookHeard?.map heardAll = some (lookHeardSh s.shape F.next F.owed.size) ∧
      ((∀ a, sj.here ≠ .head a) →
        sj'.look?.map heardAll = some (lookHeardSh s.shape F.next F.owed.size)) ∧
      ((∃ a, sj.here = .head a) → sj'.look? = sj.look?) ∧
      sj'.tl? = sj.tl? ∧ sj'.funs? = sj.funs? ∧ sj'.link? = sj.link? ∧
      sj'.rowsOwed = sj.rowsOwed ∧ sj'.st = sj.st ∧ sj'.out = sj.out ∧ sj'.check = sj.check ∧
      sj'.book = sj.book ∧ sj'.roots = sj.roots ∧ sj'.req = sj.req ∧ sj'.failed = none := by
  obtain ⟨F, H, G, a1, _, a5, hC, hf⟩ := calls_here o pol lay KL Fd Z Bs base ch A B O s hs hd lot
    m hb hbs hm hmp hpk ft sj sj' n rs c h
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _⟩ := site_facts _ _ x s hsx
  have hS := sized_of_B (hSz F a1)
  have e1 := (hearVia_sh hS f2 a5).2
  have e2 := hearVia_heard hS f2 a5
  refine ⟨F, H, G, a1, hC, ?_⟩
  rcases hC with ⟨a, hh, rfl⟩ | ⟨a, hh, rfl⟩ | ⟨a, hh, ho, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hf⟩
    · simp [S.fork?, e1]
    · simp [S.lookHeard?, e2]
    · intro _
      simp [S.look?, e2]
    · rintro ⟨b, hb'⟩
      rw [hh] at hb'
      exact nomatch hb'
    · simp [S.tl?, hh]
    · simp [S.funs?, hh]
    · simp [S.link?, hh]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hf⟩
    · simp [S.fork?, e1]
    · simp [S.lookHeard?, e2]
    · intro _
      simp [S.look?, e2]
    · rintro ⟨b, hb'⟩
      rw [hh] at hb'
      exact nomatch hb'
    · simp [S.tl?, hh]
    · simp [S.funs?, hh]
    · simp [S.link?, hh]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hf⟩
    · simp [S.fork?, ho, e1]
    · simp [S.lookHeard?, ho, e2]
    · intro hne
      exact absurd hh (hne a)
    · intro _
      simp [S.look?, hh, ho]
    · simp [S.tl?, hh, ho]
    · simp [S.funs?, hh, ho]
    · simp [S.link?, hh, ho]

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.calls_parts
