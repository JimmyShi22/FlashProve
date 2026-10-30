-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/AtSwitchReached.lean: UNDER THE HEAD P5J.AtMgA: WHAT THE LIBRARY's LAWS SAY OF
EVERY STATE WITHOUT A MARK THAT THE PROOF FILE's OWN FIRST CHAIN REACHES IN FRONT OF A LINK's CODE
SWITCH (border 14 l + 2, l < 25), gathered. A joining of laws; nothing is evaluated.

The family. Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (p, s) (Johnson/Top/H0/Walk/Reach.lean): the chain's
OWN blocks, not the wrapped ones.

  `AtSwitch Zp l s`: twelve fields in one structure: the chain stands between two links · a link's
    first call is due · the frame stands at link l · the codes and the frame's shape are the public
    part's, and its groups are that shape's · the carried rows have a written form for each mask
    row, and behind the first closing they bear the shape's two codes' numbers and two mask rows ·
    as many places in the book as messages · each message's place names a tree and a part that hold
    it · as many roots as trees, and tree j bears the number j and the source "own j" · the public
    part's codes and shape pass the library's test reqOk.
  **`atSwitch_reached`**: under the head, l < 25: every state without a mark that is reached at
    border 14 l + 2 has them.

By what. The member in front, "link l: laid", is tests alone (layFront,
Johnson/Desc/First/Walk/Frame.lean; layFront_ok, Johnson/Top/H0/Walk/FrameLaw.lean; IM.frame_of).
RecAll at every border under the tests on the plan (Meaning.K2.recAll_all, Johnson/IMR/AtReach.lean;
plans_at, PlansAtHead.lean). The book: bookHas_reached, bookFits_reached, bookInOrder_reached (the
same file).

Limits. That a state is reached at such a border is not shown. That no mark stands there is a
premise here; the library has it at these borders (IM.noMark_reach, Johnson/IMR/NoMarkReach.lean).
That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
(`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of
public files, in a side library. At the format's second hash function. Nothing on soundness,
completeness or hiding.
-/
import Johnson.IMR.AtReach
import Johnson.IMR.FinPin
import Johnson.IMR.MsgsPlaces
import Johnson.AtFull.Shape.PlansAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.Book (BookFits NumberedC)
open Johnson.Desc.First.Walk (firstDue)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- What holds of a state in front of link l's code switch. -/
structure AtSwitch (Zp : ProofFile.Pub) (l : Nat) (s : S) : Prop where
  here : s.here = .between
  due : firstDue s.check = true
  link : s.check.frame.link = l
  codes : s.st.codes = Zp.first.codes
  shape : s.check.frame.shape = Zp.first.shape
  groups : s.check.frame.groups = reqGroups Zp.first.shape
  forms : s.check.frame.rows.d.size = s.check.frame.rows.masks
  rows : l ≠ 0 → s.check.frame.rows.code = Zp.first.shape.code ∧
    s.check.frame.rows.maskCode = Zp.first.shape.maskCode ∧ s.check.frame.rows.masks = 2
  places : s.book.place.size = s.st.oracles.size
  fits : BookFits s.book
  order : NumberedC 0 (coreS s)
  ok : reqOk Zp.first.codes Zp.first.shape = true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Every state without a mark that is reached in front of a link's code switch.** -/
theorem atSwitch_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + 2) (p, s))
    (hu : s.failed = none) : AtSwitch Zp l s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hk : 14 * l + 2 ≤ (Meaning.K2.frontOf cF).length := by
    rw [Meaning.K2.front_len h.scope h.reads O]
    omega
  obtain ⟨-, rs, cols, f₀⟩ := hr.fold
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨LkF, f, bL, bB, bC, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr l hl
  obtain ⟨tm, Rm, Cm, fm⟩ := Meaning.K2.fold_back (k := 14 * l + 1) f₀
  obtain ⟨rsL, gsL, dl⟩ := Meaning.K2.fold_next iL fm f₀
  rw [dL] at dl
  have hlf := ((hlay tm s).1 dl).1
  rw [efl] at hlf
  obtain ⟨et, hB, hD, hL⟩ := Johnson.Desc.First.Walk.Law.layFront_ok hlf
  subst et
  have R := Meaning.K2.recAll_all h.scope h.reads O (plans_at h) hr hu
  have W := R.walk
  have hb : s.here = .between := by
    unfold S.atBetween at hB
    cases hh : s.here <;> rw [hh] at hB <;> first | rfl | cases hB
  refine ⟨hb, hD, hL, R.codes, W.shape, W.groups, W.rows.1, fun h0 => ?_,
    Meaning.K2.bookHas_reached O hr hk, Meaning.K2.bookFits_reached O hr hk,
    Meaning.K2.bookInOrder_reached O hr hk, R.ok⟩
  rcases W.rows.2 with e | e
  · exact absurd (hL.symm.trans e) h0
  · exact e

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.atSwitch_reached
