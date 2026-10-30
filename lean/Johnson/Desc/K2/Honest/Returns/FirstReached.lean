-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FirstReached.lean: AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH
INTO A LATER GROUP, IN THE GOALS' SCOPE, THE FRAME's NEXT CALL IS A FIRST ONE (`LinkPlain.first`,
Returns/LinkSent.lean): from "in scope", "the files are read", the opening and the place alone. SO
THE TEXT's OWN FRONT RETURNS THERE, WITH NO PREMISE BEYOND THE FIVE IN FRONT AND THE PLACE.
Statements with their proofs: calls.

HOW. Behind the closing and the shutting of segment l the open segment's frame has "next = first"
(the library's `frame_walk_link`). The sub-protocol "segment l: cleared" lays the open segment's
state of the calls as the walk's (`framesOf_clear`); "segment l + 1: laid" hands the state on as it
is (`layFront_ok`).

  `first_behind_laid` from the fold's return at the cut 14 (l + 1) + 2, l < 24
  `link_first_reached` at a state reached over the wrapped list at 14 (m + 1) + 2, m < 23
  `link_front_paid` so there are L and Q with: the text's front returns `frontAt s L Q`
  `link_front_own` and at the frame's own segment L and group Q
  `link_tables_own` `link_tables_at` (Returns/PinReached.lean) without its premise "first"
  `link_draws_own` `link_draws_first` (Returns/LinkReached.lean) without its premise "first"

By, all the library's: `frame_of` (Johnson/IMR/FrameSeat.lean) · `framesOf_clear`
(Johnson/IMR/GroupTail.lean) · `frame_walk_link`, `At.opn` (Johnson/IMR/FrameAll.lean) · `entry_at`,
`entry_at_zero` (Johnson/IMR/FrameEntry.lean) · `fold_back`, `fold_next`
(Johnson/IMR/FoldTools.lean) · `fold_cut` (Johnson/IMR/GroupRest.lean) · `layFront_ok`
(Johnson/Top/H0/Walk/FrameLaw.lean) · `reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean).

Limits. "Reached" is: over the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN
MET TOGETHER BY NOBODY HERE: NO MEMBER. `link_tables_own` keeps the three named tests on the public
part; `link_draws_own` keeps the entry's test at the plan's own list and the rounds that fit. The
finish's front is not touched. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.PinReached
import Johnson.IMR.FrameAll
import Johnson.IMR.GroupTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit foldBlocks Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (rounds par9)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.Desc.First.Walk.Law (layFront_ok)
open Meaning.K2 (Opn frame_walk_link entry_at entry_at_zero framesOf_clear fold_back fold_next
  fold_cut)
open P1K2 (Prep Nums numsAt prepOf)
open IM (k2P)
open _root_.Tw.K2 (firstFront)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **Behind "laid" of segment l + 1 the frame's next call is a first one.** -/
theorem first_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.check.frame.next = .first := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  -- "segment l + 1: laid" hands the state on
  obtain ⟨_, _, bL, _, _, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr (l + 1) (by omega)
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 14 * (l + 1) + 1) f₀
  obtain ⟨rsL, gsL, dl⟩ := fold_next iL fm f₀
  rw [dL] at dl
  have hlf := ((hlay tm t₀).1 dl).1
  rw [efl] at hlf
  obtain ⟨et, -⟩ := layFront_ok hlf
  -- "segment l: cleared" lays the open segment's state of the calls as the walk's
  obtain ⟨Lk, g, _, _, bC, -, hlen, hg, -, -, -, hclr, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  rw [hlen, show 14 * l + 7 + 7 = 14 * (l + 1) by omega] at iC
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * (l + 1)) fm
  obtain ⟨rsC, gsC, dc⟩ := fold_next iC fu fm
  rw [dC] at dc
  have hck := (framesOf_clear hfs g (List.mem_of_getElem? hg) u tm ((hclr u tm).1 dc).1).1
  -- in front of "cleared" the open segment's frame is the closed one
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 11
    (by rw [show 14 * l + 3 + 11 = 14 * (l + 1) by omega]; exact fu)
  obtain ⟨t₃, r₃, c₃, g₃⟩ := fold_cut (k := 14 * l + 3 + 2) 9
    (by rw [show 14 * l + 3 + 2 + 9 = 14 * (l + 1) by omega]; exact fu)
  obtain ⟨t₅, r₅, c₅, g₅⟩ := fold_cut (k := 14 * l + 3 + 4) 7
    (by rw [show 14 * l + 3 + 4 + 7 = 14 * (l + 1) by omega]; exact fu)
  obtain ⟨f', H⟩ : ∃ f', Opn l f' t₁ := by
    rcases Nat.eq_zero_or_pos l with rfl | h1
    · obtain ⟨f', hA, -⟩ := entry_at_zero hS hR O f₁
      exact ⟨f', hA.opn⟩
    · obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_back (k := 14 * l + 2) f₁
      obtain ⟨_, f', -, hA, -⟩ := entry_at hS hR O h1 h24 f₂ f₁
      exact ⟨f', hA.opn⟩
  obtain ⟨rows, L, hL, hLf, -⟩ := (frame_walk_link hS hR O h24 (n₃ := t₃.st.oracles.size)
    (n₅ := t₅.st.oracles.size) (fun t r q h => by rw [g₃] at h; cases h; rfl)
    (fun t r q h => by rw [g₅] at h; cases h; rfl) f₁ H).2 1 (by omega) u Ru Cu
    (by rw [show 14 * l + 3 + 10 + 1 = 14 * (l + 1) by omega]; exact fu)
  rw [et, hck]
  unfold S.live
  rw [hL]
  show L.check.frame.next = .first
  rw [hLf]
  rfl

/-- **`LinkPlain.first` at a reached state.** -/
theorem link_first_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    s.check.frame.next = .first := by
  obtain ⟨-, rs, cols, hf⟩ := (reach_raw hr).fold
  exact first_behind_laid hS hR O (by omega) hf

/-- **So the text's own front returns there.** -/
theorem link_front_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    ∃ L Q, firstFront s.st s.check.frame = .ok (frontAt s L Q) :=
  link_front_reached hS hR O hF hpl h23 hP hn hr (link_first_reached hS hR O h23 hr)

theorem link_front_own (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    {L : Params.ReqLink} {Q : ReqGroup}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    firstFront s.st s.check.frame = .ok (frontAt s L Q) :=
  link_front_at hS hR O hF hpl h23 hP hn hr (link_first_reached hS hR O h23 hr) hL hQ

/-- `link_tables_at` without "first". -/
theorem link_tables_own (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    {L : Params.ReqLink} {Q : ReqGroup}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    ∀ o ∈ (switchKept (frontAt s L Q).f.rows).toList,
      ∀ r ∈ ((frontAt s L Q).st.oracles.getD o default).sampleRows.toList,
        (∀ t ∈ r.terms.toList,
          t.v.pairs.length = (frontAt s L Q).st.tableBits o .main ∧ Own.InOrder t.v) ∧
          ∀ u ∈ r.units.toList, u.index < 2 ^ (frontAt s L Q).st.tableBits o .main :=
  link_tables_at hS hR O hF hpl hy hcut hB h23 hP hn hr (link_first_reached hS hR O h23 hr) hL hQ

/-- `link_draws_first` without "first". -/
theorem link_draws_own (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (he : planOk1 none n.sent (par9 (k2P Z a nm .link n)).eSeed = true)
    (h : roundsFit (rounds (k2P Z a nm .link n)) [r₁, r₂] = true) :
    ∃ x, firstFront s.st s.check.frame = .ok x ∧
      (∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a nm .link n).logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length = (sendingAt (k2P Z a nm .link n) x).seeds *
        ((sendingAt (k2P Z a nm .link n) x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ w ∈ K1.seedsOf (sendingAt (k2P Z a nm .link n) x) r₁, isZeroE w.2 = false :=
  link_draws_first hS hR O hF hpl h23 hP hn hr (link_first_reached hS hR O h23 hr) a nm r₁ r₂ he h

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.first_behind_laid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_first_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_front_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_front_own
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_tables_own
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_draws_own
