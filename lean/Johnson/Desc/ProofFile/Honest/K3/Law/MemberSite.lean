-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/MemberSite.lean: the step of the description's own member
accepts on the played rounds, at a site: one theorem for every lookup of a public part (`lookSites`,
Honest/K3/Lot.lean). The form of the sub-protocol's decision is picked from the address, and the
public hypotheses of `member_one` (Honest/K3/Law/MemberOne.lean) are shown from the member's own
test on the plan and from tests with code. Conditional on the hypotheses listed below. Theorems.

Terms. Honest/K3/GLOSSARY.md ("address", "description", "member", "play", "site", "step").

What is shown.
  `site_facts`: what a site holds of the address that it was made at.
  `address_form`: an address of the lot's list: its link, its sort, its place.
  `lookSeat_rounds`, `fit_length`: the seated row has as many rounds as the verifier's text hears;
    so many entries has a list that the hearing goes by.
  `caller_head`, `caller_layers`, `caller_attention`: whose link it is, by the verifier's own three
    tests on the link's number.
  `site_block`, at a site: the lot's sub-protocol there has the form at the site's own link, sort
    and parameters; and, where the member's test on the plan accepts: the entries fit, several
    calls, its rounds and oracle messages.
  `site_behind`: the step behind the lookup returns: from two tests with code; at the head's digits
    from `HeadBehind`.
  `member_yes_site`: the main theorem.

Hypotheses that remain, in `member_yes_site`.
  `O`: the description's return (`IM.Open`).
  `hs`, `hb`, `hbs`, `hm`, `hmp`: the site, the lot's sub-protocol at its place, the member at that
    place.
  `hpk`: the member's test on the plan accepts.
  `hT1`, `hT2`, `hT3`: three tests with code on public data: the face's own test; at a layers'
    link's calls the shape is the layout's; at the digits, but for the head's, the lookup ends at
    the plan's number of slots in use.
  What stands in front: `hbase`: as many challenges heard as the site says; `hdraws`: the challenges
    pass the frame's test; `hL`: the ledger (`LedgerIn`); `hF`, `h0`, `hO`: the seat's three; `hs0`:
    no mark.
  `hHead`: at the digits of the head's link: `HeadBehind`, at every state that the seated decision
    leaves on as many rounds as the plan has entries on which `hearV` has returned.

In the theorems on the way: `hs`: `siteAt` returns the site (in `site_facts`); `hx`: the address is
one of the lot's list; `h`, `hm`: two planes at least; the entries fit; the verifier's tests on the
link's number (in `lookSeat_rounds`, `fit_length` and the three on the caller); `hnx`: (in
`site_behind`) the ledger's next slot is the place's first. `hSz`: (in `site_behind`) the ledger's
arrays have their size; in `member_yes_site` it is had out of `hL`.

Imported. It rests on two folders of theorems
(Honest/SumLaw/: on the masked sumcheck; Honest/Member/: on the member
at a lot's place), as the heads of Honest/K3/Law/Joined.lean and Honest/K3/Law/MemberAtSite.lean
say.

Users. This file is imported by Honest/K3/Law/LotOfSite.lean, Honest/K3/Law/SiteThere.lean
[not in this library], Honest/K3/Law/StatedAtLot.lean [not in this library],
Honest/K3/Law/Thread/MemberBack.lean, Honest/K3/Law/Thread/OutSite.lean,
Honest/K3/Law/Thread/SitePays.lean and Honest/K3/Law/Thread/ToyLetters.lean [not in this library].

Limits. No instance of the hypotheses together is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberOne
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanOkGives
import Johnson.Desc.ProofFile.Honest.K3.LotPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn Oracle)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG isHead pieceAt entriesV
  entriesFit theStated)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (P placeAt sameShape)
open ProofFile.Honest.AtPlace (member_alone)

local notation "FS" => VerifiableInference.Desc.First.S

variable {V₁ W₁ X₁ W : Type}

/-! ## 1 Sites and addresses -/

/-- What a site holds of the address that it was made at.
Conditional on the site having been made there. -/
theorem site_facts (X : OnBytes.Model.Verify.Public) (ps : List Spot) (x : Nat × Bool × Place)
    (s : Site)
    (hs : siteAt X ps x = some s) :
    placeAt X x.1 x.2.1 = some s.p ∧ s.p.shape = some s.shape ∧ s.link = x.1 ∧ s.digits = x.2.1 ∧
      s.at_.place = x.2.2 ∧ s.at_.face = faceOf s.shape ∧
      s.caller = (callerOf X.p4 X.NGr x.1).1 ∧ s.group = (callerOf X.p4 X.NGr x.1).2 := by
  unfold siteAt at hs
  obtain ⟨p, hp, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨h, hh, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨n, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  dsimp only at hs
  split at hs
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hs
    exact ⟨hp, hh, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain rfl := Option.some.inj hs
    exact ⟨hp, hh, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An address of the lot's list names its link and its sort in its place.
Conditional on its standing in the list. -/
theorem address_form (Z : Pub) (x : Nat × Bool × Place) (hx : x ∈ K3Lot.addresses Z) :
    x.2.2.link = some x.1 ∧ x.2.2.piece = pieceAt Z.p.X x.1 x.2.1 := by
  unfold K3Lot.addresses at hx
  obtain ⟨j, _, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
  exact ⟨rfl, rfl⟩

/-- The seated row has as many rounds as the verifier's text hears.
Conditional on two planes or more. -/
theorem lookSeat_rounds (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At)
    (h : 2 ≤ a.face.planes) :
    (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).rounds = (entriesV a.face).length := by
  unfold Placed.rounds
  rw [foldl_add_eq_sum (fun p : Part V₁ W₁ X₁ => p.moves.length), proverSideOfLookupInChainAtOneOwner_moves,
    rounds_stages a.face h, Nat.zero_add]

/-- A list of entries that the hearing goes by has as many entries as the verifier's text.
Conditional on the test `entriesFit`. -/
theorem fit_length (f : LFace) (es : List Fmt.Entry) (h : entriesFit f es = true) :
    es.length = (entriesV f).length := by
  unfold entriesFit at h
  have e := congrArg List.length (of_decide_eq_true (by simpa using h) :
    (es.map fun e => { e with work := 0 }) = entriesV f)
  rwa [List.length_map] at e

/-! ## 2 Whose link -/

/-- The head's link. Conditional on the verifier's own test on the link's number. -/
theorem caller_head (X : OnBytes.Model.Verify.Public) (i : Nat) (h : isHead X i = true) :
    (callerOf X.p4 X.NGr i).1 = .head := by
  unfold isHead at h
  unfold callerOf
  simp only [h, if_true]

/-- A layers' link, and its group. Conditional on the verifier's own two tests on
the link's number. -/
theorem caller_layers (X : OnBytes.Model.Verify.Public) (i : Nat) (h : isHead X i = false)
    (hm : (i % (if X.p4 then 2 else 1) == 0) = true) :
    callerOf X.p4 X.NGr i = (.layers, i / (if X.p4 then 2 else 1)) := by
  unfold isHead at h
  unfold callerOf
  simp only [h, hm, if_true, Bool.false_eq_true, if_false]

/-- An attention link, and its group. Conditional on the verifier's own two tests on
the link's number. -/
theorem caller_attention (X : OnBytes.Model.Verify.Public) (i : Nat) (h : isHead X i = false)
    (hm : ¬ (i % (if X.p4 then 2 else 1) == 0) = true) :
    callerOf X.p4 X.NGr i = (.attention, i / (if X.p4 then 2 else 1)) := by
  unfold isHead at h
  unfold callerOf
  simp only [h, hm, Bool.false_eq_true, if_false]

/-! ## 3 The lot's sub-protocol at a site -/

/-- **The lot's sub-protocol at a site's place**: its decision has the form at the site's own link,
sort and parameters; and, where the member's test on the plan accepts, the plan's entries are those
that the hearing at the site's face goes by, there are several calls, and the sub-protocol's rounds
and oracle messages are these entries'. Conditional on the description's return and on the member's
test on the plan. -/
theorem site_block (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase)
    (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site) (hs : s ∈ lookSites Z)
    (b m : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : b.place = s.at_.place)
    (hm : m ∈ ch.blocksInOrder) (hmp : m.place = b.place) (hpk : m.planOk = true) :
    FormAt K3Lot.ofForm Z.p.X s.link s.digits s.p b ∧
      entriesFit s.at_.face (s.p.entries.getD []) = true ∧ 1 < s.shape.NC ∧
      b.rounds = (s.p.entries.getD []).map declOf ∧
      b.oracles = (s.p.entries.getD []).map fun _ => [] := by
  unfold lookSites at hs
  obtain ⟨x, hx, hsx⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, f5, f6, _, _⟩ := site_facts _ _ x s hsx
  obtain ⟨x1, x2⟩ := address_form Z x hx
  have hb' : b ∈ K3Lot.hear Z := by rw [← lot_blocks Z Bs.G₀]; exact hb
  unfold K3Lot.hear at hb'
  obtain ⟨x', hx', hst⟩ := List.mem_filterMap.1 hb'
  have hpx' := theStated_place _ _ _ _ _ _ b hst
  have hxx : x'.2.2 = x.2.2 := by rw [← hpx', hbs, f5]
  -- The form.
  obtain ⟨i, d, p, g1, g2, g3, Fm⟩ := formAt_of (theStated_decides _ _ _ _ _ _ b hst)
  rw [hxx] at g1 g2
  obtain rfl : x.1 = i := Option.some.inj (x1.symm.trans g1)
  obtain rfl : x.2.1 = d := pieceAt_inj _ _ _ _ (x2.symm.trans g2)
  obtain rfl : s.p = p := Option.some.inj (f1.symm.trans g3)
  -- The plan.
  obtain ⟨hk, hal⟩ := k3_alone Z x' hx'
  have hL : K3Lot.lot Z ∈ onlineFirstChainBlockTables Z := by simp [onlineFirstChainBlockTables]
  obtain ⟨y, hy, hlaid⟩ := member_alone o pol lay KL Fd Z Bs base ch A B O (K3Lot.lot Z) hL b hb
    (by rw [hpx', hk]; decide) (by rw [hpx']; exact hal) m hm hmp
  obtain ⟨i', d', p', hS, k1, k2, k3, k4, k5, k6, _, k8, k9⟩ :=
    theStated_plan _ _ _ _ _ _ b hst (member_planOk hy hlaid hpk)
  rw [hxx] at k1 k2
  obtain rfl : x.1 = i' := Option.some.inj (x1.symm.trans k1)
  obtain rfl : x.2.1 = d' := pieceAt_inj _ _ _ _ (x2.symm.trans k2)
  obtain rfl : s.p = p' := Option.some.inj (f1.symm.trans k3)
  obtain rfl : s.shape = hS := Option.some.inj (f2.symm.trans k4)
  refine ⟨by rw [f3, f4]; exact Fm, by rw [f6]; exact k5, k6, k8, ?_⟩
  rw [k9, k8]
  show ((s.p.entries.getD []).map fun e => ({ entry := e } : Fmt.DeclaredRound)).map
    (fun _ => ([] : List Oracle)) = _
  rw [List.map_map]
  rfl

/-! ## 4 The step behind the lookup, at a site -/

/-- **What stands behind the lookup returns, at a site.** Conditional on two tests with code on
public data (the second and third of Honest/K3/LotPublic.lean), each asked at its own sort of site;
on the first ledger's arrays having their size and its count of slots being the place's; and, at the
digits of the head's link, on `HeadBehind`. -/
theorem site_behind (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (n : Nat) (st : FS) (F : Fork)
    (hSz : OnBytes.PscRun.Sized F) (hnx : F.next = s.p.first)
    (hT2 : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (hHead : s.digits = true → s.caller = .head → ∀ (rs : List Fmt.RoundView) (g : HeardV) (G : Fork)
      (s' : FS),
      rs.length = n → hearV (faceOf s.shape) F rs = some (g, G) →
      decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t) :
    BehindReturns K3Lot.ofForm Z.p.X s.link s.digits s.p s.shape n st F := by
  unfold lookSites at hs
  obtain ⟨x, hx, hsx⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := site_facts _ _ x s hsx
  rw [← f3] at f7 f8
  intro rs g G g' s' hl hh hg hd a1 a2
  obtain ⟨pt, form, hk, hsz⟩ := keys_of_hearV s.shape hh
  obtain ⟨g'', hg'', hsh, _⟩ := toHeard_returns s.shape g pt form hk hsz (countsOk_of_shape f2)
  obtain rfl : g'' = g' := Option.some.inj (hg''.symm.trans hg)
  have hG : G.next = s.p.first + (faceOf s.shape).slots := by rw [hearV_next _ hSz hh, hnx]
  refine behind_exists K3Lot.ofForm Z.p.X s.link s.digits s.shape _ s' a1 hsh a2 hG ?_ ?_ ?_ ?_
  · intro hd0 hH hmod
    have hc : s.caller = .layers := by rw [f7, caller_layers _ _ hH hmod]
    simpa [hd0, hc] using hT2
  · intro hd1 hH hmod hp hg1
    have hc := caller_layers Z.p.X s.link hH hmod
    have hc1 : s.caller = .layers := by rw [f7, hc]
    have hc2 : s.group = s.link / (if Z.p.X.p4 then 2 else 1) := by rw [f8, hc]
    have hu : usedAt Z.p.X s = some hp.used := by
      unfold usedAt
      rw [hc1]
      show (Z.p.X.G[s.group]?).map (·.used) = _
      rw [hc2, hg1]
      rfl
    rw [f6] at hT3
    simpa [hd1, hc1, hu] using hT3
  · intro hd1 hH hmod a hg1
    have hc := caller_attention Z.p.X s.link hH hmod
    have hc1 : s.caller = .attention := by rw [f7, hc]
    have hc2 : s.group = s.link / (if Z.p.X.p4 then 2 else 1) := by rw [f8, hc]
    have hu : usedAt Z.p.X s = some a.nMsg := by
      unfold usedAt
      rw [hc1]
      show (Z.p.X.A[s.group]?).map (·.nMsg) = _
      rw [hc2, hg1]
      rfl
    rw [f6] at hT3
    simpa [hd1, hc1, hu] using hT3
  · intro hd1 hH
    exact hHead hd1 (by rw [f7, caller_head _ _ hH]) rs g G s' hl hh hd

/-! ## 5 The theorem -/

/-- **At every lookup of a public part: the frame's play of the seated row at the description's own
member goes through, and the member's step on the played rounds accepts.** Conditional on what this
file's head lists under "Hypotheses that remain". No instance of the hypotheses together is
exhibited in this file. -/
theorem member_yes_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
      (hs : s ∈ lookSites Z)
    (b m : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : b.place = s.at_.place)
    (hm : m ∈ ch.blocksInOrder) (hmp : m.place = b.place) (hpk : m.planOk = true)
    (hT1 : s.at_.face.ok = true)
    (hT2 : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts)
    (st : FS) (F : Fork) (hbase : mid.st.heard.length = s.at_.base)
    (hdraws : drawsFit ((s.p.entries.getD []).map declOf) ds = true)
    (hL : LedgerIn s.at_.face s.p.first F)
    (hF : (seatOf K3Lot.ofForm s.digits).fork st = some F)
    (h0 : ((seatOf K3Lot.ofForm s.digits).heard st).isNone = true)
    (hO : ((seatOf K3Lot.ofForm s.digits).owed st).noneWaits = true) (hs0 : st.failed = none)
    (hHead : s.digits = true → s.caller = .head → ∀ (rs : List Fmt.RoundView) (g : HeardV) (G : Fork)
      (s' : FS),
      rs.length = (s.p.entries.getD []).length → hearV (faceOf s.shape) F rs = some (g, G) →
      decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt m s.at_ J wit v mid ds c s.p.first st F chain ft stored tree
      (OneQ K3Lot.ofForm Z.p.X s.link s.digits s.shape st) := by
  obtain ⟨Fm, hfit, hN, hr, ho⟩ :=
    site_block o pol lay KL Fd Z Bs base ch A B O s hs b m hb hbs hm hmp hpk
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _, _, _, f6, _, _⟩ := site_facts _ _ x s hsx
  have hrd : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit s.at_).rounds =
      b.rounds.length := by
    rw [lookSeat_rounds _ J wit s.at_ (two_le_planes_of_ok _ hT1), hr, List.length_map,
      fit_length _ _ hfit]
  exact member_one o pol lay KL Fd Z Bs base ch A B O b m hb hm hmp K3Lot.ofForm Z.p.X s.link
    s.digits
    s.p s.shape Fm s.at_ f6 J wit v (s.p.entries.getD []) hbs hr ho mid ds c hrd st F
    ⟨hT1, hbase, hfit, hdraws⟩ hL f2 hN hF h0 hO
    (site_behind Z s hs _ st F hL.sized hL.next hT2 hT3 hHead) hs0 chain ft stored tree

#print axioms ProofFile.Honest.K3.Law.site_facts
#print axioms ProofFile.Honest.K3.Law.address_form
#print axioms ProofFile.Honest.K3.Law.lookSeat_rounds
#print axioms ProofFile.Honest.K3.Law.fit_length
#print axioms ProofFile.Honest.K3.Law.caller_head
#print axioms ProofFile.Honest.K3.Law.caller_layers
#print axioms ProofFile.Honest.K3.Law.caller_attention
#print axioms ProofFile.Honest.K3.Law.site_block
#print axioms ProofFile.Honest.K3.Law.site_behind
#print axioms ProofFile.Honest.K3.Law.member_yes_site

end ProofFile.Honest.K3.Law
