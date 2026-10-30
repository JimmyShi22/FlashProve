-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/OutSite.lean: conditional: behind the member's
acceptance the lookup's promise behind holds: at the state that the description's member leaves on
the played rounds, the Boolean test `k3OnOut` (Johnson/Desc/First/Look/K3Borders.lean) accepts, and
the mark is as in front. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there promise (the lookup's, behind), site, lot, member, seat,
ledger, mark and step without a round.

What is shown.
  `placeAt_digits`: the parameters at a place bear the sort at which they were asked.
  `heardAt_seat`, `fork_seat`: the library's readers of a state are those of the two seats.
  `onOut_oneQ`: the promise behind, from the sentence `OneQ` (Honest/K3/Law/MemberOne.lean) and the
    return of `hearV`.
  `joinedAt_out`: from `JoinedAt` (Honest/K3/Law/Joined.lean) at that sentence: the step's
    acceptance, with the promise behind it.
  `member_out_site`: at a site, with `member_yes_site` (Honest/K3/Law/MemberSite.lean): the member's
    step accepts on the played rounds, and behind it the lookup's promise holds and no mark stands.

Hypotheses that remain, in `member_out_site`: those that the head of MemberSite.lean lists.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hb`, `hbs`, `hm`, `hmp`: s is a site of the public part; b is one of the lot's
    sub-protocols, at the site's place; m is a member of the first chain's flat list, at that place.
  `hpk`: the member passes its test on the plan.
  `hT1`, `hT2`, `hT3`: three tests with code on public data: the face's own test; at the calls of a
    layers' link the shape is the layout's; at the digits, but for the head's, the lookup ends at
    the plan's number of slots in use.
  `hbase`, `hdraws`: in front: as many challenges were heard as the site says; the challenges pass
    the frame's test.
  `hL`, `hF`, `h0`, `hO`, `hs0`: in front: the ledger (`LedgerIn`, Honest/K3/Law/Top.lean); the
    seat's three readings (the ledger is open, nothing was heard, no row waits); the state bears no
    mark.
  `hHead`: at the digits of the head's link: `HeadBehind` (Honest/K3/Law/StatedMember.lean).
In the others: `hp`, `hd`, `ha`: the parameters make the shape h; their sort; the face is that
shape's. `hh`, `hQ`: (in `onOut_oneQ`) `hearV` returns; `OneQ` (Honest/K3/Law/MemberOne.lean). `H`:
(in `joinedAt_out`) `JoinedAt` (Honest/K3/Law/Joined.lean). `h`: (in `placeAt_digits`) `placeAt`
returns.

Users. Honest/K3/Law/Thread/FrontSite.lean calls `member_out_site`, `placeAt_digits` and
`fork_seat`; Honest/K3/Law/Thread/OnOutMember.lean imports this file.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Out
import Johnson.Desc.ProofFile.Honest.K3.Law.BehindHands
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf k3OnOut heardAt)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (P placeAt sameShape)

local notation "FS" => VerifiableInference.Desc.First.S

variable {V₁ W₁ X₁ W : Type}

/-- The parameters at a place bear the sort at which they were asked. Conditional on there being a
place. -/
theorem placeAt_digits {X : OnBytes.Model.Verify.Public} {i : Nat} {d : Bool} {p : P}
    (h : placeAt X i d = some p) : p.digits = d := by
  unfold placeAt at h
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- The library's reader of what was heard is the seat's. -/
theorem heardAt_seat {Cl : Type} (claim : Aff → Cl) (d : Bool) (t : FS) :
    heardAt d t = (seatOf claim d).heard t := by
  cases d <;> rfl

/-- Either seat reads the state's open ledger. -/
theorem fork_seat {Cl : Type} (claim : Aff → Cl) (d : Bool) (t : FS) :
    (seatOf claim d).fork t = t.fork? := by
  cases d <;> rfl

/-- **The lookup's promise behind, from the sentence on the state that the member leaves.**
Conditional on the place's shape and sort; the ledger in front; the return of `hearV`; and `OneQ`.
-/
theorem onOut_oneQ {Cl : Type} (claim : Aff → Cl) {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} (p : P)
    (h : Shape) (hp : p.shape = some h) (hd : p.digits = d) {F G : Fork} {x : List Fmt.RoundView}
      {g : HeardV}
    {s t : FS} (hL : LedgerIn (faceOf h) p.first F) (hh : hearV (faceOf h) F x = some (g, G))
    (hQ : OneQ claim X i d h s t g G) : k3OnOut p t = true ∧ t.failed = s.failed := by
  obtain ⟨g', c, hg, a1, a2, a3⟩ := oneQ_hands claim hQ
  exact ⟨onOut_of p h hp hL.sized hL.next hL.room hL.free hh hg t c
    (by rw [hd, heardAt_seat claim]; exact a1) (by rw [← fork_seat claim d]; exact a2), a3⟩

/-- **The step's acceptance, with the promise behind it.** Conditional on `JoinedAt` at the sentence
`OneQ`; the face is the shape's; the place's shape and sort; the ledger in front. -/
theorem joinedAt_out {Cl : Type} (claim : Aff → Cl) {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} (p : P)
    (h : Shape) (m : Block FS Cl) (a : At) (ha : a.face = faceOf h) (J : LookJobs W) (wit : W₁ → W)
    (v : Option V₁) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts) (st : FS)
      (F : Fork)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (hp : p.shape = some h) (hd : p.digits = d)
    (hL : LedgerIn a.face p.first F)
    (H : JoinedAt m a J wit v mid ds c p.first st F chain ft stored tree (OneQ claim X i d h st)) :
    ∃ y t, play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps m v c) ds [] mid = .ok y ∧
      m.step ft st (roundsOf y.1) [] = .ok (t, 0) ∧ k3OnOut p t = true ∧ t.failed = st.failed := by
  obtain ⟨y, t, g, G, h1, _, _, _, h5, h6, h7, _⟩ := H
  rw [ha] at h6 hL
  obtain ⟨k1, k2⟩ := onOut_oneQ claim p h hp hd hL h6 h7
  exact ⟨y, t, h1, h5, k1, k2⟩

/-- **At a site: the member's step accepts on the played rounds; behind it the lookup's promise
holds, and no mark stands.** Conditional on the hypotheses that the head of
Honest/K3/Law/MemberSite.lean lists. No instance of these hypotheses is exhibited in this file. -/
theorem member_out_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
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
    ∃ y t, play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_).steps m v c) ds [] mid = .ok y ∧
      m.step ft st (roundsOf y.1) [] = .ok (t, 0) ∧ k3OnOut s.p t = true ∧ t.failed = none := by
  have H := member_yes_site o pol lay KL Fd Z Bs base ch A B O s hs b m hb hbs hm hmp hpk hT1 hT2
    hT3 J
    wit v mid ds c st F hbase hdraws hL hF h0 hO hs0 hHead chain ft stored tree
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, f2, _, f4, _, f6, _, _⟩ := site_facts _ _ x s hsx
  obtain ⟨y, t, k1, k2, k3, k4⟩ := joinedAt_out K3Lot.ofForm s.p s.shape m s.at_ f6 J wit v mid ds c
    st F
    chain ft stored tree f2 ((placeAt_digits f1).trans f4.symm) hL H
  exact ⟨y, t, k1, k2, k3, k4.trans hs0⟩

#print axioms ProofFile.Honest.K3.Law.AtThr.placeAt_digits
#print axioms ProofFile.Honest.K3.Law.AtThr.heardAt_seat
#print axioms ProofFile.Honest.K3.Law.AtThr.fork_seat
#print axioms ProofFile.Honest.K3.Law.AtThr.onOut_oneQ
#print axioms ProofFile.Honest.K3.Law.AtThr.joinedAt_out
#print axioms ProofFile.Honest.K3.Law.AtThr.member_out_site

end ProofFile.Honest.K3.Law.AtThr
