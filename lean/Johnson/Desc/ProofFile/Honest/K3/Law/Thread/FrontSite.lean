-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/FrontSite.lean: conditional: from the lookup's promise
in front of a lookup's sub-protocol to its promise behind, through the member's acceptance. The
hypotheses of the theorem of Honest/K3/Law/MemberSite.lean on the verifier's state in front are
shown from `FrontOk` (Honest/K3/Law/Thread/Front.lean), which the lookup's promise in front
(`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean) gives. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there promise (the lookup's, in front and behind), site, lot,
member, seat, ledger, mark and step without a round.

What is shown.
  `ledgerIn_of_front`: the four clauses of `FrontOk` on the ledger are `LedgerIn`
    (Honest/K3/Law/Top.lean).
  `front_seatOf`: `k3OnIn` gives `FrontOk` at the seat of the parameters' own sort.
  `front_face`: the shape that `FrontOk` names at a site's parameters is the site's, and the site's
    face is that shape's.
  `member_yes_front`, `member_out_front`: `member_yes_site` (MemberSite.lean) and `member_out_site`
    (Honest/K3/Law/Thread/OutSite.lean), from `FrontOk`.
  `member_in_out`: from `k3OnIn s.p st` and no mark: the member's step accepts on the played rounds,
    and `k3OnOut s.p t` and no mark hold behind.

Hypotheses that remain, in `member_in_out`.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hb`, `hbs`, `hm`, `hmp`: s is a site of the public part; b is one of the lot's
    sub-protocols, at the site's place; m is a member of the first chain's flat list, at that place.
    (b stands in no conclusion; `lot_of_site`, Honest/K3/Law/LotOfSite.lean, gives such a b from `O`
    and `hs`.)
  `hpk`: the member passes its test on the plan.
  `hT1`, `hT2`, `hT3`: three tests with code on public data: the face's own test; at the calls of a
    layers' link the shape is the layout's; at the digits, but for the head's, the lookup ends at
    the plan's number of slots in use. (The first is stated at every site of every public part,
    without a further hypothesis, by `face_ok_site`, Johnson/AtFull/Shape/FaceAtSites.lean, a file
    which this file does not
    import.)
  `hin`, `hs0`: in front: the lookup's promise `k3OnIn`; the state bears no mark.
  `hbase`, `hdraws`: in front: as many challenges were heard as the site says; the challenges to
    come pass the frame's test.
  `hHead`: at the digits of the head's link: `HeadBehind` (Honest/K3/Law/StatedMember.lean). It is
    asked at the ledger that the state in front holds.
In the others: `Fo`: `FrontOk`; `h`: (in `front_seatOf`) the lookup's promise in front, `k3OnIn`.

Imported. These theorems stand over two folders, Honest/SumLaw/ and Honest/Member/, as the head of
MemberSite.lean says.

Users. Honest/K3/Law/Thread/SiteThr.lean and Honest/K3/Law/Thread/AtThreadSite.lean call
`front_seatOf` and `member_yes_front`; Honest/K3/Law/Thread/LeavesReady.lean [not in this library]
imports this file.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Front
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OutSite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf k3OnIn k3OnOut Seat)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (P sameShape)

local notation "FS" => VerifiableInference.Desc.First.S

variable {V₁ W₁ X₁ W : Type}

/-- The four clauses on the ledger. Conditional on `FrontOk`. -/
theorem ledgerIn_of_front {Cl : Type} {seat : Seat FS Cl} {p : P} {h : Shape} {s : FS} {F : Fork}
    (Fo : FrontOk seat p h s F) : LedgerIn (faceOf h) p.first F :=
  ⟨Fo.sized, Fo.next, Fo.room, Fo.free⟩

/-- The lookup's promise in front gives `FrontOk` at the seat of the parameters' own sort.
Conditional on that promise. -/
theorem front_seatOf {Cl : Type} (claim : Aff → Cl) {p : P} {s : FS} (h : k3OnIn p s = true) :
    ∃ hh F, FrontOk (seatOf claim p.digits) p hh s F := by
  cases hd : p.digits with
  | false => exact front_calls claim hd h
  | true => exact front_digits claim hd h

/-- The shape that `FrontOk` names at a site's parameters is the site's, and the site's face is that
shape's. Conditional on the site and on `FrontOk`. -/
theorem front_face (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) {st : FS} {h : Shape} {F : Fork}
    (Fo : FrontOk (seatOf K3Lot.ofForm s.digits) s.p h st F) :
    h = s.shape ∧ s.at_.face = faceOf s.shape := by
  unfold lookSites at hs
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs
  obtain ⟨_, f2, _, _, _, f6, _, _⟩ := site_facts _ _ x s hsx
  exact ⟨Option.some.inj (Fo.shape.symm.trans f2), f6⟩

/-- **The theorem of Honest/K3/Law/MemberSite.lean, from `FrontOk`.** Conditional on what this
file's head lists, with `FrontOk` for the lookup's promise. No instance of these hypotheses is
exhibited in this file. -/
theorem member_yes_front (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase)
    (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site) (hs : s ∈ lookSites Z)
    (b m : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : b.place = s.at_.place)
    (hm : m ∈ ch.blocksInOrder) (hmp : m.place = b.place) (hpk : m.planOk = true)
      (hT1 : s.at_.face.ok = true)
    (hT2 : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts) (st : FS)
    (hbase : mid.st.heard.length = s.at_.base)
    (hdraws : drawsFit ((s.p.entries.getD []).map declOf) ds = true) (hs0 : st.failed = none)
    {h : Shape} {F : Fork} (Fo : FrontOk (seatOf K3Lot.ofForm s.digits) s.p h st F)
    (hHead : s.digits = true → s.caller = .head → ∀ (rs : List Fmt.RoundView) (g : HeardV) (G : Fork)
      (s' : FS),
      rs.length = (s.p.entries.getD []).length → hearV (faceOf s.shape) F rs = some (g, G) →
      decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt m s.at_ J wit v mid ds c s.p.first st F chain ft stored tree
      (OneQ K3Lot.ofForm Z.p.X s.link s.digits s.shape st) := by
  obtain ⟨rfl, hf⟩ := front_face Z s hs Fo
  exact member_yes_site o pol lay KL Fd Z Bs base ch A B O s hs b m hb hbs hm hmp hpk hT1 hT2 hT3 J
    wit v
    mid ds c st F hbase hdraws (by rw [hf]; exact ledgerIn_of_front Fo) Fo.fork Fo.heard Fo.owed hs0
    hHead chain ft stored tree

/-- **The theorem of Honest/K3/Law/Thread/OutSite.lean, from `FrontOk`.** Conditional on the same.
No instance of these hypotheses is exhibited in this file. -/
theorem member_out_front (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase)
    (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site) (hs : s ∈ lookSites Z)
    (b m : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : b.place = s.at_.place)
    (hm : m ∈ ch.blocksInOrder) (hmp : m.place = b.place) (hpk : m.planOk = true)
      (hT1 : s.at_.face.ok = true)
    (hT2 : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts) (st : FS)
    (hbase : mid.st.heard.length = s.at_.base)
    (hdraws : drawsFit ((s.p.entries.getD []).map declOf) ds = true) (hs0 : st.failed = none)
    {h : Shape} {F : Fork} (Fo : FrontOk (seatOf K3Lot.ofForm s.digits) s.p h st F)
    (hHead : s.digits = true → s.caller = .head → ∀ (rs : List Fmt.RoundView) (g : HeardV) (G : Fork)
      (s' : FS),
      rs.length = (s.p.entries.getD []).length → hearV (faceOf s.shape) F rs = some (g, G) →
      decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t)
    (ft : Nat) :
    ∃ y t, play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_).steps m v c) ds [] mid = .ok y ∧
      m.step ft st (roundsOf y.1) [] = .ok (t, 0) ∧ k3OnOut s.p t = true ∧ t.failed = none := by
  obtain ⟨rfl, hf⟩ := front_face Z s hs Fo
  exact member_out_site o pol lay KL Fd Z Bs base ch A B O s hs b m hb hbs hm hmp hpk hT1 hT2 hT3 J
    wit v
    mid ds c st F hbase hdraws (by rw [hf]; exact ledgerIn_of_front Fo) Fo.fork Fo.heard Fo.owed hs0
    hHead 0 ft (fun _ _ => none) fun _ => none

/-- **From the lookup's promise in front to its promise behind.** Conditional on what this file's
head lists under "Hypotheses that remain". The hypothesis at the head's digits is asked at the
ledger that the state in front holds. No instance of these hypotheses is exhibited in this file. -/
theorem member_in_out (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase)
    (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site) (hs : s ∈ lookSites Z)
    (b m : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : b.place = s.at_.place)
    (hm : m ∈ ch.blocksInOrder) (hmp : m.place = b.place) (hpk : m.planOk = true)
      (hT1 : s.at_.face.ok = true)
    (hT2 : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts) (st : FS)
    (hbase : mid.st.heard.length = s.at_.base)
    (hdraws : drawsFit ((s.p.entries.getD []).map declOf) ds = true) (hs0 : st.failed = none)
    (hin : k3OnIn s.p st = true)
    (hHead : s.digits = true → s.caller = .head → ∀ (F : Fork) (rs : List Fmt.RoundView) (g : HeardV)
      (G : Fork)
      (s' : FS), st.fork? = some F → rs.length = (s.p.entries.getD []).length →
      hearV (faceOf s.shape) F rs = some (g, G) →
      decideVia (seatOf K3Lot.ofForm s.digits) s.p st rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t)
    (ft : Nat) :
    ∃ y t, play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_).steps m v c) ds [] mid = .ok y ∧
      m.step ft st (roundsOf y.1) [] = .ok (t, 0) ∧ k3OnOut s.p t = true ∧ t.failed = none := by
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, _, _, f4, _, _, _, _⟩ := site_facts _ _ x s hsx
  have hd : s.p.digits = s.digits := (placeAt_digits f1).trans f4.symm
  obtain ⟨hh, F, Fo⟩ := front_seatOf K3Lot.ofForm hin
  rw [hd] at Fo
  exact member_out_front o pol lay KL Fd Z Bs base ch A B O s hs b m hb hbs hm hmp hpk hT1 hT2 hT3 J
    wit v
    mid ds c st hbase hdraws hs0 Fo
    (fun h1 h2 rs g G s' => hHead h1 h2 F rs g G s'
      ((fork_seat K3Lot.ofForm s.digits st).symm.trans Fo.fork))
    ft

#print axioms ProofFile.Honest.K3.Law.AtThr.ledgerIn_of_front
#print axioms ProofFile.Honest.K3.Law.AtThr.front_seatOf
#print axioms ProofFile.Honest.K3.Law.AtThr.front_face
#print axioms ProofFile.Honest.K3.Law.AtThr.member_yes_front
#print axioms ProofFile.Honest.K3.Law.AtThr.member_out_front
#print axioms ProofFile.Honest.K3.Law.AtThr.member_in_out

end ProofFile.Honest.K3.Law.AtThr
