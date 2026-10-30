-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindSite.lean: the honest side of the kind "lookup"
(K3): BEHIND THE MEMBER'S ACCEPTING STEP AT A LOOKUP ON THE DIGITS, THE THREAD'S CLAUSE ON THE FORM
HOLDS ONE BORDER ON. From the premises on the place (`SiteAt`) and the frame's own sentence on a
step (`Stepped`) to `Form (b + 1)`. Theorems.

  `lot_planOk`          where the member's test on the plan accepts, so does the test of the
                        lookups' own sub-protocol at its place
  `lot_stated_at`         that sub-protocol is the stated one at the site's place
  `place_link`          the site's place names the site's link and sort
  `placeAt_of_look`     the parameters at a place, of the public data's own entry for it
  `form_site_digits`    **the theorem**

What is laid in, and by what: the stated sub-protocol and its test on the plan (the two lemmas
above); its accepting step, from the member's (Honest/K3/Law/MemberAtSite.lean); the library's
promise
in front, from the thread (Honest/K3/Law/Thread/SiteThr.lean); no mark behind the step, and the
input
unturned (Honest/K3/Law/Thread/Accepted.lean, Honest/K3/Law/BehindHands.lean).

`SiteAt` has the field half: the list of halves holds, at the site's place, the elder row `proverSideOfLookupInChainAtOneOwner`
at these summands. Who pays the field, each at the fast summands and under hypotheses on the list:
where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot` (HalfAtSite.lean
[not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean [not in this library]); where it
holds a lot with the halves of `theLotInst` at the public part: `half_like_ok`, `half_field_like`
(HalfOfLotLike.lean [not in this library]). A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. CONDITIONAL ON the description's return; `SiteAt`; `HeadReturns`; the thread in front; the
frame's sentence on the step; and the premises on public data and on the promise's meaning that
Honest/K3/Law/Thread/BehindDigitsPaid.lean's theorem lists, which are handed through. No instance of
these hypotheses is exhibited in this file. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindDigitsPaid
import Johnson.Desc.ProofFile.Honest.K3.Law.BehindHands

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn Oracle)
open VerifiableInference.Desc.K3 (pieceAt theStated)
open VerifiableInference.Desc.First (ModelPart pubSets openSets start shift sameStand bookFit pubStep
  pubRowM pubOfItems stepOpen rowOf)
open VerifiableInference.Desc.First.Look (P Sent lookAt placeAt)
open VerifiableInference.Desc.Sound (MsgT Frame)
open VerifiableInference.OnPublicFiles (K3At K3Letters digTableB k3Like InOrderReads HeldReads)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.AtPlace (member_alone)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 The lookups' own sub-protocol at a site -/

/-- Where the member's test on the plan accepts, so does the test of the lookups' own sub-protocol
at
its place. CONDITIONAL ON the description's return and on the member's test. -/
theorem lot_planOk (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (b m : Block FS ProofFile.Cl)
    (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = b.place)
    (hpk : m.planOk = true) : b.planOk = true := by
  have hb' : b ∈ K3Lot.hear Z := by rw [← lot_blocks Z Bs.G₀]; exact hb
  unfold K3Lot.hear at hb'
  obtain ⟨x', hx', hst⟩ := List.mem_filterMap.1 hb'
  have hpx' := theStated_place _ _ _ _ _ _ b hst
  obtain ⟨hk, hal⟩ := k3_alone Z x' hx'
  have hL : K3Lot.lot Z ∈ onlineFirstChainBlockTables Z := by simp [onlineFirstChainBlockTables]
  obtain ⟨y, hy, hlaid⟩ := member_alone o pol lay KL Fd Z Bs base ch A B O (K3Lot.lot Z) hL b hb
    (by rw [hpx', hk]; decide) (by rw [hpx']; exact hal) m hm hmp
  exact member_planOk hy hlaid hpk

/-- The lookups' own sub-protocol at a place is the stated one at that place. CONDITIONAL ON its
standing in the lot's list. -/
theorem lot_stated_at (Z : Pub) (G : Ground) (b : Block FS ProofFile.Cl)
    (hb : b ∈ (K3Lot.lot Z).blocks G) :
    theStated K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X Z.first.codes Z.first.shape b.place =
      some b := by
  obtain ⟨x, hx⟩ := lot_stated Z G b hb
  rw [theStated_place _ _ _ _ _ _ b hx]
  exact hx

/-- A site's place names the site's link and sort. CONDITIONAL ON the site. -/
theorem place_link (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) :
    s.at_.place.link = some s.link ∧ s.at_.place.piece = pieceAt Z.p.X s.link s.digits := by
  unfold lookSites at hs
  obtain ⟨x, hx, hsx⟩ := List.mem_filterMap.1 hs
  obtain ⟨_, _, f3, f4, f5, _, _, _⟩ := site_facts _ _ x s hsx
  obtain ⟨x1, x2⟩ := address_form Z x hx
  rw [f3, f4, f5]
  exact ⟨x1, x2⟩

/-- The parameters at a place, of the public data's own entry for it. CONDITIONAL ON that entry. -/
theorem placeAt_of_look {X : OnBytes.Model.Verify.Public} {i : Nat} {d : Bool}
    {x : VerifiableInference.Desc.First.Look.Place} (h : lookAt X i d = some x) :
    placeAt X i d = some (P.ofPlace (OnBytes.Params.settingOf X.P.frame) d x) := by
  unfold placeAt
  rw [h]
  rfl

/-! ## 2 The theorem -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **Behind the member's accepting step at a lookup on the digits the thread's clause on the form
holds one border on.** CONDITIONAL ON what this file's head lists. No instance of these hypotheses
is exhibited in this file. -/
theorem form_site_digits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
    {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
    {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
    (hH : HeadReturns L b Z s) (hdg : s.digits = true) {blk : Block FS ProofFile.Cl}
    (hb : L.bs[b]? = some blk) {k : Coins Bk} {st st' : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn}
    (hA : Thr L.thread b k st m E) (hd : drawsFit blk.rounds ds = true)
    (hSt : L.thread.Stepped blk k st m E ds y cols st')
    (hIO : InOrderReads L.MgP) (hHe : HeldReads L.MgP) (Fr : Frame) (y₀ : Fr.E.Str) (a' : Place)
    (hk : L.ps[b]? = some s.at_.place) (hk1 : L.ps[b + 1]? = some a')
    (hfitS : sameStand L.links s.at_.place a' = true) (sub : ModelPart)
    (hsub : L.links[s.link]? = some sub) (hpcT : s.at_.place.piece = 7 + shift sub)
    (hTab : digTableB L.MgP.more L.links L.ps b s.at_.place s.link (shift sub) = true)
    {x : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt Z.p.X s.link true = some x)
    (told : List (List Oracle)) (hbf : bookFit L.N L.ps told = true) (hn : told[b]? = some [])
    (hObj : L.mgP.pub (.formsIn s.link (7 + shift sub) "objects")
      (L.pubOf m.st.input.x, st') = true)
    (hRest : ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
          (pubRowM L.mgP.more L.links s.at_.place) ++
        pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
          (VerifiableInference.Desc.First.rowOf L.links s.at_.place)),
      k3Like r = false → r ≠ .formsIn s.link (7 + shift sub) "objects" →
        L.mgP.pub r (L.pubOf m.st.input.x, st') = true)
    (othersP : ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
        (pubRowM L.mgP.more L.links s.at_.place),
      (∀ j, r ≠ .left j) → (∀ j, r ≠ .leftOn j) → L.mgP.pubP r (L.pubOf m.st.input.x, st')) :
    L.thread.Form (b + 1) k st' y.2 := by
  have hmem : blk ∈ ch.blocksInOrder := by rw [← hS.flat]; exact List.mem_of_getElem? hb
  have hpl := hS.place blk hb
  -- what the member's step has left
  obtain ⟨_, hy2, _, _, g, G, _, _, _, hQ, _⟩ :=
    stepped_look (seated_site hS) (joins_site o pol lay KL Fd base A B O hS hH) hb hA hd hSt
  obtain ⟨_, _, _, _, _, hfail⟩ := oneQ_hands K3Lot.ofForm hQ
  have hf : st'.failed = none := hfail.trans (failed_of_thr L hA)
  have hm : y.2.st.input = m.st.input := by rw [hy2]
  -- the lookups' own sub-protocol: stated; its test on the plan; its accepting step
  have hB := lot_stated_at Z Bs.G₀ lot hS.inLot
  rw [hS.lotPlace] at hB
  have hOk := lot_planOk o pol lay KL Fd Z Bs base ch A B O lot blk hS.inLot hmem hpl
    (hS.plan blk hb)
  obtain ⟨_, _, _, _, hiff⟩ :=
    memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hS.inLot blk hmem hpl
  have hst := ((hiff _ _ _ _ _ _).1 hSt.2).1
  -- the place; the promise in front
  obtain ⟨hi, hpc⟩ := place_link Z s hS.site
  rw [hdg] at hpc
  have hq := hS.lookIn
  rw [hdg] at hq
  have hOnIn := onIn_thr L hS.k3At (placeAt_of_look hlook) hq hA
  exact form_digits_paid L hS.k3At hIO hHe Fr y₀ K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.first.codes
    Z.first.shape s.at_.place a' lot hB hOk hk hk1 hfitS s.link hi sub hsub hpcT hpc hTab hlook hA
    hm hOnIn _ _ _ _ hst hf told hbf hn hObj hRest othersP

end

#print axioms ProofFile.Honest.K3.Law.AtThr.lot_planOk
#print axioms ProofFile.Honest.K3.Law.AtThr.lot_stated_at
#print axioms ProofFile.Honest.K3.Law.AtThr.place_link
#print axioms ProofFile.Honest.K3.Law.AtThr.placeAt_of_look
#print axioms ProofFile.Honest.K3.Law.AtThr.form_site_digits

end ProofFile.Honest.K3.Law.AtThr
