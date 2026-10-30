-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LeftThr.lean: the honest side of the kind "lookup" (K3):
what stands behind the member's acceptance, in the thread's own letters, with the letters "planes"
and "keys" given values: from the first chain's thread in front of the description's own member at a
lookup's place and that member's step (`Thread.Stepped`, Honest/Thread/Pays.lean). One definition;
theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `Left R planes keys g G` (Honest/K3/Law/LookLeftOf.lean)
is stated at two letters, planes and keys; here they are `Spec.planesOf` and `Spec.keysOf`
(Honest/K3/Law/SpecLawful.lean) of `siteData` (Honest/K3/Law/AtSite.lean). The specification's
summands are those of `specFill`, the summands that fold tables those of `fastFill`
(Honest/K3/LotRow.lean).

What is shown.
  `LeftAt`: (definition) what is concluded, under a name.
  `left_thr_spec`: `LeftAt` at the specification's summands.
  `left_thr_fast`: `LeftAt` at the summands that fold tables.

Hypotheses that remain. Both theorems are conditional on all of these.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hS`, `hH`: `SiteAt` and `HeadReturns` (Honest/K3/Law/Thread/SiteThr.lean).
  `hb`, `hA`: the thread's member at the border b; the thread's relation in front (`Thr`).
  `hd`: the challenges pass their test (`drawsFit`).
  `hSt`: the member's step (`Thread.Stepped`).
  `hSet`: the input no longer moves from the challenges in front of the lookup on (`Ask.Settled` at
    the site's number of rounds in front, Honest/K3/WitLaw.lean).
  `hM`: the relation after the challenge holds at the structure's keys and bits (`Data.Mid`,
    Johnson/HonestTrace/LookDefs.lean).

Imported. The theorems rest on the files under Honest/SumLaw/ and Honest/Member/.

How the proof goes. The summands that fold tables are lawful because they agree, at the run, with
the specification's (`FastLaw.site_agree`, Honest/K3/FastLaw/Sites.lean; `agreeLawful`,
Honest/K3/Law/Agree.lean).

Users. Honest/K3/Law/Thread/LeftAtCalls.lean calls `left_thr_fast`.

`SiteAt` has the field half: the list of halves holds, at the lookup's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. `LeftAt`, the end of both theorems, spells the elder row's parts too,
in the type of the coins c and in the return of `lendRow`; it names no list of halves. Who pays the
field, each at the fast summands and under hypotheses on the list: where the list of lots holds
`theLot` or `theLotInst` itself: `half_field_theLot` (HalfAtSite.lean [not in this library]),
`half_field_theLotInst` (HalfOfLotInst.lean [not in this library]); where it holds a lot with the
halves of `theLotInst` at the public part: `half_like_ok`, `half_field_like` (HalfOfLotLike.lean
[not in this library]). A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. No instance of these hypotheses is exhibited in this file. The nearest thing to one is
Honest/K3/Law/JoinedMember.lean [not in this library]: like hypotheses are met together at a
synthetic place, by evaluation. What is left has its values at mask entries that are the coins
spent: which coin the verifier's world reads under which slot is not stated here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.AtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV)
open VerifiableInference.Desc.First.Look (Sent)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3Letters)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok W₀' Rc' Xi' Tr' : Type}
  {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT}
  {b : Nat} {Z : Pub} {Bs : PureBase} {ch : Chain FS ProofFile.Cl} {s : Site} {lot : Block FS ProofFile.Cl}
  {wit : Local W₀ Rc Xi Tr → Ask} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **What stands behind the member's acceptance at a lookup of a public part**, at summands J: no
column was read; what the play leaves (the columns opened stand as they stood in front); c is the
coins that the book lent the row; F is the ledger that the state in front holds; the course's first
slot is the parameters' own; `hearV` has returned on the played rounds from F; the state that the
member's step leaves is tied to what was heard and to the ledger behind the hearing (`OneQ`,
Honest/K3/Law/MemberOne.lean); there is a course with the row's coins at which what was heard is the
run's, with its points, the invariant holds behind the last stage, and `Left` holds at the planes'
values of the structure's own bits and the extension of the structure's own keys. -/
def LeftAt (chain : Nat) (k : Coins Bk) (blk : Block FS ProofFile.Cl) (Z : Pub) (s : Site)
    (J : LookJobs Ask)
    (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo)
    (cols : List OpenedColumn) : Prop :=
  cols = [] ∧ y.2 = ⟨{ m.st with heard := m.st.heard ++ ds }, m.loc ++ ds,
    m.seen ++ roundsOf y.1, m.opened⟩ ∧
    ∃ (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr)
      (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts)
      (F : Fork) (g : HeardV) (G : Fork) (c' : (t : Stage) → StageCoins s.at_ t),
      lendRow Bk (Bk.rowsOf chain) (k.look chain) blk.place
        (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts 0 =
          .ok c ∧
      (seatOf K3Lot.ofForm s.digits).fork st = some F ∧
      hearV s.at_.face F (roundsOf y.1) = some (g, G) ∧
      OneQ K3Lot.ofForm Z.p.X s.link s.digits s.shape st st' g G ∧
      CoinsAre (V := Unit) (courseAt s.at_ J s.p.first wit m ds c')
        (unlift (X := Xo) (fun (_ : Local W₀ Rc Xi Tr) => ()) wit
          (lookRow ⟨ptsOf, pointsAt⟩ J s.at_) c) ∧
      HeardIs (courseAt s.at_ J s.p.first wit m ds c') g ∧
      PointsAgree s.at_.face g s.at_.base (m.st.heard ++ ds) ∧
      Inv (courseAt s.at_ J s.p.first wit m ds c') (stages s.at_.face).length G ∧
      Left (courseAt s.at_ J s.p.first wit m ds c')
        (Spec.planesOf (siteData s (wit m.st.input) m.st.heard ds))
        (Spec.keysOf (siteData s (wit m.st.input) m.st.heard ds)) g G

/-- **At the specification's summands.** Conditional on the hypotheses that the head of this file
lists. No instance of these hypotheses is exhibited in this file. -/
theorem left_thr_spec (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument) (pol lay KL : ByteArray)
    (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B)
    (hS : SiteAt L b Z Bs ch s lot ((specFill (Rc := Rc') src).jobs s).asked wit D Lk)
    (hH : HeadReturns L b Z s) {blk : Block FS ProofFile.Cl} (hb : L.bs[b]? = some blk) {k : Coins Bk}
      {st st' : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn} (hA : Thr L.thread b k st m E)
    (hd : drawsFit blk.rounds ds = true) (hSt : L.thread.Stepped blk k st m E ds y cols st')
    (hSet : Ask.Settled s.at_.base (wit m.st.input))
    (hM : (siteData s (wit m.st.input) m.st.heard ds).Mid) :
    LeftAt L.thread.chain k blk Z s ((specFill (Rc := Rc') src).jobs s).asked wit st st' m ds y cols
      := by
  obtain ⟨h1, h2, c, F, g, G, hlend, hFk, hh, hQ, c', hc, hHd, P, hI, hLeft⟩ :=
    stepped_look (seated_site hS) (joins_site o pol lay KL Fd base A B O hS hH) hb hA hd hSt
  have hFit := fit_of_stands (stands_of_thr (seated_site hS) hb hA hd)
    ((specFill (Rc := Rc') src).jobs s).asked s.p.first wit c'
  exact ⟨h1, h2, c, F, g, G, c', hlend, hFk, hh, hQ, hc, hHd, P, hI, hLeft _ _
    (Spec.lawful_site (Rc := Rc') src Z s hS.site _ rfl rfl hFit hSet hM)⟩

/-- **The same at the summands that fold tables**, conditional on the same hypotheses. No instance
of these hypotheses is exhibited in this file. -/
theorem left_thr_fast (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument) (pol lay KL : ByteArray)
    (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B)
    (hS : SiteAt L b Z Bs ch s lot ((fastFill (Rc := Rc') src).jobs s).asked wit D Lk)
    (hH : HeadReturns L b Z s) {blk : Block FS ProofFile.Cl} (hb : L.bs[b]? = some blk) {k : Coins Bk}
      {st st' : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn} (hA : Thr L.thread b k st m E)
    (hd : drawsFit blk.rounds ds = true) (hSt : L.thread.Stepped blk k st m E ds y cols st')
    (hSet : Ask.Settled s.at_.base (wit m.st.input))
    (hM : (siteData s (wit m.st.input) m.st.heard ds).Mid) :
    LeftAt L.thread.chain k blk Z s ((fastFill (Rc := Rc') src).jobs s).asked wit st st' m ds y cols
      := by
  obtain ⟨h1, h2, c, F, g, G, hlend, hFk, hh, hQ, c', hc, hHd, P, hI, hLeft⟩ :=
    stepped_look (seated_site hS) (joins_site o pol lay KL Fd base A B O hS hH) hb hA hd hSt
  have hFs := fit_of_stands (stands_of_thr (seated_site hS) hb hA hd)
    ((specFill (Rc := Rc') src).jobs s).asked s.p.first wit c'
  have hLs := Spec.lawful_site (Rc := Rc') src Z s hS.site
    (courseAt s.at_ ((specFill (Rc := Rc') src).jobs s).asked s.p.first wit m ds c') rfl rfl hFs
      hSet hM
  have hAg := FastLaw.site_agree (Rc := Rc') src Z s hS.site
    (courseAt s.at_ ((specFill (Rc := Rc') src).jobs s).asked s.p.first wit m ds c') rfl rfl hFs
  exact ⟨h1, h2, c, F, g, G, c', hlend, hFk, hh, hQ, hc, hHd, P, hI, hLeft _ _
    ((agreeLawful Ask _ _ _ _ hFs hAg).2 hLs)⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.left_thr_spec
#print axioms ProofFile.Honest.K3.Law.AtThr.left_thr_fast
