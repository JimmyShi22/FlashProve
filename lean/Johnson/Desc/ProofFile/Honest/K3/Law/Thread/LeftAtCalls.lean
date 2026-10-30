-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LeftAtCalls.lean: the honest side of the kind "lookup"
(K3): one statement on the honest thread, behind the accepting step of the member at a lookup on the
calls: the hypotheses of `bracket_of_left` (Honest/K3/Law/Thread/JoinBracket.lean
[not in this library]), all but `MasksAre` (Honest/K3/Law/Statements.lean) and the later ledger, at
one course, together with what the verifier's state then holds: as heard, the very structure; as its
ledger, the very ledger behind the hearing. One definition; theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: R is the course `courseAt s.at_ J s.p.first wit m ds c'`
(Honest/K3/Law/Top.lean); D is the data `siteData s (wit m.st.input) m.st.heard ds`
(Honest/K3/Law/AtSite.lean); planes is `Spec.planesOf D` (Honest/K3/Law/SpecLawful.lean).

Why. For a call of `bracket_of_left` at `keysG` (Honest/K3/Law/KeysAreKvG.lean) on K4's honest side
(no file of this library makes that call) one statement of the lookup's files was asked for: "there
are R planes D gV G g' with" nine clauses. Six of the nine stood among the conjuncts of `LeftAt`
(Honest/K3/Law/Thread/LeftThr.lean), two of them in the seat's own readers at a state between; one
stood in Honest/K3/Law/KeysTie.lean; two had not been stated by name.

What is shown.
  `via_split`: the library's `hearVia` is `hearV`, then `toHeard`: so where both have returned from
    one ledger on the same rounds, what they return agrees.
  `CallsLeft`: (definition) what is concluded, under a name; the shape h is a letter.
  `left_at_calls`: the composition, for arbitrary letters of the thread, at the site's own shape.
  `CallsLeft.shape`: the same at a shape that is the site's.
  `left_at_layers`: on the calls of a group's layers, at the seated filling's own reader: at the
    shape X.layers.y.fo, and the data's keys are the joint vector of `keysG`.
  `left_at_layers_head`: the same at the letters `lettersHead` (Honest/Thread/FirstHead.lean) under
    the library's hypothesis `P5J.AtMgA`, at the border borderOf s.link s.digits.

The nine clauses, in the order in which they were asked, and where each stands in `CallsLeft` and
`left_at_layers`.
  (1) toHeard h (toHeardG gV) = some g'.
  (2) R.f.parts = [h.v].
  (3) HeardIs R gV.
  (4) PointsAgree R.f gV R.a.base (R.t.heard ++ R.ds).
  (5) Left R planes (Spec.keysOf D) gV G.
  (6) D.v = h.v.
  (7) The keys of D: the second half of `left_at_layers`.
  (8) st'.lookHeard? = some g'.
  (9) st'.fork? = some G.
Besides, for a caller that wants `MasksAre`: c, the coins that the book lent the row, and `CoinsAre`
at them, which is the hypothesis of `masksAre_of_spent` (Honest/K3/Law/SpentFlat.lean
[not in this library]); and F, the ledger that the state in front holds, whose next slot is the
course's first (F.next = s.p.first: from `calls_here`, Honest/K3/Law/Thread/StateHere.lean, behind
the same step), which a use of that theorem wants besides.

How the proof goes. The member's step (`Thread.Stepped`, Honest/Thread/Pays.lean) holds the
sub-protocol's own accepting step on the played rounds. Behind such a step `member_back_cEnd`
(Honest/K3/Law/Thread/CEndBelow.lean) has: `hearVia` returned (H, G₂) from the ledger in front, and
the state behind holds H as heard and G₂ as its ledger. `LeftAt` has: `hearV` returned (gV, G) from
the ledger in front on the same rounds. There is one ledger in front; so by `via_split` toHeard … =
some H and G₂ = G. The state between and the step without a round, of which `OneQ`
(Honest/K3/Law/MemberOne.lean) speaks, are not needed. `HeadReturns`
(Honest/K3/Law/Thread/SiteThr.lean), which `left_thr_fast` assumes, is empty at a lookup on the
calls: three lines inside the proof. The same stands by name as `headReturns_calls` in
Honest/K3/Law/Thread/BehindSiteCalls.lean, which
is not imported, so that less lies beneath.

Hypotheses that remain, and what is known of where each is shown. At `left_at_layers_head`, by the
hypothesis's own letter; the line `hSet` is of `left_at_calls` alone.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). An instance of it at each of
    the two named sets of public files stands in the library's side files:
    `headMember_zFull` (AtFullSide/Top/HeadMemberAtFull.lean)
    and `headMember_zGap`
    (AtFullSide/Top/HeadMemberAtGap.lean).
  `hsite`: s ∈ lookSites Zp. Under `P5J.AtMgA` a site is there at every link on the calls:
    `site_calls_head` (Honest/K3/Law/Thread/SiteThereHead.lean).
  `hd`, `hc`: on the calls; a layers' link: public data of the site.
  `hB`: `ShapeIsFs` (Honest/K3/LotPublic.lean): a test with code gives it (`shapeIsFs`, there); that
    test was evaluated at the small example alone, as far as this file's writers knew. It stands
    beside the field shapeIs of `SiteRest` because that test (the library's `sameShape`,
    Johnson/Desc/First/Look/LookQuiet.lean) compares seven numbers of the two shapes, not the
    shapes: it does not give s.shape = X.layers.y.fo.
  `R`: `SiteRest` (Honest/K3/Law/Thread/SiteAtLetters.lean), of seven fields, in the next six lines.
  `R.inLot`, `R.lotPlace`: `lot_at_site` (Honest/K3/Law/Thread/LotAtSite.lean) shows them from one
    public test.
  `R.half`: which half the prover's list holds at the place. By a lemma on the first chain's halves
    in the files under Honest/Thread/, with `theLot_kind`
    (Honest/K3/Law/LotKind.lean) and its like of the other kinds.
  `R.fits`: a test with code on public data.
  `R.ok`: `face_ok_site` (Johnson/AtFull/Shape/FaceAtSites.lean)
    states it at every site
    of every public part;
    it is not imported here.
  `R.shapeIs`: a test with code on public data.
  `R.usedIs`: empty at the calls.
  `hb`, `hA`, `hdr`, `hSt`: the member; the thread's relation in front; the challenges' test; the
    member's step. These are for the files under Honest/Thread/ to show.
  `hSet`: `Ask.Settled` (Honest/K3/WitLaw.lean) at the site's number of rounds in front of the
    lookup: from so many challenges on the input no longer moves. It is a hypothesis of
    `left_at_calls` alone, where the reader of the input is a letter. At `left_at_layers` and
    `left_at_layers_head`, where it is the seated filling's own, it is no hypothesis:
    `askOf_settled` (Honest/K3/WitLaw.lean) shows it; the one condition of that theorem speaks of
    lookups on the digits.
  `hM`: `Data.Mid` (Johnson/HonestTrace/LookDefs.lean): the relation after the challenge at the
    structure's keys and bits. It is the honest witness's own property, and it is not shown here at
    a real witness. A way to it is stated in the files under Honest/K3/Law/ and is not connected
    here: `mid_of_meets` (Honest/K3/Law/MeetsMid.lean) gives `Mid` from a hypothesis on keys and
    bits; `ownG_meets` (Honest/K3/Law/WitOwnerFull.lean) gives that hypothesis at the own sources'
    layers, under named hypotheses on the trace and the public part. No lemma of this file ends at
    this file's own term.
  `O`, `hS`: (in `left_at_calls`, `left_at_layers`) the description returns (`IM.Open`); `SiteAt`
    (Honest/K3/Law/Thread/SiteThr.lean): hypotheses of `left_thr_fast`.
  `hp`, `hv`, `hh`: (in `via_split`) the parameters make the shape h; `hearVia` and `hearV` return.
    `C`, `e`: (in `CallsLeft.shape`) `CallsLeft` at h; h is h'.
  The local notation "LH" in the last statement is `lettersHead` at `h` and at twelve letters more.

Imported. Beneath this file lie, among others:
  Honest/Thread/First,
    FirstAt, HeadForm, HeardLaw, MadeLaw, PaysLaw, Riders; Honest/BookOf, ForKinds, Sum, SumToy;
  Honest/Frame, Side, Law/Cut, Law/Play;
  Honest/SumLaw/Law, LawEnds,
    Statement, Terms, Toy; Honest/Member/AtLot, InSegment;
  under Johnson/HonestTrace/: DigitsAtTrace,
    FromCells, LookAtDigits, LookCube, LookDefs, LookJobs, LookRows, LookSum;
  Johnson/Desc/K9/Honest/SlotsLive.

Users. Honest/K3/Law/Thread/LeftAtCallsMid.lean imports this file.

Limits. No instance of these hypotheses is exhibited in this file. No thread, no step and no witness
is shown at which the hypotheses hold together. At the calls alone; the keys' clause at a layers'
link alone. `left_at_layers_head` holds at the full size alone. `MasksAre` is not concluded: it
wants the frame's form on the mask row. That s.group is half the link's number is not
stated.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LeftThr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CEndBelow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateHere
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.KeysTie
import Johnson.Desc.ProofFile.Honest.K3.Law.SiteShapes
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open OnBytes.Model.Forest (Shape)
open OnBytes.Ends (jointKey)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn Strs)
open VerifiableInference.Desc.K3 (HeardV hearV toHeard toHeardG faceOf seatCalls)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First.Look (P Sent)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (K3Letters)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Letters lettersHead Script WtF)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 The two hearings -/

/-- **Where both have returned from one ledger on the same rounds, they agree.** Conditional on the
parameters' shape and on both returns. No instance of these hypotheses is exhibited in this file. -/
theorem via_split {p : P} {h : Shape} {F G G₂ : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    {H : OnBytes.Model.Forest.Heard} (hp : p.shape = some h)
    (hv : hearVia p F rs = some (H, G₂)) (hh : hearV (faceOf h) F rs = some (g, G)) :
    toHeard h (toHeardG g) = some H ∧ G₂ = G := by
  unfold hearVia at hv
  rw [hp] at hv
  simp only at hv
  split at hv
  · rw [hh] at hv
    have hv' : (toHeard h (toHeardG g)).map (fun g' => (g', G)) = some (H, G₂) := hv
    obtain ⟨g', hg', e⟩ := Option.map_eq_some_iff.1 hv'
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    exact ⟨by rw [hg', e1], e2.symm⟩
  · exact nomatch hv

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells' Tok W₀' Rc' Xi' Tr' : Type}

/-! ## 2 What is concluded -/

/-- **What stands behind the member's acceptance at a lookup on the calls**, at the shape h: the
coins that the book lent the row, and that they are the course's; the ledger in front, whose next
slot is the course's first; the clauses (1) to (6), (8) and (9) of the list in the head of this
file. -/
def CallsLeft (chain : Nat) (k : Coins Bk) (blk : Block FS ProofFile.Cl) (s : Site) (J : LookJobs Ask)
    (wit : Local W₀ Rc Xi Tr → Ask) (h : Shape) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn) : Prop :=
  ∃ (c : RowCoins
      (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts)
    (c' : (t : Stage) → StageCoins s.at_ t) (F : Fork) (gV : HeardV) (G : Fork)
    (g' : OnBytes.Model.Forest.Heard),
    lendRow Bk (Bk.rowsOf chain) (k.look chain) blk.place
      (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts 0 =
        .ok c ∧
    CoinsAre (V := Unit) (courseAt s.at_ J s.p.first wit m ds c')
      (unlift (X := Xo) (fun (_ : Local W₀ Rc Xi Tr) => ()) wit
        (lookRow ⟨ptsOf, pointsAt⟩ J s.at_) c) ∧
    st.fork? = some F ∧ F.next = s.p.first ∧
    toHeard h (toHeardG gV) = some g' ∧
    (courseAt s.at_ J s.p.first wit m ds c').f.parts = [h.v] ∧
    HeardIs (courseAt s.at_ J s.p.first wit m ds c') gV ∧
    PointsAgree (courseAt s.at_ J s.p.first wit m ds c').f gV
      (courseAt s.at_ J s.p.first wit m ds c').a.base
      ((courseAt s.at_ J s.p.first wit m ds c').t.heard ++
        (courseAt s.at_ J s.p.first wit m ds c').ds) ∧
    Left (courseAt s.at_ J s.p.first wit m ds c')
      (Spec.planesOf (siteData s (wit m.st.input) m.st.heard ds))
      (Spec.keysOf (siteData s (wit m.st.input) m.st.heard ds)) gV G ∧
    (siteData s (wit m.st.input) m.st.heard ds).v = h.v ∧
    st'.lookHeard? = some g' ∧ st'.fork? = some G

/-- The same at a shape that is the site's. Conditional on the sentence and the equation.
No instance of these hypotheses is exhibited in this file. -/
theorem CallsLeft.shape {chain : Nat} {k : Coins Bk} {blk : Block FS ProofFile.Cl} {s : Site}
    {J : LookJobs Ask} {wit : Local W₀ Rc Xi Tr → Ask} {h h' : Shape} {st st' : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {ds : List Fmt.Drawn}
    (C : CallsLeft chain k blk s J wit h st st' m ds) (e : h = h') :
    CallsLeft chain k blk s J wit h' st st' m ds := e ▸ C

/-! ## 3 The composition -/

variable {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells' Tok MsgT}
  {b : Nat} {Z : Pub} {Bs : PureBase} {ch : Chain FS ProofFile.Cl} {s : Site} {lot : Block FS ProofFile.Cl}
  {wit : Local W₀ Rc Xi Tr → Ask} {D : Sent} {Lk : K3Letters Cells' Tok}

/-- **The composition, for arbitrary letters of the thread.** Conditional on the hypotheses of
`left_thr_fast` but for `HeadReturns`, and on the site being on the calls. No instance of these
hypotheses is exhibited in this file. -/
theorem left_at_calls (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument) (pol lay KL : ByteArray)
    (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B)
    (hS : SiteAt L b Z Bs ch s lot ((fastFill (Rc := Rc') src).jobs s).asked wit D Lk)
    (hd : s.digits = false) {blk : Block FS ProofFile.Cl} (hb : L.bs[b]? = some blk) {k : Coins Bk}
    {st st' : FS} {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn}
    (hA : Thr L.thread b k st m E) (hdr : drawsFit blk.rounds ds = true)
    (hSt : L.thread.Stepped blk k st m E ds y cols st')
    (hSet : Ask.Settled s.at_.base (wit m.st.input))
    (hM : (siteData s (wit m.st.input) m.st.heard ds).Mid) :
    CallsLeft L.thread.chain k blk s ((fastFill (Rc := Rc') src).jobs s).asked wit s.shape st st'
      m ds := by
  have hH : HeadReturns L b Z s := by
    intro h1
    rw [hd] at h1
    exact nomatch h1
  obtain ⟨_, _, c, F, g, G, c', hlend, hFk, hh, _, hc, hHd, hP, _, hLeft⟩ :=
    left_thr_fast src o pol lay KL Fd base A B O hS hH hb hA hdr hSt hSet hM
  have hs' := hS.site
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _, _, _, f6, _, _⟩ := site_facts _ _ x s hsx
  have hmem : blk ∈ ch.blocksInOrder := by
    rw [← hS.flat]
    exact List.mem_of_getElem? hb
  obtain ⟨F₂, H, G₂, a1, a2, a3, a4, _, _⟩ :=
    member_back_cEnd o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
      hmem (hS.place blk hb) (hS.plan blk hb) _ st st' _ _ _ hSt.2
  rw [hd] at hFk
  have hF1 : st.fork? = some F := hFk
  have hF2 : st.fork? = some F₂ := a1
  obtain rfl : F = F₂ := Option.some.inj (hF1.symm.trans hF2)
  obtain ⟨F₃, _, _, d1, d2, _, _, _⟩ :=
    calls_here o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
      hmem (hS.place blk hb) (hS.plan blk hb) _ st st' _ _ _ hSt.2
  obtain rfl : F = F₃ := Option.some.inj (hF1.symm.trans d1)
  have hnext : F.next = s.p.first := by simpa using d2
  rw [f6] at hh
  obtain ⟨b1, rfl⟩ := via_split f2 a2 hh
  have hparts : s.at_.face.parts = [s.shape.v] := by
    rw [f6]
    rfl
  have hok : (faceOf s.shape).ok = true := by
    rw [← f6]
    exact hS.ok
  have hv : (siteData s (wit m.st.input) m.st.heard ds).v = s.shape.v := by
    have e := (Spec.numsAre_real s.shape s.p.lm s.p.first
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) hok).parts
    have e' : [s.shape.v] = [(_root_.Fo.numsF s.shape s.p.lm s.p.first
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta)).v' + 1] := e
    exact (List.cons.inj e').1.symm
  exact ⟨c, c', F, g, G₂, H, hlend, hc, hF1, hnext, b1, hparts, hHd, hP, hLeft, hv, a3, a4⟩

/-! ## 4 On the calls of a group's layers -/

/-- **At the shape X.layers.y.fo, and the data's keys are the joint vector of `keysG`.** Conditional
on the same hypotheses but for `hSet`, at the seated filling's own reader; the site is a layers'
link's; `ShapeIsFs`. No instance of these hypotheses is exhibited in this file. -/
theorem left_at_layers (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat)
    (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst)
    (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B)
    (hS : SiteAt L b Z Bs ch s lot ((fastFill (Rc := Rc') src).jobs s).asked
      (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s)) D Lk)
    (hd : s.digits = false) (hc : s.caller = .layers) (hB : ShapeIsFs Z.p.X s)
    {blk : Block FS ProofFile.Cl} (hb : L.bs[b]? = some blk) {k : Coins Bk}
    {st st' : FS} {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) Xo} {cols : List OpenedColumn}
    (hA : Thr L.thread b k st m E) (hdr : drawsFit blk.rounds ds = true)
    (hSt : L.thread.Stepped blk k st m E ds y cols st')
    (hM : (siteData s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) m.st.input)
      m.st.heard ds).Mid) :
    CallsLeft L.thread.chain k blk s ((fastFill (Rc := Rc') src).jobs s).asked
        (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s)) Z.p.X.layers.y.fo st st' m ds ∧
      ∀ x, (siteData s (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) m.st.input)
          m.st.heard ds).key x =
        jointKey Z.p.X.layers.y.fo
          (keysG Z.p.X (cells m.st.input.trace) (weights m.st.input.w₀) s.group)
          (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) x := by
  obtain ⟨h1, _, h3⟩ := Spec.site_layers Z s hS.site hd hc
  have hsh : s.shape = Z.p.X.layers.y.fo := Option.some.inj (hB.symm.trans h1)
  have hSet : Ask.Settled s.at_.base
      (askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) m.st.input) :=
    askOf_settled _ _ _ _ fun link rng e => by
      rw [h3] at e
      exact nomatch e
  refine ⟨(left_at_calls src o pol lay KL Fd base A B O hS hd hb hA hdr hSt hSet hM).shape hsh,
    fun x => ?_⟩
  rw [h3]
  exact dataAt_key_layers _ Z.p.X cells weights req s.group m.st.input m.st.heard _ x

/-! ## 5 At the letters `lettersHead` under `P5J.AtMgA` -/

section
variable {Zl : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xP : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Zl Dw r Zp Np cF xP) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-- **The one statement, at the letters `lettersHead` under `P5J.AtMgA`.** Conditional on the
hypotheses that the head of this file lists. At the full size alone. No instance of these hypotheses
is exhibited in this file. -/
theorem left_at_layers_head (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : ProofFile.Inst → OnBytes.Model.Head.Covered × Array Nat) (src : Sources W₀' Xi' Tr')
    (s : Site) (hsite : s ∈ lookSites Zp) (hd : s.digits = false) (hc : s.caller = .layers)
    (hB : ShapeIsFs Zp.p.X s) (lot : Block TS ProofFile.Cl)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked
      (askOf (tiedOwnSources Zp.p.X cells weights req) (whoOf s)))
    {blk : Block TS ProofFile.Cl} (hb : (LH).bs[borderOf s.link s.digits]? = some blk) {k : Coins Bk}
    {st st' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hA : Thr (LH).thread (borderOf s.link s.digits) k st m E)
    (hdr : drawsFit blk.rounds ds = true)
    (hSt : (LH).thread.Stepped blk k st m E ds y cols st')
    (hM : (siteData s (askOf (tiedOwnSources Zp.p.X cells weights req) (whoOf s) m.st.input)
      m.st.heard ds).Mid) :
    CallsLeft (LH).thread.chain k blk s ((fastFill (Rc := Rc') src).jobs s).asked
        (askOf (tiedOwnSources Zp.p.X cells weights req) (whoOf s)) Zp.p.X.layers.y.fo st st' m
        ds ∧
      ∀ x, (siteData s (askOf (tiedOwnSources Zp.p.X cells weights req) (whoOf s) m.st.input)
          m.st.heard ds).key x =
        jointKey Zp.p.X.layers.y.fo
          (keysG Zp.p.X (cells m.st.input.trace) (weights m.st.input.w₀) s.group)
          (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) x := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot _ _ R
  exact left_at_layers cells weights req src o pol lay KL Fd base A B O hS hd hc hB hb hA hdr hSt hM

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.via_split
#print axioms ProofFile.Honest.K3.Law.AtThr.CallsLeft.shape
#print axioms ProofFile.Honest.K3.Law.AtThr.left_at_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.left_at_layers
#print axioms ProofFile.Honest.K3.Law.AtThr.left_at_layers_head
