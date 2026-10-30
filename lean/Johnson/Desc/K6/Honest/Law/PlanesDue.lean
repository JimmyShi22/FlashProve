-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/PlanesDue.lean.
WHAT IT IS NOT. EVERY STATEMENT IS CONDITIONAL: on the member's form, on its passing its test on the
plan, on an accepting decision (or step) of the member, on nine facts on the state in front and five
on public data (K6DueFront, K6DuePub: Johnson/Desc/K6/Honest/Law/Due.lean), and on eight more
premises on public data and on the state in front, each named. None is shown here of any state or
data. NO ITEM OF THE TABLE OF JOINTS IS SHOWN: K6PlanesDue is a structure of premises: nine of the
premises of the library's planes_mgAll (Johnson/Desc/Kinds/Law/K6PlanesAtMgAll.lean), gathered: to
meet it is no property of a protocol. No thread, no prover, no coin, no value of a witness. Segment
24 is a numeral, as in that lemma. Nothing on soundness, on completeness or on what a proof hides.
WHAT IT IS. The sub-protocol "the output head's own rounds": what the law on the item "planes" asks
of the verifier's states in front of and behind its accepting step, from what is known in front.
  K6PlanesDue          the nine premises, as a structure; general in the composed meaning's data
  planesDue_of_front   from the member's accepting decision: the bare sub-protocol's decision, what
                       the library asks of the state in front (K6On), and K6PlanesDue at some part
                       of the state behind
  planesDue_of_step    the same from the member's accepting step
WHO PAYS WHAT. The bare decision and the state's own test on the request, from the member's:
seated_decide_iff (Law/K6WayUp.lean) at the library's IM.alone_underR (IMR/SeatForm.lean): at every
address and every guard. K6On: k6On_of_start (Law/K6OrdLeft.lean). seg, arr, stated, and nu's layout
and mask oracle: recordRest_keeps (Due.lean). nu's five facts a matrix, at the planes' columns: the
library's matsSeated_of_C (Law/K6SeatsTest.lean) at stateIsPlan_keeps (Due.lean). nu: the library's
nu_mg (Law/K6PlanesAtMgAll.lean). ns: what an accepting step keeps (K6Keeps: as many slots), and the
premise nsEq. wide: wide_below, wide_says (Law/HeadRidesSays.lean). len, shape: an accepting step
keeps what the lookup has heard (K6Keeps.kept, Johnson/Desc/K6/Honest/Law/Keeps.lean); left_says
(Law/K6LeftSays.lean); the premises hplace and planeCols. rd: decide_record (Law/RowPromise.lean),
readers_silent_planes (Law/PlanesCell.lean), at the premises readers and runs2 and at A's "no tables
are laid yet".
NOT SPENT: of the nine facts in front the ninth (the ledger has at most the plan's number of slots):
nsEq says more; of the five on public data the first and the fourth (states: on the link's third
run-stating sub-protocol; named: at other columns than the planes').
TYPED AFTER: planesDue_of_front's first lines (to the bare decision with the test on the words) and
its lines on the two ledgers are those of due_of_front (Due.lean); its line on the reader's equation
goes as the library's own law has it (Johnson/Desc/Kinds/Law/K6LawAtMgAll.lean, inside a proof).
It imports, beside library files, Due.lean and what that imports.

-/
import Johnson.Desc.K6.Honest.Law.Due
import Johnson.Desc.Kinds.Law.K6PlanesAtMgAll
import Johnson.Desc.Kinds.Law.HeadRidesSays
import Johnson.Desc.Kinds.Law.PlanesCell
import Johnson.Desc.Kinds.Law.K6LeftSays
import Johnson.Desc.Kinds.Law.K6SeatsTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block Claim OpenedColumn Place Link Wit noDigest)
open VerifiableInference.OnPublicFiles (headNu k3AdrAt)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT MgData namedOnce)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (K6DueFront K6DuePub recordRest_keeps
  stateIsPlan_keeps matsSeated_of_C)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}

/-- **NINE PREMISES OF THE LIBRARY's LAW ON THE ITEM "PLANES", ON THE TWO STATES.** s: in front of
the sub-protocol; s': behind its accepting step; aK: the open segment's part of s'; cU: the array of
the reads. rd: at s' the link's reader of the run "planes" is the silent one. seg, arr: aK and cU
are read off s'. ns: the ledger behind has the plan's number of slots. stated: what is stated at s'.
wide: the array of the reads is as wide as the plan says. len: an inequality on what the lookup has
heard and the plan's numbers. shape: in front, what the lookup has heard has the caller's shape. nu:
the lookup's places off the data are the caller's off the witness, at every witness. A structure of
premises. Nothing is claimed of it. -/
structure K6PlanesDue (D : MgData Xi P Tok rows cols nR Wp)
    (x : First.Look.Place) (states : Nat → List (K9.RunOf S)) (s s' : S) (aK : K9.Part)
    (cU : Nat × String) : Prop where
  rd : (D.Rd 24).forms 2 "planes" s' = k6Silent (p8K6 Wp 24) states 2 "planes" s'
  seg : K9.segAt? s' = some aK
  ns : aK.F.ns = Wp.H.ns
  arr : aK.L.arrayOf[readsOf Wp]? = some cU
  stated : StatedAt Wp (p8K6 Wp 24) D.St s' cU
  wide : ∀ e F tr, withTables (p8K6 Wp 24) s' = some e → e.fork? = some F →
    F.trees[readsOf Wp]? = some tr → Wp.H.nU.getD 2 0 ≤ tr.K
  len : ∀ gk, s'.lookHeard? = some gk →
    gk.shape.NC * 2 ^ (gk.shape.kT + 5 - Wp.hS.lmbH) ≤
      (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
        ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH)
  shape : ∀ g, s.lookHeard? = some g → g.shape = x.fs
  nu : ∀ (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) pq, nuK6 Wp s'
      (Sound.dataQ (D.N.sent 24 0) aK (Sound.seatTab D.cs D.arr D.ms w)) pq =
    headNu (k3AdrAt Wp) x Wp.H.tl D.sent D.l3.rad D.l3.oW D.l3.wOf D.l3.nr D.l3.nc
      (fun j => D.l3.seat x.link false j.1) D.l3.arr D.l3.msgW w pq

/-- **FROM THE MEMBER's ACCEPTING DECISION.** CONDITIONAL: Mb: the member's form; hp: it passes its
test on the plan; hd: its decision, with the test that every word is below the prime, accepts; A, B:
the nine facts in front and the five on public data; readers, runs2: the link's readers and its
second run-stating sub-protocol's states; nsEq: the ledger in front has the plan's number of slots;
Mt, callsB, namedB: the caller's facts on public data, at the planes' columns too; hplace: the place
of the lookup on the calls has the caller's shape; planeCols: an inequality on the plan's numbers.
-/
theorem planesDue_of_front (D : MgData Xi P Tok rows cols nR Wp) {lay6 : ReqLayout}
    {num : ℕ → ℕ → ℕ} {Lp : K12.Door.Laid} {M : List OracleShape} {pl : Option Place}
    {same : S → S → Bool} {a : Place} {blk : Block S Claim} (Mb : K6MemberIs Wp 24 same a blk)
    (hp : blk.planOk = true)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (Sound.below blk).decide s rs gs = .ok s')
    (A : K6DueFront D.N Wp lay6 D.cs D.shape D.pubD.dS Lp M (D.sent.arrayOf.getD 24 #[]) pl s)
    (Lk : Link S Claim)
    (B : K6DuePub D.arr D.N Wp lay6 num D.cs D.shape D.pubD.dS Lp M (D.sent.arrayOf.getD 24 #[]) pl
      D.St Lk)
    (small : S → Option K9.Read)
    (readers : D.Rd 24 =
      K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (runs2 : PlanesStates (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (nsEq : ∀ F, s.fork? = some F → F.ns = Wp.H.ns) {x : First.Look.Place}
    (Mt : CallerMeets D lay6 num (num 24 0) x)
    (callsB : CallsSeated (colsB Wp) D.arr D.ms D.N Wp lay6 num D.sent D.l3.rad x.link
      fun j => D.l3.seat x.link false j.1)
    (namedB : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      colsB Wp μ.val c → namedOnce D.arr D.N 24 (seatLay Wp lay6 num 24 μ r c).1 = true)
    (hplace : ∀ p, First.Look.placeAt Wp 24 false = some p → p.shape = some x.fs)
    (planeCols : x.fs.NC * 2 ^ (x.fs.kT + 5 - Wp.hS.lmbH) ≤
      (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
        ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH)) :
    (Sound.below (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24)).decide s rs gs = .ok s' ∧
      K6On Wp s ∧ ∃ aK cU, K6PlanesDue D x (K9.statesOfLink Lk) s s' aK cU := by
  have hv : (if VerifiableInference.Desc.viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩
      then blk.decide s rs gs else .error "a word is not below the prime") = .ok s' := hd
  split at hv
  · rename_i hok
    obtain ⟨hbare, hstart⟩ : (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24).decide s rs gs = .ok s' ∧
        startOk Wp s = true := by
      have hU := Mb.bare
      obtain ⟨ms, bS, name, hS, hla⟩ := Mb
      exact (seated_decide_iff hS hU s s' rs gs).1 ((IM.alone_underR hla).2 s rs gs s' hv)
    have K : K6Keeps s s' := Honest.k6_keeps_of_member Mb hv
    have hOn : K6On Wp s := by
      obtain ⟨ms, bS, name, hS, hla⟩ := Mb
      exact k6On_of_start hS ((IM.alone_planOk hla).symm.trans hp) hstart A.left
    have hbel :
        (Sound.below (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24)).decide s rs gs = .ok s' := by
      show (if VerifiableInference.Desc.viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩
        then (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24).decide s rs gs
        else .error "a word is not below the prime") = .ok s'
      rw [if_pos hok]
      exact hbare
    obtain ⟨aK, cU, ⟨r1, r2, _, r4, r6, r7, _⟩, hF, F0, hF0⟩ := recordRest_keeps K A.fold A.sentIs
      A.fresh A.book B.seats D.St B.stated A.lookLeft
    obtain ⟨aK2, I, _, _, _⟩ := stateIsPlan_keeps K A.fold A.sentIs A.fresh A.book
    have e2 : aK2 = aK := Option.some.inj (I.seg.symm.trans r1)
    rw [e2] at I
    have rB1 : MatsSeated (colsB Wp) D.arr D.N Wp (D.N.sent 24 0) aK num lay6 :=
      matsSeated_of_C B.seats I (colsB Wp) (fun a _ hc => by
        have e : a = Wp.hS.NHf + 2 := hc
        omega)
    have hKk := K.kept Wp
    have e0 : (seatAt Wp.hS (readsOf Wp)).ledger s = F0 := by
      show s.fork?.getD {} = F0
      rw [hF0]
      rfl
    have e1 : (seatAt Wp.hS (readsOf Wp)).ledger s' = aK.F := by
      show s'.fork?.getD {} = aK.F
      rw [hF]
      rfl
    have hLn := hKk.1.ns
    rw [e1, e0] at hLn
    have hns : aK.F.ns = Wp.H.ns := by
      have h2 := nsEq F0 hF0
      omega
    obtain ⟨p3, hp3, L3⟩ := A.lookLeft
    obtain ⟨h3, _, g0, hs3, _, hg0, Y, _⟩ := left_says p3 s L3
    have eh : h3 = x.fs := Option.some.inj (hs3.symm.trans (hplace p3 hp3))
    have hshape : ∀ g, s.lookHeard? = some g → g.shape = x.fs := fun g hg => by
      have eg : g0 = g := Option.some.inj (hg0.symm.trans hg)
      rw [← eg, Y.shape, eh]
    have hrd : (D.Rd 24).forms 2 "planes" s' =
        k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk) 2 "planes" s' := by
      obtain ⟨o, F1, X, Q, ho, _, _, e⟩ := Came.decide_record _ _ _ _ hbare
      have hnt := A.noTables
      unfold noTablesB at hnt
      rw [ho] at hnt
      rw [readers]
      exact readers_silent_planes (readsOf Wp) Wp.hS.lmbH 2 Lk runs2 (p8K6 Wp 24) small s'
        { o with F := F1, x := some X, squaresP := some Q } (by rw [e])
        (Option.isNone_iff_eq_none.1 hnt)
    exact ⟨hbel, hOn, aK, cU,
      { rd := hrd
        seg := r1
        ns := hns
        arr := r6
        stated := r7
        wide := wide_says (p8K6 Wp 24) s' (readsOf Wp)
          (wide_below Wp 24 _ Mb.bare s s' rs gs hbel _ _ A.wide)
        len := fun gk hg => by
          rw [hshape gk (hKk.2.2.2 ▸ hg)]
          exact planeCols
        shape := hshape
        nu := fun w pq => nu_mg Mt B.laid namedB callsB w aK s' r2 rB1 r4 pq }⟩
  · cases hv

/-- **THE SAME FROM THE MEMBER's ACCEPTING STEP.** CONDITIONAL: as `planesDue_of_front`, with hstep
in hd's stead. The decision stands at the rounds without the sealed digest: so the step shows them
(Desc/Block.lean). -/
theorem planesDue_of_step (D : MgData Xi P Tok rows cols nR Wp) {lay6 : ReqLayout}
    {num : ℕ → ℕ → ℕ} {Lp : K12.Door.Laid} {M : List OracleShape} {pl : Option Place}
    {same : S → S → Bool} {a : Place} {blk : Block S Claim} (Mb : K6MemberIs Wp 24 same a blk)
    (hp : blk.planOk = true)
    {ft n : Nat} {s s' : S} {rs : List Fmt.RoundView} {cl : List OpenedColumn}
    (hstep : (Sound.below blk).step ft s rs cl = .ok (s', n))
    (A : K6DueFront D.N Wp lay6 D.cs D.shape D.pubD.dS Lp M (D.sent.arrayOf.getD 24 #[]) pl s)
    (Lk : Link S Claim)
    (B : K6DuePub D.arr D.N Wp lay6 num D.cs D.shape D.pubD.dS Lp M (D.sent.arrayOf.getD 24 #[]) pl
      D.St Lk)
    (small : S → Option K9.Read)
    (readers : D.Rd 24 =
      K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (runs2 : PlanesStates (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (nsEq : ∀ F, s.fork? = some F → F.ns = Wp.H.ns) {x : First.Look.Place}
    (Mt : CallerMeets D lay6 num (num 24 0) x)
    (callsB : CallsSeated (colsB Wp) D.arr D.ms D.N Wp lay6 num D.sent D.l3.rad x.link
      fun j => D.l3.seat x.link false j.1)
    (namedB : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      colsB Wp μ.val c → namedOnce D.arr D.N 24 (seatLay Wp lay6 num 24 μ r c).1 = true)
    (hplace : ∀ p, First.Look.placeAt Wp 24 false = some p → p.shape = some x.fs)
    (planeCols : x.fs.NC * 2 ^ (x.fs.kT + 5 - Wp.hS.lmbH) ≤
      (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
        ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH)) :
    ∃ gs, (Sound.below (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24)).decide s (rs.map noDigest) gs =
        .ok s' ∧
      K6On Wp s ∧ ∃ aK cU, K6PlanesDue D x (K9.statesOfLink Lk) s s' aK cU := by
  obtain ⟨gs, hd⟩ := Came.step_decide ft (Sound.below blk) s rs cl s' n hstep
  exact ⟨gs, planesDue_of_front D Mb hp hd A Lk B small readers runs2 nsEq Mt callsB namedB hplace
    planeCols⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.planesDue_of_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.planesDue_of_step
