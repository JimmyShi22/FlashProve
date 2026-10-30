-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/RideTies.lean: on the tables that senders of the kind K1 send along in the
first chains of the proof file and of a key file. Under public premises the numbers k and h of each
such table are the numbers at which the verifier's sub-protocol is made whose first fold is meant to
use it.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". A table sent along (Ride) is the
fresh mask table of a later folding step. It has two numbers: k, the fold's number of row variables,
and h, its number of mask row variables. The sender takes 2 k + 1 coins for it (Ride.count,
Johnson/Desc/ProofFile/Honest/K1/Coins.lean). Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. In these two first chains senders of the kind K1 send a table along at four
places. In the proof file's first chain: with the opening, and with the request's own table W. In a
key file's first chain: with the lookups' own message, and with W.

The proof file, W. The premises are IM.Open and F.planOk = true.
  w_fold_some       A table is sent along: wFold Z.first.lin names a fold.
  w_ride_tie        Let N be the value of H2U.placesOfMade Z.made, the numbers from which the
                    description's maker makes the proximity tests. If wFold Z.first.lin names a fold
                    Fd, the first stage of N.W has Fd's k and h, and the first pair of N.W.idx is
                    Fd's two codes' numbers.
  w_stages_tie      The same for all stages: N.W's stages have the k and h of the stages of
                    Z.first.lin.testOwn, and N.W.idx has their codes' numbers.
  w_codes_tie       The first chain's codes, as parsed from the parameter bytes, are the codes that
                    the planner sized. So a code's number names the same code in the sender's
                    parameters and in the numbers from which the proximity tests are made.
  w_member_tie      The same at the description's own member. F is the library's descN at Z, some N
                    and some c'. RowK12 holds there (Johnson/Loose/H2K12/SitsRow.lean): its field
                    own says that the last chain's list holds the proximity test at the parameters
                    pOwn N, seated by enterOwn and leaveOwn, and that every entry of that list with
                    the kind K12 is that entry. pOwn N has the k, h and codes' numbers of
                    Z.first.lin.testOwn. The stage at which that test's first fold is made
                    (K12.stageAt (pOwn N) 0, Johnson/Desc/K12/Join.lean) is the first stage of
                    Z.first.lin.testOwn, whole.

The proof file, the opening. The premise is IM.Open, at every hash function o.
  first_ride_tie    For any list xs, any p with p.link = 0 and any Q with
                    ProofFile.k10Par Z xs p = some Q: firstFold Bs.G₀.first names a fold with k = Q.k and
                    h = Q.h. The description's own call is at ProofFile.k9Stretches Z and IM.k9At Z 0.
  first_member_tie  The same at the description's own member. The further premises are
                    IM.HeadIsTwo Z (Johnson/IMR/CloseSeat.lean) and that the public part has a
                    link 0. Then the second of the three blocks that close segment 0 (Lk.close[1];
                    the first is the one equation, the third marks the segment shut) is the
                    library's closing sub-protocol at the numbers Q that ProofFile.k10Par makes there,
                    seated by itself with nothing joined behind it, and firstFold's fold has
                    k = Q.k and h = Q.h.

A key file. The premise is (Key.descriptionFromSource Xs N P).planOk = true.
  key_folds_some    Tables are sent along: msgFold Xs.Y.k.oneTime.ranges and
                    wFold Xs.Y.k.oneTime.lin name folds.
  key_msg_ride_tie, key_w_ride_tie   If msgFold Xs.Y.k.oneTime.ranges names a fold, the first stage
                    of N has that fold's k and h, and the first pair of N.idx is its two codes'
                    numbers. The same holds for wFold Xs.Y.k.oneTime.lin and P.W.
  key_stages_tie    The same for all stages of the two tests.
  key_member_tie    The same at the description's own members. RowK12Key holds
                    (Johnson/Loose/H2K12/SitsRowKey.lean). The parameters of the ranges' test and of
                    the test on the request's own group have the k, h and codes' numbers of the
                    matching test of the one-time chain (ranges.stages, lin.testOwn). The stage at
                    which each test's first fold is made is the first stage of the matching test,
                    whole.
  key_w_there       The shape has a message for W, so keyPars Xs has three entries.
  sized_codes       For any codes, stages and numbers at which Key.stagesAsSized accepts: the two
                    lists of stages have one length, and stage by stage the two codes under the
                    stage's two numbers are there, and the stage's sized numbers C and Z are those
                    codes' three numbers (logN, ell, r).
  key_plan_facts    What the tests on the plan say of the one-time chain's values: every code's
                    message length is a power of two; the stages of each of the two tests fit
                    together (ioppOk); masks are sent along and sent ahead.

How it fits. The statements on the field fresh have content where a later part spends a table's
coins. How many coins the sender takes depends on k, and no test on the sender's public numbers sees
k (rideOwn, Johnson/Desc/ProofFile/Honest/K1/PlaceJob.lean, Limits). These lemmas show that the k
and h which the sender reads off its own parameters are those from which the verifier's sub-protocol
is made whose first fold is meant to use that mask: the proximity test on the request's own group,
the closing of segment 0, and at a key file the ranges' test and the test on the request's own
group. That it takes this very message as its mask is not shown (Limits). Meant as steps toward
index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from
them. Not one of the release's goal statements.

How it is proved. Every step is a lemma of the library or an unfolding of a definition.
At the proof file's W. The numbers of the places are the stages that the planner sized (places_nums,
Johnson/Desc/K12/Law/PlacesNums.lean; places_idx, Johnson/Desc/K12/Law/Sizes/IdxAtScope.lean). The
shape's test stages are computed from those, with the same k and h (pub_configure,
Johnson/Desc/ProofFile/Law/PlainMade.lean; configure_proof_sizes, OnBytes/Plan/PlanListsProof.lean;
tests_of_proofSized, IdxAtScope.lean; kh_of_stages, OnBytes/Params/Fit/StageCaps.lean). The shape
that the planner sized is the first chain's shape as parsed from the parameter bytes, by the test on
the plan of the shared chain's first sub-protocol (front2_at_planOk, lin_sized, codes_sized,
Johnson/P2R0R/SizedIsRead.lean). For the member: descPure_of_open (Johnson/AtFull/Desc/Ledger.lean),
k12_sits_row, RowK12.plans and RowK12.nums (SitsRow.lean), idx_of_planOk (IdxAtScope.lean).
At the opening: par_k and first_groups (Johnson/LPFK10R/KLive.lean) and IM.Open.first. For the
member: k10_sits_alone (Johnson/LPFK10R/SitsO.lean) and k9_alone (Johnson/IMR/LinkSeat.lean).
At a key file: clauses of the description's test on the file, "stages.rng", "stages.own" and the
clause that the first two chains hold the same shape (Johnson/Desc/Key/FileOk.lean), and "lengths",
"ranges" and "form" (Johnson/Desc/Key/Source.lean), through fileOkD_of (Johnson/RunOne/KeyPayD.lean)
and clause_of_ok (Johnson/RunOne/KeyPayClauses.lean). For the members: key_sits_row, RowK12Key.plans
and RowK12Key.nums (SitsRowKey.lean).

The other names. maps_eq_of_zip, head_of_maps: on lists. wFold_spec, msgFold_spec: what a fold that
wFold or msgFold names is made of. first_stage_tie, first_fold_stage: from the equations on all
stages to the first stage. head_of_ioppOk: a test whose stages fit together has a first stage.
front2_of_plan, own_test_of_plan: from F.planOk to the test of the shared chain's first
sub-protocol, and to ioppOk and "masks are sent ahead" at Z.first.lin. sized_maps: what
Key.stagesAsSized says of the stages' k and h and of the pairs of codes' numbers; sized_codes has
the rest.

Limits.
These lemmas reach the verifier's sub-protocols alone (of the kind K12, and K10 at the opening).
Among the files that this folder imports there is no honest part (a Part of an honest side,
Johnson/Desc/ProofFile/Honest/Frame.lean) of the kind K12 or K10, for the proof file or a key file.
Johnson/Prover/Link/ writes some of the honest prover's messages of the proximity test as functions,
with no side and no coins. Nor does anything among these files make the entries of a book of coins
(Book, Frame.lean) from a description. A folder and a file that this folder does not import could be
taken for such: Johnson/Desc/K10/Honest/ holds theorems on the verifier's own text, and
Johnson/Desc/ProofFile/Honest/BookOf.lean says that its rows and entries are not yet written. So
nothing here shows that a book names the verifier's sub-protocol as the part that spends a table
sent along: nothing here rules out a book that is clear (BookClearAny,
Johnson/SendSim/At/BookWide.lean) while it names another part, or no part.
These are equations on public numbers; nothing here speaks of distributions.
Only the first chains are covered. In both files' shared chains a sub-protocol of the kind K1
(K14.sendAt, Johnson/Desc/K14/Blocks.lean) also sends a fresh mask along, with the message that
holds the folded row, where masks are sent ahead (linWithU, OnBytes/Iop/Lin.lean). The numbers of
that mask are not tied here.
Which message the verifier's sub-protocol takes as its mask is a number in the verifier's state, not
in the plan, and nothing here ties it to the table that is sent along. At a key file's ranges' test
the description's own text ties them, by inspection, not proved. Where masks are sent along,
openRangesGroup (Johnson/Desc/Key/One.lean) records the second number that the sending leaves
(sent[1]): the message at index 1 of the sending, the index that msgFold names. enterRanges
(Johnson/Desc/Key/Chain1.lean) passes it to the test. At the proof file's last chain the library's
own limit says more: at the chain's start any message that is not sampled and has no answers passes
as the mask (the test's own front asks more), and only W's own number is shown to be refused
(Johnson/Desc/Third/State.lean, Limits (1)).
What is compared is k, h and the two codes' numbers. The fold's layout and its class of leaves are
not compared. That a code's number names the same code on both sides is w_codes_tie at the proof
file. At a key file sized_codes gives it stage by stage for any test at which Key.stagesAsSized
accepts; it is not applied to the two tests here.
That an entry with the kind K12 stands only once in its list is not said by RowK12 or RowK12Key.
first_ride_tie is about numbers: it does not say that a member of the description is made at Q.
first_member_tie says so under IM.HeadIsTwo Z, which the library proves only in the scope of the
release's goals, at the hash function OnBytes.secondHashFunction (head_is_two, Johnson/IMR/CloseSeat.lean). The
closing's decision reads k and h from the frame in the verifier's state, not from Q. The library
carries that frame's groups along the first chain (descPure_recAll, Johnson/IMR/RecRun.lean); the
two are not joined here.
That msgFold's fold is the one that Wf.messageOf sends along is by inspection, not proved
(AtKeyPars.lean, Limits).
At a key file Xs, N and P are any arguments. That they are what Key.descriptionFromPlan makes of given files
is not shown here.
That F.planOk holds at given public files is not shown here. At the hash function OnBytes.secondHashFunction, at
every public file in the goals' scope at which the library's gate accepts, the maker returns and its
description passes its tests on the plan (plan_of_live, ReadsAtLive.lean; returns_of_live,
AtDesc.lean). That the gate accepts is a theorem of the side library at the stored full-size
files, under both named policies and every policy within the four bounds of VerifierAndGoals.inScope_zAt
(theLive_zFull, AtFullSide/Top/LiveAtFull.lean; theLive_zGap, theLive_zAt, LiveAtPolicies.lean
beside it).
At a key file the library proves the premise at the Xs, N and P that the maker makes of given
files: wherever Key.keyDataAndDecisionAtDigest returns (key_sits_row_laidAt, Johnson/Loose/H2K12/SitsRowKey.lean), and,
for files in the scope of the release's goals, at the fixed digest where the maker's five routines
return (key_planOk_in_scope, Johnson/HB/LLHARD/KB4/RowInScope.lean).
For all other limits see AtDescLots.lean.
-/
import Johnson.SendSim.Seat.RideFitsW
import Johnson.SendSim.Seat.AtKeyPars
import Johnson.Desc.K12.Law.PlacesNums
import Johnson.Desc.K12.Law.Sizes.IdxAtScope
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Loose.H2K12.SitsRow
import Johnson.Loose.H2K12.SitsRowKey
import Johnson.AtFull.Desc.Ledger
import Johnson.LPFK10R.KLive
import Johnson.LPFK10R.SitsO
import Johnson.RunOne.KeyPayD

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

/-! ## Lists, and the two folds -/

/-- Two lists of one length whose members agree pair by pair under f and g have equal images. -/
theorem maps_eq_of_zip {α β γ : Type} (f : α → γ) (g : β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (∀ x ∈ l₁.zip l₂, f x.1 = g x.2) → l₁.map f = l₂.map g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l₁, b :: l₂, h, hz => by
    rw [List.map_cons, List.map_cons, hz (a, b) (List.mem_cons_self ..),
      maps_eq_of_zip f g l₁ l₂ (Nat.succ.inj h) fun x hx => hz x (List.mem_cons_of_mem _ hx)]

/-- If two lists have equal images and the second has a first member, so has the first, with the
same image. -/
theorem head_of_maps {α β γ : Type} {f : α → γ} {g : β → γ} {l₁ : List α} {l₂ : List β}
    (h : l₁.map f = l₂.map g) {b : β} (hb : l₂.head? = some b) :
    ∃ a, l₁.head? = some a ∧ f a = g b := by
  have h1 := congrArg List.head? h
  rw [List.head?_map, List.head?_map, hb] at h1
  exact Option.map_eq_some_iff.1 h1

/-- A fold that wFold names has the four numbers of the first stage of the test on the request's own
group. -/
theorem wFold_spec {S : LinShape} {n : Nat} {Fd : FoldShape} (h : wFold S = some (n, Fd)) :
    ∃ s, S.testOwn.head? = some s ∧ Fd.layout.k = s.k ∧ Fd.layout.h = s.h ∧ Fd.code = s.code ∧
      Fd.maskCode = s.maskCode := by
  unfold wFold at h
  split at h
  · obtain ⟨s, hs, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl := (Prod.mk.inj e).2
    exact ⟨s, hs, rfl, rfl, rfl, rfl⟩
  · cases h

/-- A fold that msgFold names has the four numbers of the first stage of the ranges' test. -/
theorem msgFold_spec {x : WfPublic} {n : Nat} {Fd : FoldShape} (h : msgFold x = some (n, Fd)) :
    ∃ s, x.stages.head? = some s ∧ Fd.layout.k = s.k ∧ Fd.layout.h = s.h ∧ Fd.code = s.code ∧
      Fd.maskCode = s.maskCode := by
  unfold msgFold at h
  split at h
  · rename_i t ht
    split at h
    · obtain rfl := (Prod.mk.inj (Option.some.inj h)).2
      exact ⟨t, ht, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- If the stages' k and h and the codes' numbers agree list by list with st, the first member of
stages has the k and h of st's first member s, and the first pair of idx is s's two codes'
numbers. -/
theorem first_stage_tie {stages : List Fmt.M1.Stage} {idx : List (Nat × Nat)}
    {st : List IoppStage}
    (h : (stages.map fun y => (y.k, y.h)) = (st.map fun s => (s.k, s.h)) ∧
      idx = st.map fun s => (s.code, s.maskCode)) {s : IoppStage} (hs : st.head? = some s) :
    (∃ y, stages.head? = some y ∧ y.k = s.k ∧ y.h = s.h) ∧
      idx.head? = some (s.code, s.maskCode) := by
  obtain ⟨y, hy, e⟩ := head_of_maps h.1 hs
  refine ⟨⟨y, hy, (Prod.mk.inj e).1, (Prod.mk.inj e).2⟩, ?_⟩
  rw [h.2, List.head?_map, hs]
  rfl

/-- Under the same two equations at the parameters p of a proximity test: the stage at which the
test's first fold is made (K12.stageAt p 0, Johnson/Desc/K12/Join.lean) is st's first member,
whole. -/
theorem first_fold_stage {p : K12.P12} {st : List IoppStage}
    (h : (p.nums.stages.map fun y => (y.k, y.h)) = (st.map fun s => (s.k, s.h)) ∧
      p.idx = st.map fun s => (s.code, s.maskCode)) {s : IoppStage} (hs : st.head? = some s) :
    ∃ y, p.nums.stages.head? = some y ∧ K12.stageAt p 0 y = some s := by
  obtain ⟨⟨y, hy, ek, eh⟩, hi⟩ := first_stage_tie h hs
  refine ⟨y, hy, ?_⟩
  have h0 : p.idx[0]? = some (s.code, s.maskCode) := by
    rw [← List.head?_eq_getElem?]
    exact hi
  unfold K12.stageAt
  rw [h0, Option.map_some, ek, eh]

/-- If the stages of a proximity test fit together, the test has a first stage. -/
theorem head_of_ioppOk {codes : Codes} {st : List IoppStage} {answers : Nat}
    (h : ioppOk codes st answers = true) : ∃ s, st.head? = some s := by
  unfold ioppOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  cases st with
  | nil => exact absurd h.1.1 (by simp)
  | cons s _ => exact ⟨s, rfl⟩

/-! ## The proof file: the table sent along with the request's own table -/

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Under IM.Open and F.planOk the test on the plan of the shared chain's first sub-protocol accepts
(OkD.AtC.front2). -/
theorem front2_of_plan (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    VerifiableInference.OnPublicFiles.OkD.AtC.front2 Z.p.chains = true := by
  have hA : _root_.Desc.K14.sharedSeatAt Z = some A := O.shared
  unfold _root_.Desc.K14.sharedSeatAt at hA
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    rw [hN] at hA
    cases hA
  | ok N =>
    rw [hN] at hA
    obtain rfl := Option.some.inj hA
    have e := O.desc
    subst e
    exact P2R0.front2_at_planOk _ _ _ _ _ _ _ _ _ _ _ _ _ hp

/-- Under IM.Open and F.planOk: the stages of the test on the request's own group fit together, and
masks are sent ahead. -/
theorem own_test_of_plan (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    ioppOk Z.first.codes Z.first.lin.testOwn Z.p.chains.proof.second.given.plan.samples = true ∧
      Z.first.lin.masksAhead = true := by
  have hb := beside_of_plan O hp
  unfold VerifiableInference.OnPublicFiles.OkD.AtC.beside VerifiableInference.OnPublicFiles.OkD.AtC.k12
    VerifiableInference.OnPublicFiles.OkD.AtC.file at hb
  simp only [Bool.and_eq_true] at hb
  have hW' : ioppOk Z.p.chains.proof.shared.codes Z.p.chains.proof.shared.lin.testOwn
      Z.p.chains.proof.second.given.plan.samples = true := hb.1.1.1.1.1.2
  have ha' : Z.p.chains.proof.shared.lin.masksAhead = true := hb.1.2.1.1.1.1.1.1.1.2
  have hr := P2R0.read_at_pub O.pub
  rw [Params.ProofChains.read_codes hr, Params.ProofChains.read_lin hr] at hW'
  rw [Params.ProofChains.read_lin hr] at ha'
  exact ⟨hW', ha'⟩

/-- **Under IM.Open and F.planOk a table is sent along with the request's own table**: wFold names a
fold. So w_ride_tie is not vacuous. -/
theorem w_fold_some (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    ∃ n Fd, wFold Z.first.lin = some (n, Fd) := by
  obtain ⟨h1, h2⟩ := own_test_of_plan O hp
  obtain ⟨s, hs⟩ := head_of_ioppOk h1
  have e : wFold Z.first.lin = some (if Z.first.lin.ownSplitNeeded then 2 else 1,
      { ioppFoldShape s {} with maskLeafClass := Z.first.lin.wLeafClass }) := by
    simp only [wFold, h2, if_true, hs, Option.map_some]
  exact ⟨_, _, e⟩

/-- Under IM.Open and F.planOk the first chain's codes, as parsed from the parameter bytes, are the
codes that the planner sized. So a code's number names the same code in the sender's parameters and
in the numbers from which the proximity tests are made. -/
theorem w_codes_tie (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    Z.first.codes = Z.p.chains.made.sized.proof.codes :=
  P2R0.codes_sized O.pub (front2_of_plan O hp)

/-- **Under IM.Open and F.planOk: the numbers from which the maker makes the proximity test on the
request's own group have the k, h and codes' numbers of the stages of Z.first.lin.testOwn.** -/
theorem w_stages_tie (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    {N : H2U.Places4} (hN : H2U.placesOfMade Z.made = .ok N) :
    (N.W.nums.stages.map fun y => (y.k, y.h)) = (Z.first.lin.testOwn.map fun s => (s.k, s.h)) ∧
      N.W.idx = Z.first.lin.testOwn.map fun s => (s.code, s.maskCode) := by
  obtain ⟨-, g, -, -, hW, -⟩ := H2K.Made.places_nums Z.made N hN
  have hI := (H2K.Sizes.places_idx Z.made N hN).2.2.2
  have hl : Z.p.chains.proof.first.lin = Z.p.chains.made.sized.proof.batch.shape :=
    P2R0.lin_sized O.pub (front2_of_plan O hp)
  obtain ⟨ls, -, hc, -, -⟩ := ProofFile.Law.pub_configure O.pub
  have ht := (H2K.Sizes.tests_of_proofSized (Params.configure_proof_sizes hc).1).2.2.2.1
  have hl' : Z.first.lin = Z.p.chains.made.sized.proof.batch.shape := hl
  constructor
  · rw [hW, List.map_map, hl', ht, Params.kh_of_stages]
    rfl
  · rw [hI, hl']
    rfl

/-- **Under IM.Open and F.planOk: the table that is sent along with the request's own table has the
k, h and codes' numbers of the first stage of N.W, from which the proximity test on the request's
own group is made.** -/
theorem w_ride_tie (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    {N : H2U.Places4} (hN : H2U.placesOfMade Z.made = .ok N) {n : Nat} {Fd : FoldShape}
    (hw : wFold Z.first.lin = some (n, Fd)) :
    (∃ y, N.W.nums.stages.head? = some y ∧ y.k = Fd.layout.k ∧ y.h = Fd.layout.h) ∧
      N.W.idx.head? = some (Fd.code, Fd.maskCode) := by
  obtain ⟨s, hs, e1, e2, e3, e4⟩ := wFold_spec hw
  rw [e1, e2, e3, e4]
  exact first_stage_tie (w_stages_tie O hp hN) hs

/-- **The same at the description's own member.** The description is the library's descN at Z and
some N and c'; RowK12 holds there; the parameters pOwn N of the proximity test on the last chain
have the k, h and codes' numbers of Z.first.lin.testOwn; and the stage at which that test's first
fold is made is the first stage of Z.first.lin.testOwn, whole. -/
theorem w_member_tie (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    ∃ N c', H2U.placesOfMade Z.made = .ok N ∧
      F = H2K.JointK.descN o ProofFile.pureRoad.links K12.guardedProximityTestParts Z N c' ∧
      H2K.JointK.RowK12 o ProofFile.pureRoad.links Z N c' ∧
      (((H2K.JointK.pOwn N).nums.stages.map fun y => (y.k, y.h)) =
          (Z.first.lin.testOwn.map fun s => (s.k, s.h)) ∧
        (H2K.JointK.pOwn N).idx = Z.first.lin.testOwn.map fun s => (s.code, s.maskCode)) ∧
      ∃ y s, (H2K.JointK.pOwn N).nums.stages.head? = some y ∧
        Z.first.lin.testOwn.head? = some s ∧ K12.stageAt (H2K.JointK.pOwn N) 0 y = some s := by
  obtain ⟨Z', N, c', hZ, hN, e, R⟩ :=
    H2K.JointK.k12_sits_row o pol lay KL F (Johnson.AtFull.Desc.descPure_of_open O)
  obtain rfl : Z = Z' := Except.ok.inj (O.pub.symm.trans hZ)
  obtain ⟨t1, t2⟩ := w_stages_tie O hp hN
  obtain ⟨s, hs⟩ := head_of_ioppOk (own_test_of_plan O hp).1
  subst e
  have hi : (H2K.JointK.pOwn N).idx = N.W.idx :=
    H2K.Sizes.idx_of_planOk ⟨3, none, 2, .K12⟩ N.W (R.plans hp).2.2.2
  have hT : ((H2K.JointK.pOwn N).nums.stages.map fun y => (y.k, y.h)) =
        (Z.first.lin.testOwn.map fun s => (s.k, s.h)) ∧
      (H2K.JointK.pOwn N).idx = Z.first.lin.testOwn.map fun s => (s.code, s.maskCode) := by
    rw [(R.nums hp).2.2.2, hi]
    exact ⟨t1, t2⟩
  obtain ⟨y, hy, hst⟩ := first_fold_stage hT hs
  exact ⟨N, c', hN, rfl, R, hT, y, s, hy, hs, hst⟩

/-! ## The proof file: the table sent along with the opening -/

/-- **Under IM.Open: the table that is sent along with the opening has the k and h of the numbers
that are made for the closing of segment 0.** -/
theorem first_ride_tie (O : IM.Open o pol lay KL F Z Bs base c A B)
    {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)} {p : VerifiableInference.Desc.K9.Where}
    {Q : VerifiableInference.Desc.First.Close.Par} (hQ : ProofFile.k10Par Z xs p = some Q)
    (h0 : p.link = 0) :
    ∃ n Fd, firstFold Bs.G₀.first = some (n, Fd) ∧ Fd.layout.k = Q.k ∧ Fd.layout.h = Q.h := by
  obtain ⟨-, Gr, hG, ek, eh⟩ := LPFK10.par_k hQ
  rw [LPFK10.first_groups O.pub, h0] at hG
  refine ⟨_, _, rfl, ?_, ?_⟩
  · show ((reqGroups Bs.G₀.first.shape).getD 0 {}).k = Q.k
    rw [O.first, Array.getD_eq_getD_getElem?, hG, ek]
    rfl
  · show ((reqGroups Bs.G₀.first.shape).getD 0 {}).h = Q.h
    rw [O.first, Array.getD_eq_getD_getElem?, hG, eh]
    rfl

/-- **The same at the description's own member**, under IM.HeadIsTwo Z: the second of the three
blocks that close segment 0 is the library's closing sub-protocol at the numbers Q that ProofFile.k10Par
makes, seated by itself, and the table that is sent along with the opening has k = Q.k and h = Q.h.
-/
theorem first_member_tie (O : IM.Open o pol lay KL F Z Bs base c A B) (hk2 : IM.HeadIsTwo Z)
    {sub : First.ModelPart} (hsub : (ProofFile.subsOf Z)[0]? = some sub) :
    ∃ (Lk : Link First.S ProofFile.Cl) (p : VerifiableInference.Desc.K9.Where)
      (Q : VerifiableInference.Desc.First.Close.Par) (b : Block First.S ProofFile.Cl),
      c.links[0]? = some Lk ∧ IM.k9At Z 0 = some p ∧
      ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ Lk.close[1]? = some b ∧
      IM.LaidAlone ProofFile.sameReply b
        (VerifiableInference.Desc.K9.closing Q : Block First.S Unit).retype b.name
        (IM.cAt 0 sub 1 KindName.K10) ∧
      ∃ n Fd, firstFold Bs.G₀.first = some (n, Fd) ∧ Fd.layout.k = Q.k ∧ Fd.layout.h = Q.h := by
  obtain ⟨Lk, p, Q, b, h1, h2, h3, h4, h5⟩ := LPFK10.k10_sits_alone O hk2 0 sub hsub
  obtain ⟨-, p', -, h2', -, -, hl, -⟩ := IM.k9_alone O 0 sub hsub
  obtain rfl : p' = p := Option.some.inj (h2'.symm.trans h2)
  exact ⟨Lk, p', Q, b, h1, h2, h3, h4, h5, first_ride_tie O h3 hl⟩

end

/-! ## A key file -/

/-- What Key.stagesAsSized says of k, h and the codes' numbers. -/
theorem sized_maps {codes : Codes} {st : List IoppStage} {N : H2U.PlaceNums}
    (h : Key.stagesAsSized codes st N = true) :
    (N.nums.stages.map fun y => (y.k, y.h)) = (st.map fun s => (s.k, s.h)) ∧
      N.idx = st.map fun s => (s.code, s.maskCode) := by
  unfold Key.stagesAsSized at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hl, hi⟩, hz⟩ := h
  refine ⟨maps_eq_of_zip _ _ _ _ hl fun x hx => ?_, hi⟩
  have h1 := hz x hx
  split at h1
  · simp only [Bool.and_eq_true, beq_iff_eq] at h1
    rw [h1.1.2, h1.2]
  · cases h1

/-- What a key file's tests on the plan say of the one-time chain's public values: every code's
message length is a power of two; the stages of the ranges' test fit together, and so do those of
the test on the request's own group; masks are sent along with the lookups' own message, and sent
ahead with W. -/
theorem key_plan_facts (Xs : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N P).planOk = true) :
    Own.lengthsFit Xs.Y.k.oneTime.codes = true ∧
      ioppOk Xs.Y.k.oneTime.codes Xs.Y.k.oneTime.ranges.stages
        Xs.Y.k.oneTime.ranges.message.shape.answers = true ∧
      ioppOk Xs.Y.k.oneTime.codes Xs.Y.k.oneTime.lin.testOwn
        Xs.Y.k.second.given.plan.samples = true ∧
      Xs.Y.k.oneTime.ranges.choice.masksRide = true ∧ Xs.Y.k.oneTime.lin.masksAhead = true := by
  have hD := Johnson.RunOne.KeyPay.fileOkD_of ((FileDescription.planOk_ok _).1 hp).fileOk
  have hs := hD.more ("chains 1 and 2 hold the same codes and the same shape, by value",
    decide (Xs.Y.k.oneTime.codes = Xs.Y.k.shared.codes) &&
      decide (Xs.Y.k.oneTime.lin = Xs.Y.k.shared.lin)) (by simp [Key.shapeClauses])
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  have h3 := hD.more ("ioppOk at chain 3's test", ioppOk Xs.Y.k.shared.codes
    Xs.Y.k.shared.lin.testOwn Xs.Y.k.second.given.plan.samples) (by simp [Key.shapeClauses])
  have hl := Johnson.RunOne.KeyPay.clause_of_ok hD.ok (n := "lengths")
    (b := Xs.Y.k.oneTime.codes.lengthsOk) (by simp [Key.sourceClauses])
  have hr := Johnson.RunOne.KeyPay.clause_of_ok hD.ok (n := "ranges")
    (b := Wf.admitted Xs.Y.k.oneTime.codes Xs.Y.k.oneTime.ranges
      (Wf.matrixOf Xs.Y.k.oneTime.lin)) (by simp [Key.sourceClauses])
  have hf := Johnson.RunOne.KeyPay.clause_of_ok hD.ok (n := "form")
    (b := Xs.Y.k.oneTime.ranges.choice.masksRide && Xs.Y.k.shared.lin.choice.masksRide &&
      Xs.Y.k.shared.lin.masksAhead && Xs.Y.k.shared.lin.sharedSplitNeeded &&
      !Xs.Y.k.shared.lin.ownSplitNeeded) (by simp [Key.sourceClauses])
  simp only [Bool.and_eq_true] at hf
  unfold Wf.admitted at hr
  simp only [Bool.and_eq_true] at hr
  rw [← hs.1, ← hs.2] at h3
  refine ⟨hl, hr.2, h3, hf.1.1.1.1, ?_⟩
  rw [hs.2]
  exact hf.1.1.2

/-- **If a key file's description passes its tests on the plan, a table is sent along with the
lookups' own message and with W**: msgFold and wFold name folds. So key_msg_ride_tie and
key_w_ride_tie are not vacuous. -/
theorem key_folds_some (Xs : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N P).planOk = true) :
    (∃ n Fd, msgFold Xs.Y.k.oneTime.ranges = some (n, Fd)) ∧
      ∃ n Fd, wFold Xs.Y.k.oneTime.lin = some (n, Fd) := by
  obtain ⟨-, h1, h2, h3, h4⟩ := key_plan_facts Xs N P hp
  obtain ⟨s, hs⟩ := head_of_ioppOk h1
  obtain ⟨t, ht⟩ := head_of_ioppOk h2
  have e1 : msgFold Xs.Y.k.oneTime.ranges = some (1, { ioppFoldShape s {} with
      maskLeafClass := Xs.Y.k.oneTime.ranges.message.leafClass }) := by
    simp only [msgFold, hs, h3, if_true]
  have e2 : wFold Xs.Y.k.oneTime.lin = some (if Xs.Y.k.oneTime.lin.ownSplitNeeded then 2 else 1,
      { ioppFoldShape t {} with maskLeafClass := Xs.Y.k.oneTime.lin.wLeafClass }) := by
    simp only [wFold, h4, if_true, ht, Option.map_some]
  exact ⟨⟨_, _, e1⟩, ⟨_, _, e2⟩⟩

/-- **If a key file's description passes its tests on the plan, the shape has a message for W**, so
keyPars has three entries. -/
theorem key_w_there (Xs : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N P).planOk = true) :
    (∃ msg, linMessageW Xs.Y.k.oneTime.lin = some msg) ∧ (keyPars Xs).length = 3 := by
  obtain ⟨-, -, h2, -, h4⟩ := key_plan_facts Xs N P hp
  obtain ⟨t, ht⟩ := head_of_ioppOk h2
  have hm : ∃ msg, linMessageW Xs.Y.k.oneTime.lin = some msg := by
    unfold linMessageW linMaskNotice
    rw [h4, ht]
    exact ⟨_, rfl⟩
  obtain ⟨msg, hm'⟩ := hm
  refine ⟨⟨msg, hm'⟩, ?_⟩
  unfold keyPars
  dsimp only
  rw [hm']
  rfl

/-- What Key.stagesAsSized says of the codes: the two lists of stages have one length, and stage by
stage the two codes under the stage's two numbers are there, and the stage's sized numbers C and Z
are those codes' three numbers. -/
theorem sized_codes {codes : Codes} {st : List IoppStage} {N : H2U.PlaceNums}
    (h : Key.stagesAsSized codes st N = true) :
    N.nums.stages.length = st.length ∧
      ∀ x ∈ N.nums.stages.zip st, ∃ c z, codes.base[x.2.code]? = some c ∧
        codes.mask[x.2.maskCode]? = some z ∧ x.1.C = ⟨c.logN, c.ell, c.r⟩ ∧
        x.1.Z = ⟨z.logN, z.ell, z.r⟩ := by
  unfold Key.stagesAsSized at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1.1, fun x hx => ?_⟩
  have h1 := h.2 x hx
  split at h1
  · rename_i c z hc hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨c, z, hc, hz, h1.1.1.1, h1.1.1.2⟩
  · cases h1

/-- **If a key file's description passes its tests on the plan, the numbers from which its ranges'
test and its test on the request's own group are made have the k, h and codes' numbers of the stages
of the one-time chain's two tests.** -/
theorem key_stages_tie (Xs : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N P).planOk = true) :
    ((N.nums.stages.map fun y => (y.k, y.h)) =
        (Xs.Y.k.oneTime.ranges.stages.map fun s => (s.k, s.h)) ∧
      N.idx = Xs.Y.k.oneTime.ranges.stages.map fun s => (s.code, s.maskCode)) ∧
    ((P.W.nums.stages.map fun y => (y.k, y.h)) =
        (Xs.Y.k.oneTime.lin.testOwn.map fun s => (s.k, s.h)) ∧
      P.W.idx = Xs.Y.k.oneTime.lin.testOwn.map fun s => (s.code, s.maskCode)) := by
  have hD := Johnson.RunOne.KeyPay.fileOkD_of ((FileDescription.planOk_ok _).1 hp).fileOk
  have hs : Xs.Y.k.oneTime.lin = Xs.Y.k.shared.lin := by
    have h1 := hD.more ("chains 1 and 2 hold the same codes and the same shape, by value",
      decide (Xs.Y.k.oneTime.codes = Xs.Y.k.shared.codes) &&
        decide (Xs.Y.k.oneTime.lin = Xs.Y.k.shared.lin)) (by simp [Key.shapeClauses])
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.2
  refine ⟨sized_maps hD.stagesRng, ?_⟩
  rw [hs]
  exact sized_maps hD.stagesOwn

/-- **The same at the description's own members.** RowK12Key holds (key_sits_row needs no premise).
The parameters of the ranges' test and of the test on the request's own group have the k, h and
codes' numbers of the stages of the matching test of the one-time chain (ranges.stages,
lin.testOwn). The stage at which each test's first fold is made is the first stage of the matching
test, whole. -/
theorem key_member_tie (Xs : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N P).planOk = true) :
    H2K.JointK.RowK12Key Xs N P ∧
      ((((Key.rangesParams N).nums.stages.map fun y => (y.k, y.h)) =
          (Xs.Y.k.oneTime.ranges.stages.map fun s => (s.k, s.h)) ∧
        (Key.rangesParams N).idx =
          Xs.Y.k.oneTime.ranges.stages.map fun s => (s.code, s.maskCode)) ∧
      ∃ y s, (Key.rangesParams N).nums.stages.head? = some y ∧
        Xs.Y.k.oneTime.ranges.stages.head? = some s ∧
        K12.stageAt (Key.rangesParams N) 0 y = some s) ∧
      (((H2K.JointK.pOwnK P).nums.stages.map fun y => (y.k, y.h)) =
          (Xs.Y.k.oneTime.lin.testOwn.map fun s => (s.k, s.h)) ∧
        (H2K.JointK.pOwnK P).idx =
          Xs.Y.k.oneTime.lin.testOwn.map fun s => (s.code, s.maskCode)) ∧
      ∃ y s, (H2K.JointK.pOwnK P).nums.stages.head? = some y ∧
        Xs.Y.k.oneTime.lin.testOwn.head? = some s ∧
        K12.stageAt (H2K.JointK.pOwnK P) 0 y = some s := by
  have R := H2K.JointK.key_sits_row Xs N P
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := key_stages_tie Xs N P hp
  obtain ⟨-, h1, h2, -, -⟩ := key_plan_facts Xs N P hp
  obtain ⟨s, hs⟩ := head_of_ioppOk h1
  obtain ⟨t, ht⟩ := head_of_ioppOk h2
  have i1 : (Key.rangesParams N).idx = N.idx :=
    H2K.Sizes.idx_of_planOk Key.rangesPlace N (R.plans hp).1
  have i2 : (H2K.JointK.pOwnK P).idx = P.W.idx :=
    H2K.Sizes.idx_of_planOk ⟨3, none, 2, .K12⟩ P.W (R.plans hp).2.2.2
  have T1 : ((Key.rangesParams N).nums.stages.map fun y => (y.k, y.h)) =
        (Xs.Y.k.oneTime.ranges.stages.map fun s => (s.k, s.h)) ∧
      (Key.rangesParams N).idx =
        Xs.Y.k.oneTime.ranges.stages.map fun s => (s.code, s.maskCode) := by
    rw [(R.nums hp).1, i1]
    exact ⟨a1, a2⟩
  have T2 : ((H2K.JointK.pOwnK P).nums.stages.map fun y => (y.k, y.h)) =
        (Xs.Y.k.oneTime.lin.testOwn.map fun s => (s.k, s.h)) ∧
      (H2K.JointK.pOwnK P).idx =
        Xs.Y.k.oneTime.lin.testOwn.map fun s => (s.code, s.maskCode) := by
    rw [(R.nums hp).2.2.2, i2]
    exact ⟨b1, b2⟩
  obtain ⟨y, hy, e1⟩ := first_fold_stage T1 hs
  obtain ⟨z, hz, e2⟩ := first_fold_stage T2 ht
  exact ⟨R, ⟨T1, y, s, hy, hs, e1⟩, T2, z, t, hz, ht, e2⟩

/-- **If the description passes its tests on the plan: the table that is sent along with the
lookups' own message has the k, h and codes' numbers of the first stage of N, from which the ranges'
test is made.** -/
theorem key_msg_ride_tie (Xs : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N P).planOk = true) {n : Nat} {Fd : FoldShape}
    (hw : msgFold Xs.Y.k.oneTime.ranges = some (n, Fd)) :
    (∃ y, N.nums.stages.head? = some y ∧ y.k = Fd.layout.k ∧ y.h = Fd.layout.h) ∧
      N.idx.head? = some (Fd.code, Fd.maskCode) := by
  obtain ⟨s, hs, e1, e2, e3, e4⟩ := msgFold_spec hw
  rw [e1, e2, e3, e4]
  exact first_stage_tie (key_stages_tie Xs N P hp).1 hs

/-- **If the description passes its tests on the plan: the table that is sent along with a key
file's W has the k, h and codes' numbers of the first stage of P.W, from which the test on the
request's own group is made.** -/
theorem key_w_ride_tie (Xs : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N P).planOk = true) {n : Nat} {Fd : FoldShape}
    (hw : wFold Xs.Y.k.oneTime.lin = some (n, Fd)) :
    (∃ y, P.W.nums.stages.head? = some y ∧ y.k = Fd.layout.k ∧ y.h = Fd.layout.h) ∧
      P.W.idx.head? = some (Fd.code, Fd.maskCode) := by
  obtain ⟨s, hs, e1, e2, e3, e4⟩ := wFold_spec hw
  rw [e1, e2, e3, e4]
  exact first_stage_tie (key_stages_tie Xs N P hp).2 hs

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.maps_eq_of_zip
#print axioms OnBytes.SendSim.Seat.head_of_maps
#print axioms OnBytes.SendSim.Seat.wFold_spec
#print axioms OnBytes.SendSim.Seat.msgFold_spec
#print axioms OnBytes.SendSim.Seat.first_stage_tie
#print axioms OnBytes.SendSim.Seat.first_fold_stage
#print axioms OnBytes.SendSim.Seat.head_of_ioppOk
#print axioms OnBytes.SendSim.Seat.front2_of_plan
#print axioms OnBytes.SendSim.Seat.own_test_of_plan
#print axioms OnBytes.SendSim.Seat.w_fold_some
#print axioms OnBytes.SendSim.Seat.w_codes_tie
#print axioms OnBytes.SendSim.Seat.w_stages_tie
#print axioms OnBytes.SendSim.Seat.w_ride_tie
#print axioms OnBytes.SendSim.Seat.w_member_tie
#print axioms OnBytes.SendSim.Seat.first_ride_tie
#print axioms OnBytes.SendSim.Seat.first_member_tie
#print axioms OnBytes.SendSim.Seat.sized_maps
#print axioms OnBytes.SendSim.Seat.key_plan_facts
#print axioms OnBytes.SendSim.Seat.key_folds_some
#print axioms OnBytes.SendSim.Seat.key_w_there
#print axioms OnBytes.SendSim.Seat.sized_codes
#print axioms OnBytes.SendSim.Seat.key_stages_tie
#print axioms OnBytes.SendSim.Seat.key_member_tie
#print axioms OnBytes.SendSim.Seat.key_msg_ride_tie
#print axioms OnBytes.SendSim.Seat.key_w_ride_tie
