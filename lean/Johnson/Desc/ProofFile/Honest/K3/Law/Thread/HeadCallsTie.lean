-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadCallsTie.lean: for the callers of the lookup on the
calls of the head's link (link 24; number 340 of the first chain's flat list): a text for what that
lookup returns, made of the public shape and of the challenges heard alone. Under the library's
hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): what the fold's state right behind that lookup's
member holds as the returned structure agrees with that text in the eleven fields of `OpenSame`
(Honest/K3/HeardWhole.lean); and, six numbers on, at the fold over the first 346 members: each
call's key point in what the head's own rounds heard is that text's. Four definitions; theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a number such as 340 or 346 counts members of the first
chain's flat list. The fold is `foldBlocks` (Johnson/Desc/Block.lean) over the first members of that
list. `lookHeardAt` (Honest/K3/HeardWhole.lean) is the structure that a shape, a base and a list of
challenges make.

What is shown.
  `headCallsShape Z`: the shape of the site on the calls at link 24; the default shape where the
    list of sites has none.
  `headLookOfK3 Z c`: the text, as a function of the chain's challenges from its first round on:
    `lookHeardAt` at that shape and at the number of rounds of the first 340 members.
  `headKeysOfK3 c`: its field zk, each call's key point, in the type in which another kind's
    statement (see Users) has a free letter for it; the second argument is not read.
  `HeadG1At v s`: the sentence that is carried from 342 to 346: the state stands in the head's link;
    what the head's own rounds heard is laid; the ledger has its sizes; that hearing's copy of the
    lookup's structure has v as its key points.
  `head_calls_site_found`: under `P5J.AtMgA` the list of sites has a site on the calls at link 24,
    and `headCallsShape` is its shape.
  `head_calls_tie`: the tie behind 340, in all eleven fields, from every first state; the list of
    challenges may go on behind the lookup's own rounds (the letter back).
  `HeadG1At.kept`: the sentence stays where the library's `KeptW`
    (Johnson/Desc/Kinds/Law/WeightAtSame.lean) holds.
  `HeadG1At.here`: two of its clauses alone.
  `rounds_346_cut`: the rounds of the first 346 members are those of the first 341 and of five
    members more.
  `head_keys_tie`: the tie at 346, from the description's own first state, in the form in which
    another kind's statement asks it.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`. No public test, no site and nothing on the ledger is
    assumed.
  `hfold`, `hH`: (in `head_calls_tie`) a fold over the first 341 members returns; the state behind
    reads H as the lookup's structure.
  Inside `head_keys_tie`: a fold over the first 346 members returns; no mark; the asked reply is
    heard; the state stands in the head's link and holds what the head's own rounds heard. "No mark"
    and "the asked reply is heard" are among the hypotheses for the sake of the form named under
    Users; the proof does not use them.
  `hG`, `K`: (in `HeadG1At.kept`, `HeadG1At.here`) the carried sentence; the library's `KeptW`.

How the proof goes. At 340 the lookup's member sets the state's field lookHeard, and nothing of what
the head's own rounds hear (`calls_here`, Honest/K3/Law/Thread/StateHere.lean). At 341 the head's
own sub-protocol lays what it heard, whole; its field g1 is a copy of lookHeard: the library's
`g1_behind` (Johnson/Desc/Kinds/Law/LeftTiesInScope.lean), over `P4.yes_341`
(Johnson/P4R/WaK6At346.lean). At 342, 343, 344 and 345 what was heard stays as it is: the library's
`KeptW`, by `P4.kept_342`, `kept_343`, `kept_344` and `digits_345` (WaK6At346.lean). The last asks
that the ledger has its sizes: this comes from `P4.wellLaid_341` (Johnson/P4R/FreeAt341N.lean) at
what the fold's first 341 members reach, from `blockAt_later` (Johnson/Desc/Kinds/Law/KeepsAt.lean),
and then from the last clause of `KeptW` itself. The fold is cut at its end five times:
`IM.fold_last` (Johnson/IMR/SendsFold.lean).

Follows. `head_calls_tie` follows `layers_tie_head` (Honest/K3/Law/Thread/LayersTieHead.lean), which
has the like at the twelve layers' links. The way from 341 to 346, the carried sentence and how the
ledger's sizes travel are those of the honest part of the kind K11's files, which
carry three other fields of the same hearing so (Honest/K11/ThreeTiesBare.lean and
Honest/K11/ThreeTies.lean: `TiesAt`, `TiesAt.kept`, `threeTiesAlongBareFold`); seventeen lines of
the proof of `head_keys_tie` on the ledger at 341 (from `hR` to the equation of o) are theirs,
eighteen lines there, but for the letters, names spelled out or short, one line broken in two, and
"_ _" for "rs' gs'". Nothing of theirs is imported.

Users. `HeadClaimIsOfKeysBare` (Honest/K11/ThreeTiesBareStatement.lean; there a definition of a
proposition) has, as the one
tie that is left of four, a hypothesis on a free letter keys. `head_keys_tie` is that hypothesis at
keys := `headKeysOfK3 cF`, except that the number of rounds of the first j members is written out
here: `((cF.blocksInOrder.take j).flatMap (·.rounds)).length`. The term `roundsAhead cF.blocksInOrder j` is by its
definition that term (Johnson/Desc/K13/Honest/FoldCut.lean;
not imported). The
composition over `head_keys_tie` stands in K11's files and in K13's files
(Honest/K11/ClaimIsOfK3.lean, Honest/K13/AcceptedAtAnyK3.lean).

What lies beneath, among others:
  Honest/Thread/First, FirstAt, HeardLaw,
    KeepsBy, MadeLaw, PaysLaw, Shape; Honest/BookOf, ForKinds, Sum;
  Johnson/Desc/First/Shape/Chain, Parts, Tail;
    Honest/Frame, Side, Law/Cut, Law/Play;
  Honest/SumLaw/Law, LawEnds, Statement, Terms;
    Honest/Member/AtLot, InSegment;
  Johnson/Desc/K9/Honest/SlotsLive.
These come in through LayersTieHead.lean; this file imports none of them directly.
None of the other files
that are named under Follows and Users lies beneath.

Limits. On the verifier's side alone. At the full size alone: that limit comes with `P5J.AtMgA`. At
the list that runs (cF.blocksInOrder) alone: the like at the list with the test in front of each member is
not here. This file shows of no rounds that a fold returns. No instance of these hypotheses is
exhibited in this file. `head_keys_tie` shows one of three things that the other kind's statement
leaves open, not that statement's conclusion.
The line `attribute [-instance] Inst.Model.Scl.ref` takes that instance of the library's out of the
search for instances in this file: no default table of scales is in sight: a statement that reads a
table says which. What the text is not, as LayersTieHead.lean says of its own text: the eight other
fields of the structure are blank in it; it computes the fields tT and leavesA, which are costly to
compute; it is evaluated at no data in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LayersTieHead
import Johnson.P4R.WaK6At346
import Johnson.P4R.FreeAt341N
import Johnson.Desc.Kinds.Law.LeftTiesInScope
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (HeadOwn Here)
open VerifiableInference.Desc.Sound (step_ok_iff)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (reach_of_fold)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

local notation "FS" => VerifiableInference.Desc.First.S

/-- The shape of the site on the calls at link 24. Where the list of sites has none it is the
default shape, without a warning: under `P5J.AtMgA` that does not happen (`head_calls_site_found`).
-/
def headCallsShape (Z : Pub) : OnBytes.Model.Forest.Shape :=
  (((lookSites Z).find? fun s => s.link == 24 && !s.digits).map (·.shape)).getD default

/-- **The text**: what the lookup on the calls of link 24 returns, as far as it depends on the
public shape and the challenges alone. -/
def headLookOfK3 (Z : Pub) (c : Chain FS ProofFile.Cl) :
    List Fmt.Drawn → OnBytes.Model.Forest.Heard :=
  fun hd => lookHeardAt (headCallsShape Z) ((c.blocksInOrder.take 340).flatMap (·.rounds)).length hd

/-- **Each call's key point, by that text.** The second argument is not read. -/
def headKeysOfK3 (c : Chain FS ProofFile.Cl) : Pub → Ground → List Fmt.Drawn → Array (Array E) :=
  fun Z _ hd => (headLookOfK3 Z c hd).zk

/-- **The sentence that is carried from 342 to 346.** -/
def HeadG1At (v : Array (Array E)) (s : FS) : Prop :=
  ∃ (a : HeadOwn) (hx : OnBytes.Model.Head.Heard), s.here = .head a ∧ a.x = some hx ∧
    Sized a.F ∧ hx.g1.zk = v

/-- **It stays where the sub-protocol between keeps what the library's sentence reads.** Conditional
on the sentence in front and on `KeptW`. No instance of these hypotheses is exhibited in this file.
-/
theorem HeadG1At.kept {v : Array (Array E)} {s t : FS} (hG : HeadG1At v s) (K : KeptW s t) :
    HeadG1At v t := by
  obtain ⟨a, hx, ha, hax, hz, e⟩ := hG
  obtain ⟨o, o', ho, ho', ex, _, _, _, _, _, hL⟩ := K
  obtain rfl : a = o := Here.head.inj (ha.symm.trans ho)
  exact ⟨o', hx, ho', ex.trans hax, hL.sized hz, e⟩

/-- Of the sentence: the state stands in the head's link, and the ledger there has its sizes.
Conditional on the sentence. No instance of these hypotheses is exhibited in this file. -/
theorem HeadG1At.here {v : Array (Array E)} {s : FS} (hG : HeadG1At v s) :
    ∃ a : HeadOwn, s.here = .head a ∧ Sized a.F := by
  obtain ⟨a, _, ha, _, hz, _⟩ := hG
  exact ⟨a, ha, hz⟩

/-- **The rounds of the first 346 members are those of the first 341 and of five members more.** -/
theorem rounds_346_cut {S Cl : Type} (l : List (Block S Cl)) :
    ((l.take 346).flatMap (·.rounds)).length =
      ((l.take 341).flatMap (·.rounds)).length +
        (((l.drop 341).take 5).flatMap (·.rounds)).length := by
  have e : l.take 346 = l.take 341 ++ (l.drop 341).take 5 := List.take_add (i := 341) (j := 5)
  rw [e, List.flatMap_append, List.length_append]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under `P5J.AtMgA` the list of sites has a site on the calls at link 24, and `headCallsShape` is
its shape. Conditional on `P5J.AtMgA`. No instance of these hypotheses is exhibited in this file. -/
theorem head_calls_site_found (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ s ∈ lookSites Zp, s.link = 24 ∧ s.digits = false ∧ headCallsShape Zp = s.shape := by
  obtain ⟨s₀, hs₀, e1, e2, _, _⟩ := site_calls_head h 24 (by omega)
  cases hf : (lookSites Zp).find? fun s => s.link == 24 && !s.digits with
  | none =>
    have h0 := List.find?_eq_none.1 hf s₀ hs₀
    rw [e1, e2] at h0
    simp at h0
  | some s =>
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    refine ⟨s, List.mem_of_find?_eq_some hf, hp.1, hp.2, ?_⟩
    unfold headCallsShape
    rw [hf]
    rfl

/-- **The tie behind 340, in all eleven fields, from every first state.** Conditional on
`P5J.AtMgA`; on a fold over the first 341 members that returns; on what the state behind reads as
the lookup's structure. No instance of these hypotheses is exhibited in this file. -/
theorem head_calls_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (s₀ : TS) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (sj : TS) (rr : List Fmt.RoundView)
    (c : List OpenedColumn) (H : OnBytes.Model.Forest.Heard) (back : List Fmt.Drawn)
    (hfold : foldBlocks 0 (cF.blocksInOrder.take 341) s₀ rs cols = .ok (sj, rr, c))
    (hH : sj.lookHeard? = some H) :
    OpenSame H (headLookOfK3 Zp cF
      ((rs.take ((cF.blocksInOrder.take 341).flatMap (·.rounds)).length).map (·.drawn) ++ back)) := by
  obtain ⟨s, hs, e1, e2, eS⟩ := head_calls_site_found h
  have hl : s.link < 25 := by omega
  obtain ⟨blk, hblk0, _⟩ := member_at_link h 24 (by omega) false
  have hblk : cF.blocksInOrder[340]? = some blk := hblk0
  obtain ⟨t, rs', cols', n, hfront, hstep⟩ := IM.fold_last hblk hfold
  obtain ⟨er, hle⟩ := fold_rest 0 _ _ _ _ _ _ _ hfront
  obtain ⟨Fd, Bs, base, A, B, lot, O, hlot, hbs, hm⟩ := site_hub h s hs hl
  have hb' : cF.blocksInOrder[borderOf s.link s.digits]? = some blk := by
    rw [e1, e2]
    exact hblk
  obtain ⟨m1, m2, m3⟩ := hm blk hb'
  obtain ⟨F, H', G, _, _, hv, hC, _⟩ := calls_here _ _ _ _ Fd Zp Bs base cF A B O s hs e2 lot blk
    hlot hbs m1 m2 m3 0 t sj n _ cols' hstep
  have eH : H = H' := by
    rcases hC with ⟨q, _, e⟩ | ⟨q, _, e⟩ | ⟨q, _, hq, e⟩
    · rw [e] at hH
      exact (Option.some.inj hH).symm
    · rw [e] at hH
      exact (Option.some.inj hH).symm
    · rw [e] at hH
      have hH' : (if q.opened = true then some H' else none) = some H := hH
      rw [if_pos hq] at hH'
      exact (Option.some.inj hH').symm
  have hsh : s.p.shape = some s.shape := by
    have hs' := hs
    unfold lookSites at hs'
    obtain ⟨a, _, hsa⟩ := List.mem_filterMap.1 hs'
    exact (site_facts _ _ a s hsa).2.1
  have W := heardWhole_of_hearVia s.p s.shape hsh F G _ H'
    ((rs.take ((cF.blocksInOrder.take 340).flatMap (·.rounds)).length).map (·.drawn)) back hv
  have eL : ((rs.take ((cF.blocksInOrder.take 340).flatMap (·.rounds)).length).map
      (·.drawn)).length = ((cF.blocksInOrder.take 340).flatMap (·.rounds)).length := by
    rw [List.length_map, List.length_take]
    exact Nat.min_eq_left hle
  have eA : ((cF.blocksInOrder.take 341).flatMap (·.rounds)).length =
      ((cF.blocksInOrder.take 340).flatMap (·.rounds)).length + blk.rounds.length := by
    rw [show 341 = 340 + 1 from rfl, List.take_add_one, hblk]
    simp
  rw [eL, er, ← List.map_append, ← List.take_add, ← eA] at W
  rw [eH]
  unfold headLookOfK3
  rw [eS]
  exact W

/-- **The tie at 346: each call's key point in what the head's own rounds heard, from the
description's own first state.** Conditional on `P5J.AtMgA` and on the five hypotheses inside the
statement, which the head lists. No instance of these hypotheses is
exhibited in this file. -/
theorem head_keys_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : Ground) :
    ∀ (ξ : ProofFile.Inst) rs cols sj c,
      foldBlocks 0 (cF.blocksInOrder.take 346) (ProofFile.startS Zp ξ.pub) rs cols =
        .ok (sj, rs.drop ((cF.blocksInOrder.take 346).flatMap (·.rounds)).length, c) →
      sj.failed = none → sj.out.reply = some ξ.asked →
      ∀ a hx, sj.here = .head a → a.x = some hx →
        hx.g1.zk = headKeysOfK3 cF Zp G
          ((rs.take ((cF.blocksInOrder.take 346).flatMap (·.rounds)).length).map (·.drawn)) := by
  intro ξ rs cols sj c hfold _ _ a hx ha hax
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b5, hb50, _⟩ := member_at_link h 24 (by omega) true
  have hb5 : cF.blocksInOrder[345]? = some b5 := hb50
  have hlen : 345 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb5).1
  obtain ⟨b4, hb4⟩ : ∃ b, cF.blocksInOrder[344]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨b3, hb3⟩ : ∃ b, cF.blocksInOrder[343]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨b2, hb2⟩ : ∃ b, cF.blocksInOrder[342]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨b1, hb1⟩ : ∃ b, cF.blocksInOrder[341]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨t5, r5, c5, n5, hf5, hs5⟩ := IM.fold_last hb5 hfold
  obtain ⟨t4, r4, c4, n4, hf4, hs4⟩ := IM.fold_last hb4 hf5
  obtain ⟨t3, r3, c3, n3, hf3, hs3⟩ := IM.fold_last hb3 hf4
  obtain ⟨t2, r2, c2, n2, hf2, hs2⟩ := IM.fold_last hb2 hf3
  obtain ⟨t1, r1, c1, n1, hf1, hs1⟩ := IM.fold_last hb1 hf2
  have hd5 := ((step_ok_iff 0 b5 t5 sj _ c5 n5).1 hs5).2.2.2
  have hd4 := ((step_ok_iff 0 b4 t4 t5 _ c4 n4).1 hs4).2.2.2
  have hd3 := ((step_ok_iff 0 b3 t3 t4 _ c3 n3).1 hs3).2.2.2
  have hd2 := ((step_ok_iff 0 b2 t2 t3 _ c2 n2).1 hs2).2.2.2
  have hd1 := ((step_ok_iff 0 b1 t1 t2 _ c1 n1).1 hs1).2.2.2
  have y1 := P4.yes_341 h.scope h.reads O hb1 hd1
  obtain ⟨gk, X0, o, hgk, ho, hoX, hg1⟩ := InScope.g1_behind _ _ _ _ y1
  have hT := head_calls_tie h _ rs cols t1 r1 c1 gk
    (((rs.drop ((cF.blocksInOrder.take 341).flatMap (·.rounds)).length).take
      (((cF.blocksInOrder.drop 341).take 5).flatMap (·.rounds)).length).map (·.drawn)) hf1 hgk
  rw [← List.map_append, ← List.take_add, ← rounds_346_cut] at hT
  have hR : Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (ξ.pub, t1) :=
    reach_of_fold (start := ProofFile.startS Zp) (z := ξ.pub) 341 (by omega) t1 rs _ cols c1 hf1
  have hW := P4.wellLaid_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hR Bs.G₀.W.hS
    (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs.G₀.W)
  obtain ⟨a0, F1, X1, Q, _, hop, _, e⟩ := Came.decide_record _ _ _ _ y1
  have ho2 : t2.here = .head { a0 with F := F1, x := some X1, squaresP := some Q } := by rw [e]
  have eL : (seatAt Bs.G₀.W.hS
      (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs.G₀.W)).ledger t2 = F1 := by
    rw [e]
    show (VerifiableInference.Desc.First.S.fork? _).getD {} = F1
    simp [VerifiableInference.Desc.First.S.fork?, hop]
  have hz2 : Sized ({ a0 with F := F1, x := some X1, squaresP := some Q } : HeadOwn).F := by
    have hL := blockAt_later _ _ _ _ t1 t2 _ _ y1
    rw [eL] at hL
    exact hL.sized (sized_of_wellLaid hW)
  obtain rfl : o = { a0 with F := F1, x := some X1, squaresP := some Q } :=
    Here.head.inj (ho.symm.trans ho2)
  have g2 : HeadG1At (headKeysOfK3 cF Zp G
      ((rs.take ((cF.blocksInOrder.take 346).flatMap (·.rounds)).length).map (·.drawn))) t2 :=
    ⟨_, X0, ho, hoX, hz2, by rw [hg1]; exact hT.zk⟩
  have g3 := g2.kept (P4.kept_342 h.scope h.reads O hb2 hd2 ho)
  obtain ⟨a3, ha3, _⟩ := g3.here
  have g4 := g3.kept (P4.kept_343 h.scope h.reads O hb3 hd3 ha3)
  obtain ⟨a4, ha4, _⟩ := g4.here
  have g5 := g4.kept (P4.kept_344 h.scope h.reads O hb4 hd4 ha4)
  obtain ⟨a5, ha5, hz5⟩ := g5.here
  have g6 := g5.kept (P4.digits_345 h.scope h.reads O h.laid.planOk hb5 hd5 ha5 hz5).1
  obtain ⟨a', hx', ha', hax', _, e6⟩ := g6
  obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
  obtain rfl : hx' = hx := Option.some.inj (hax'.symm.trans hax)
  exact e6

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.HeadG1At.kept
#print axioms ProofFile.Honest.K3.Law.AtThr.HeadG1At.here
#print axioms ProofFile.Honest.K3.Law.AtThr.rounds_346_cut
#print axioms ProofFile.Honest.K3.Law.AtThr.head_calls_site_found
#print axioms ProofFile.Honest.K3.Law.AtThr.head_calls_tie
#print axioms ProofFile.Honest.K3.Law.AtThr.head_keys_tie
