-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- Statements and ties read once; proofs not read; the two lines beside
-- leftOn_open347 came after that reading, on its word.
/-
Johnson/Desc/ProofFile/Honest/K6/Term/Values.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of the
online proof): THE PROOFS OF THE STATEMENTS OF Honest/K6/Term/ValuesStatements.lean: what this kind
owes to "the run on shapes": its test on values at member 341, and its four rows' tests at the
batching member 347.

WHAT IT IS NOT. What that file's head says of the statements holds of the theorems: none says that a
verifier or a member's step accepts; the eight at a border stand under the library's hypothesis on
the first chain and say nothing where the thread's invariant holds at no run; of the batching's test
they pay four rows' share alone. Closed facts on the promise's table are evaluated by Lean's kernel
(leftOn_open347 and the two lines beside it); they are replayed by no independent checker. At 341
the road stands over two elder files of this kind's that lie in no sealed tree
(Honest/K6/Law/FrontedAtHead.lean, FrontAt.lean); at 347 and along the rows every law that is called
lies in the sealed tree. Nothing on soundness or on what a proof hides.

WHAT IT IS. Calls and ties; no new mathematics.
  BY WHICH ROADS, at 341. The state in front is ready (k6Front_at_head,
  Honest/K6/Law/FrontedAtHead.lean): its fields "start" and "letters" are what k6V tests
  (headTest_of_front; the library's test_of_pointsOk, Kinds/Law/K6GivenOfLeft.lean).
  BY WHICH ROADS, at 347. This kind's member closes the promise's item "what the lookup on the calls
  left" (left 24) and opens the form of it that stands at later states (leftOn 24); that item is
  open from behind this kind's member up to the batching's front, and neither in front of the one
  nor behind the other (leftOn_open347, leftOn_openFromTheHeadToTheBatching, leftOn_shutOutside).
  So the thread's clause on the promise gives the sentence k3LeftOnItemAt at border 347
  (leftOn_of_thread); it holds the record and how its key points are made; with the test on public
  numbers keysFitB, a theorem in the goals' scope, that is PointsOk (pointsOk_of_leftOn), whose
  second half is endsB (endsTest_of_pointsOk).
  ALONG THE ROWS. The draw carries EndsHeard (the library's endsHeard_draw). Every run writes the
  ledger or the smallness test's parameters alone: each state behind is a putFork or a putTl of the
  state in front, the state itself, or (the merge) the head's own record with another ledger. None
  writes the record.
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.ValuesStatements
import Johnson.Desc.ProofFile.Honest.K6.Law.FrontedAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Chain Strs Place Claim named)
open VerifiableInference.Desc.First (S Pub flatPlacesOf)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgMore pubQ linksFull CellsQ)
open VerifiableInference.Desc.Kinds (Head.Par)
open VerifiableInference.Desc.Kinds.Head (parOf startOk kind asClaim seatAt callerKeys)
open VerifiableInference.Desc.Kinds.Head.Law (workOf workAtW K6Front PointsOk test_of_pointsOk
  keysFitB pointsOk_of_raw)
open VerifiableInference.Desc.Kinds.Head.Shape (endsB EndsHeard endsHeard_draw three_strong
  join_strong)
open VerifiableInference.Desc.K3 (seatCalls planesRun Readers joinRun)
open VerifiableInference.Desc.K9 (Where atS drawAlone)
open VerifiableInference.Desc.K9.Shape (guardRun guardRun_iff)
open VerifiableInference.OnPublicFiles (objectsRun guestsRun seatOf guestsRun_nil k3LeftOnItem
        k3LeftOnItemAt)
open Johnson.AtFull.Shape (k6V endsS rowsHead tabOf firstZA preAllT Tab.g Tab.vals Row eqBare
  cell_v cells_head)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Letters Script WtF lettersHead)

local notation "RunOfClaims" => VerifiableInference.Desc.K9.Shape.Run

/-! ## 1 Member 341 -/

/-- Where the state's own test on the request accepts, what the lookup heard is laid, and its points
are as the head's text asks: the table's test on values accepts. -/
theorem headTest_of_heard {W : OnBytes.Model.Verify.Public} {s : TS}
    {g : OnBytes.Model.Forest.Heard} (hst : startOk W s = true) (hg : s.lookHeard? = some g)
    (hP : @PointsOk (parOf W.hS (workOf W)).sizes (parOf W.hS (workOf W)).floor g.zx
      fun c => g.zk.getD c #[]) : k6V W s = true := by
  have ht := @test_of_pointsOk (parOf W.hS (workOf W)).sizes _ _ _ hP
  unfold k6V
  rw [Bool.and_eq_true]
  refine ⟨hst, ?_⟩
  rw [hg]
  exact ht

/-- At a state that is ready in front of the output head's own rounds, the table's test on values
accepts. -/
theorem headTest_of_front {W : OnBytes.Model.Verify.Public} {room : Nat} {s : TS}
    (R : K6Front W room s) : k6V W s = true := by
  obtain ⟨z, y, hz, -, hP⟩ := R.letters
  have hz' : (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = some z := hz
  obtain ⟨g, hg, e⟩ := Option.map_eq_some_iff.mp hz'
  rw [← e] at hP
  exact headTest_of_heard R.start hg hP

theorem headTestAcceptsAtTheBorder : HeadTestAcceptsAtTheBorder := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said k s m E hT
  obtain ⟨_, _, -, -, F⟩ := k6Front_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact headTest_of_front (F k s m E hT.1)

theorem valuesAtTheOutputHeadAtAnyShape : ValuesAtTheOutputHeadAtAnyShape := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said shape J fall hv
    blk _ k s m E ds y cols hT _ _ _ _ _
  rw [hv]
  exact headTestAcceptsAtTheBorder W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w Said k s m E hT

theorem valuesAtTheOutputHead : ValuesAtTheOutputHead := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said G J fall
  refine valuesAtTheOutputHeadAtAnyShape W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w Said _ J fall fun s rounds shown => ?_
  have hc : Johnson.AtFull.Shape.Tab.cells Zp G 341 =
      (Johnson.AtFull.Shape.Tab.headRow Zp G).at 4 :=
    cells_head Zp G 4 (by omega) rfl
  show Tab.vals Zp G 341 s rounds shown = _
  rw [cell_v hc]
  rfl

/-! ## 2 The form -/

theorem eachRowsTestGivesTheBatchingsTest : EachRowsTestGivesTheBatchingsTest := by
  intro runOf testOf names
  induction names with
  | nil => intro _ _ _; rfl
  | cons o os ih =>
    intro n s hAll
    show (testOf o n s &&
      match runOf o n s with
      | .ok y => preAllT runOf testOf os (n + y.1.length) y.2
      | .error _ => true) = true
    rw [hAll [] o os rfl n s rfl, Bool.true_and]
    cases hr : runOf o n s with
    | error e => rfl
    | ok y =>
      refine ih _ _ fun front name rest e count' state' hb =>
        hAll (o :: front) name rest (by rw [e]; rfl) count' state' ?_
      show (match runOf o n s with
        | .ok y => behindTheRuns runOf front (n + y.1.length) y.2
        | .error _ => none) = some (count', state')
      rw [hr]
      exact hb

/-- Where every run leaves what the lookup heard, so do runs one behind the other. -/
theorem behindTheRuns_keeps (runOf : Nat × String → RunOfClaims)
    (hk : ∀ name, KeepsWhatTheLookupHeard (runOf name)) (names : List (Nat × String)) :
    ∀ (start : Nat) (s : TS) (count : Nat) (state : TS),
      behindTheRuns runOf names start s = some (count, state) →
      state.lookHeard? = s.lookHeard? := by
  induction names with
  | nil =>
    intro start s count state e
    have e' : (start, s) = (count, state) := Option.some.inj e
    rw [← (Prod.mk.inj e').2]
  | cons o os ih =>
    intro start s count state e
    have e' : (match runOf o start s with
      | .ok y => behindTheRuns runOf os (start + y.1.length) y.2
      | .error _ => none) = some (count, state) := e
    cases hr : runOf o start s with
    | error _ => rw [hr] at e'; exact nomatch e'
    | ok y =>
      rw [hr] at e'
      exact (ih _ _ _ _ e').trans (hk o start s y hr)

/-! ## 3 The eleven runs leave what the lookup heard -/

theorem objects_keep (digits : Bool) :
    KeepsWhatTheLookupHeard (objectsRun (seatOf K3Lot.ofForm digits)) := by
  intro n s z hz
  unfold objectsRun at hz
  cases hF : (seatOf K3Lot.ofForm digits).fork s with
  | none => simp [hF, named, bind, Except.bind] at hz
  | some F =>
    cases hg : (seatOf K3Lot.ofForm digits).heard s with
    | none => simp [hF, hg, named, bind, Except.bind] at hz
    | some g =>
      simp only [hF, hg, named, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hz
      subst hz
      show ((seatOf K3Lot.ofForm digits).mark s _).lookHeard? = s.lookHeard?
      rw [ProofFile.Honest.K3.Shape.mark_is]
      exact S.look_putFork s _

theorem guests_keep : KeepsWhatTheLookupHeard
    (guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest TS Claim))) := by
  intro n s z hz
  rw [guestsRun_nil] at hz
  obtain rfl := Except.ok.inj hz
  rfl

theorem planes_keep (planesLog : Nat) (readers : Readers TS) :
    KeepsWhatTheLookupHeard (planesRun (seatCalls K3Lot.ofForm) planesLog readers) := by
  intro n s z hz
  obtain ⟨G, e⟩ := P4.planesRun_putFork K3Lot.ofForm planesLog readers n s z hz
  rw [e]
  exact S.look_putFork s G

theorem equations_keep : KeepsWhatTheLookupHeard eqBare := by
  intro n s z hz
  have hz' : VerifiableInference.Desc.First.K8.atRecord (fun p =>
      (equations (p.F.nClaim + n) p.tl p.funs p.F).map fun x =>
        (x.2.2, { p with tl := x.1, F := x.2.1 })) s = .ok z := hz
  unfold VerifiableInference.Desc.First.K8.atRecord at hz'
  cases hq : k8PartP.get? s with
  | none => rw [hq] at hz'; exact nomatch hz'
  | some q =>
    rw [hq] at hz'
    dsimp only at hz'
    cases hf : (equations (q.F.nClaim + n) q.tl q.funs q.F).map fun x =>
        (x.2.2, { q with tl := x.1, F := x.2.1 }) with
    | error e => rw [hf] at hz'; exact nomatch hz'
    | ok y =>
      rw [hf] at hz'
      obtain rfl := Except.ok.inj hz'
      show S.lookHeard? ((s.putTl y.2.tl).putFork y.2.F) = s.lookHeard?
      rw [S.look_putFork, S.look_putTl]

theorem three_keep (hS : OnBytes.Model.Head.Shape) (readsArray : Nat) (p : Head.Par)
    (name : String) : KeepsWhatTheLookupHeard
      (VerifiableInference.Desc.Kinds.Head.Shape.bare hS readsArray p 24 4 name) := by
  intro n s z hz
  unfold VerifiableInference.Desc.Kinds.Head.Shape.bare at hz
  cases hk : (kind asClaim (seatAt hS readsArray) 24 4 p).claims.lookup name with
  | none =>
    rw [hk] at hz
    have hz' : (Except.error "no such run" : Except String (List Claim × TS)) = .ok z := hz
    exact nomatch hz'
  | some run =>
    rw [hk] at hz
    have hz' : run n s = .ok (z.1, z.2) := hz
    rw [(three_strong hS readsArray p 24 4 name run hk n s z.2 z.1 hz').2.1]

theorem join_keep (hS : OnBytes.Model.Head.Shape) (readsArray : Nat) (p : Head.Par) :
    KeepsWhatTheLookupHeard
      (joinRun (seatCalls asClaim) (callerKeys p (seatAt hS readsArray))) := by
  intro n s z hz
  obtain ⟨⟨_, G, -, e, -⟩, -⟩ := join_strong hS readsArray p n s z.2 z.1 hz
  rw [e]
  exact S.look_putFork s G

theorem merge_keep : KeepsWhatTheLookupHeard headMergeClaim := by
  intro n s z hz
  have hz' : headMergeClaim n s = .ok (z.1, z.2) := hz
  obtain ⟨a, _, G, ha, -, e, -, -⟩ := VerifiableInference.Desc.First.MergeLaw.claim_inv hz'
  rw [e]
  exact S.look_head s a _ ha rfl rfl

/-- A table out of a list of rows: where each listed row's run leaves the record, so does the run
under every name (the idle row's never returns). -/
theorem tabOf_keeps : ∀ (rows : List ((Nat × String) × Row)),
    (∀ e ∈ rows, KeepsWhatTheLookupHeard e.2.run) →
    ∀ name, KeepsWhatTheLookupHeard (tabOf rows name).run
  | [], _, _ => fun _ _ z hz =>
    nomatch (show (Except.error "no such run" : Except String (List Claim × TS)) = .ok z from hz)
  | (key, row) :: rows, h, name => by
    unfold tabOf
    rw [List.lookup_cons]
    cases name == key with
    | true => exact h (key, row) List.mem_cons_self
    | false => exact tabOf_keeps rows (fun e he => h e (List.mem_cons_of_mem _ he)) name

theorem headRowsKeepWhatTheLookupHeard : HeadRowsKeepWhatTheLookupHeard := by
  intro W readsArray planesLog name n s z hz
  refine tabOf_keeps (rowsHead W readsArray planesLog) (fun e he => ?_) name n s z
    ((guardRun_iff sameReply _ n s z).1 hz).1
  simp only [rowsHead, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact objects_keep false
  · exact guests_keep
  · exact three_keep W.hS readsArray (parOf W.hS (workAtW W)) "norm"
  · exact join_keep W.hS readsArray (parOf W.hS (workAtW W))
  · exact three_keep W.hS readsArray (parOf W.hS (workAtW W)) "policy"
  · exact planes_keep _ _
  · exact objects_keep true
  · exact guests_keep
  · exact equations_keep
  · exact three_keep W.hS readsArray (parOf W.hS (workAtW W)) "logits"
  · exact merge_keep

/-! ## 4 Border 347 -/

set_option maxRecDepth 1000000 in
/-- The item leftOn 24 is among the public items that are open at border 347 of the full chain: in
front of the batching member of the head's link. By evaluation in Lean's kernel. -/
theorem leftOn_open347 :
    Pub.leftOn 24 ∈ pubQ mgMore linksFull (flatPlacesOf linksFull true) 347 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It is open at each of the six borders from behind the output head's own rounds (342) to the
batching's front (347). By evaluation in Lean's kernel. -/
theorem leftOn_openFromTheHeadToTheBatching : ((List.range 6).all fun j =>
    decide (Pub.leftOn 24 ∈ pubQ mgMore linksFull (flatPlacesOf linksFull true) (342 + j))) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: THE TEST CAN SAY NO: the item is not open in front of the output head's own rounds
(341), nor behind the batching (348). By evaluation in Lean's kernel. -/
theorem leftOn_shutOutside :
    decide (Pub.leftOn 24 ∈ pubQ mgMore linksFull (flatPlacesOf linksFull true) 341) = false ∧
      decide (Pub.leftOn 24 ∈ pubQ mgMore linksFull (flatPlacesOf linksFull true) 348) = false := by
  decide +kernel

/-- Wherever a first chain's thread holds at border 347, at letters whose promise is the composed
one over the empty base at the full chain: the sentence of the item leftOn 24. -/
theorem leftOn_of_thread {Bk : ProverCoinCounts} {Cl' W₀ Rc Xi Tr X Xd P Tok : Type} {rows cols nR : ℕ}
    {Wp : OnBytes.Model.Verify.Public}
    (L : Letters Bk Cl' W₀ Rc Xi Tr X P (CellsQ rows cols) Tok MsgT)
    (D : MgData Xd P Tok rows cols nR Wp) (hMg : L.MgP = mgAll D mgBase)
    (hl : L.links = linksFull) (hps : L.ps = flatPlacesOf linksFull true) (hN : L.N = D.N)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hT : Thr L.thread 347 k s m E) : k3LeftOnItemAt Wp 24 s := by
  obtain ⟨-, p⟩ := Small.partsAt_of_thr L hT
  rw [hMg, hl, hps, hN] at p
  exact p.pubP (.leftOn 24) (by
    rw [VerifiableInference.Desc.Sound.mgAll_more_closed D mgBase rfl]
    exact leftOn_open347)

/-- From the sentence of the item leftOn, at numbers that pass the test on the lookup's shape: the
record is laid, and its points are as the head's text asks. -/
theorem pointsOk_of_leftOn (p : Head.Par) {p3 : VerifiableInference.Desc.First.Look.P}
    {h3 : OnBytes.Model.Forest.Shape} {s : S} (L : k3LeftOnItem p3 s) (hs : p3.shape = some h3)
    (hfit : @keysFitB p.sizes p.floor h3 = true) :
    ∃ g, s.lookHeard? = some g ∧ @PointsOk p.sizes p.floor g.zx fun c => g.zk.getD c #[] := by
  obtain ⟨⟨h3', hs', _, _, _, g, _, -, -, K, hg, -⟩, -⟩ := L
  obtain rfl : h3' = h3 := Option.some.inj (hs'.symm.trans hs)
  exact ⟨g, hg, @pointsOk_of_raw p.sizes p.floor h3' g hfit K.zx
    (fun c hc => (K.zkRaw c hc).2) K.zkLen⟩

/-- The second half of the head's test on the points is the four rows' one test on values. -/
theorem endsTest_of_pointsOk (p : Head.Par) (g : OnBytes.Model.Forest.Heard)
    (hP : @PointsOk p.sizes p.floor g.zx fun c => g.zk.getD c #[]) : endsB p g = true := by
  unfold endsB
  refine List.all_eq_true.2 ?_
  rintro ⟨keys, c⟩ hc
  rw [List.mem_zipIdx_iff_getElem?] at hc
  exact beq_iff_eq.2 (hP c keys hc).2

theorem lookupIsHeardAtTheBatching : LookupIsHeardAtTheBatching := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said k s m E hT
  obtain ⟨p3, e3, L⟩ := leftOn_of_thread
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) h.𝔇 rfl rfl rfl rfl hT.1
  obtain ⟨⟨h3, s3, -⟩, -⟩ := id L
  obtain ⟨g, hg, hP⟩ := pointsOk_of_leftOn
    (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) L s3
    (VerifiableInference.Desc.Kinds.Head.Law.InScope.headKeysFit_at_place h.scope h.reads
      h.pubOne p3 h3 e3 s3)
  exact ⟨g, hg, endsTest_of_pointsOk _ g hP⟩

theorem endsTestAcceptsWhereTheLookupIsHeard : EndsTestAcceptsWhereTheLookupIsHeard := by
  intro numbers s a
  obtain ⟨g, hg, hE⟩ := a
  unfold endsS
  rw [hg]
  exact hE

theorem endsTestAcceptsAtTheBatching : EndsTestAcceptsAtTheBatching := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said k s m E hT
  exact endsTestAcceptsWhereTheLookupIsHeard _ s (lookupIsHeardAtTheBatching W₀ Rc Tr X Z D r Zp Np
    cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said k s m E hT)

theorem endsTestAcceptsAtTheBatchingInTheTablesLetters :
    EndsTestAcceptsAtTheBatchingInTheTablesLetters := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said Bs k s m E hB hT
  obtain ⟨Bs', _, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  have a := lookupIsHeardAtTheBatching W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w Said k s m E hT
  rw [← eW] at a
  exact ⟨a, endsTestAcceptsWhereTheLookupIsHeard _ s a⟩

theorem endsTestAcceptsAtEveryStandOfTheBatching : EndsTestAcceptsAtEveryStandOfTheBatching := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said Bs J s hB hStand
  obtain ⟨k, m, E, hT, -⟩ := hStand
  exact (endsTestAcceptsAtTheBatchingInTheTablesLetters W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q
    test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Bs k s m E hB hT).2

theorem headRowsTestsAcceptAlongTheRows : HeadRowsTestsAcceptAlongTheRows := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said Bs k s m E
    place rounds shown drawn readsArray planesLog names start count state hB hT hd hb
  obtain ⟨g, hg, hE⟩ := endsHeard_draw _ place hd
    (endsTestAcceptsAtTheBatchingInTheTablesLetters W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test
      carryX item n₁ n₂ b₀ Vd Rd Kp w Said Bs k s m E hB hT).1
  have a : EndsHeard (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) state :=
    ⟨g, (behindTheRuns_keeps _ (headRowsKeepWhatTheLookupHeard Bs.G₀.W readsArray planesLog) names
      start drawn count state hb).trans hg, hE⟩
  have hS := endsTestAcceptsWhereTheLookupIsHeard _ state a
  refine ⟨a, hS, fun name hn => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> exact hS

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.headTest_of_heard
#print axioms ProofFile.Honest.K6.Term.headTest_of_front
#print axioms ProofFile.Honest.K6.Term.headTestAcceptsAtTheBorder
#print axioms ProofFile.Honest.K6.Term.valuesAtTheOutputHeadAtAnyShape
#print axioms ProofFile.Honest.K6.Term.valuesAtTheOutputHead
#print axioms ProofFile.Honest.K6.Term.eachRowsTestGivesTheBatchingsTest
#print axioms ProofFile.Honest.K6.Term.behindTheRuns_keeps
#print axioms ProofFile.Honest.K6.Term.objects_keep
#print axioms ProofFile.Honest.K6.Term.guests_keep
#print axioms ProofFile.Honest.K6.Term.planes_keep
#print axioms ProofFile.Honest.K6.Term.equations_keep
#print axioms ProofFile.Honest.K6.Term.three_keep
#print axioms ProofFile.Honest.K6.Term.join_keep
#print axioms ProofFile.Honest.K6.Term.merge_keep
#print axioms ProofFile.Honest.K6.Term.tabOf_keeps
#print axioms ProofFile.Honest.K6.Term.headRowsKeepWhatTheLookupHeard
#print axioms ProofFile.Honest.K6.Term.leftOn_open347
#print axioms ProofFile.Honest.K6.Term.leftOn_openFromTheHeadToTheBatching
#print axioms ProofFile.Honest.K6.Term.leftOn_shutOutside
#print axioms ProofFile.Honest.K6.Term.leftOn_of_thread
#print axioms ProofFile.Honest.K6.Term.pointsOk_of_leftOn
#print axioms ProofFile.Honest.K6.Term.endsTest_of_pointsOk
#print axioms ProofFile.Honest.K6.Term.lookupIsHeardAtTheBatching
#print axioms ProofFile.Honest.K6.Term.endsTestAcceptsWhereTheLookupIsHeard
#print axioms ProofFile.Honest.K6.Term.endsTestAcceptsAtTheBatching
#print axioms ProofFile.Honest.K6.Term.endsTestAcceptsAtTheBatchingInTheTablesLetters
#print axioms ProofFile.Honest.K6.Term.endsTestAcceptsAtEveryStandOfTheBatching
#print axioms ProofFile.Honest.K6.Term.headRowsTestsAcceptAlongTheRows
