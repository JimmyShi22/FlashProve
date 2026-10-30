-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05LawGuard.lean: KIND K5's LAW IN ONE STATEMENT AT THE SEATED BLOCK k5AtN
(Att/SeatN.lean), WITH NO RECORD OF PUBLIC PREMISES: on the public side it takes "the public record
is what publicOf returns", the block's own test on the plan, the guard's yes (Att/GuardN.lean) and
"the data stand round by round against the kind's declared rounds".

Main names:
  `k5AtN_is`: the block k5AtN is the kind's, with its four runs of claims and one more test on the
    plan.
  `planOk_of_blk`: a yes of that block's planOk is a yes of the kind's own test and of claimsOkAtO.
  `guard_binds`: the lookup's place x := what lookAt returns is bound by the guard's yes; and there
    is A0, what the planner returns at the stored plan a's own settings, input and configuration (by
    publicOf's return: public_plan, Att/GuardPublic.lean), and a is A0 but for the field plFor of
    seam.tl.
  `K05_law_one_guard`: **K05_law_one at k5AtN**: K5Public is gone from the premises.
    `K05_law_one_guard_means`: with what the kind's rounds mean in front. `K05_law_one_guard_ok`: at
    { blk with planOk := ok' }, any ok': for a lot that conjoins one more test to the block's
    planOk.
  `K05_law_one_asks`: what a yes of every named test of k5AsksDescN gives, in one statement.
THE LAW's OBJECT: the constant k5AtN. ITS LETTERS ARE THE SEAT's OWN: Wv, g, before, at the link 2 g
+ 1; a, the stored plan (ha names what k5AtN's own "some" gives); x, the lookup's place (hx;
guard_binds meets it). These two equations bind letters and ask nothing; x and a stand in the types
of α, x0, pl and I. THE LAW STANDS WHOLLY AT a: the shape a.S, the record of the smallness test
a.seam.tl (what the carried record holds), the dry run's letters a's. The planner's return A0 is
opened inside the proof alone: every reading of a unfolds to A0's, but for the plan that K5Behind's
"worth" hands on whole; there the plan's letter is idle (billsWorthJ_withNC,
Att/K05WorthPlFor.lean).
WHAT IS LEFT ON THE PUBLIC SIDE, FOR WHAT THE PROOF SPENDS: hP · h4 (the proof covers attention) ·
hblk · hok · hG · hds. Who pays hP: at a return of Verify.publicOf planIs_public; at a public record
that a description makes by another text (publicOf's with a letter for the second hash function)
planIs_publicO (Att/GuardPublicCut.lean). Who pays h4: at a member of the guard's walk attLinks_mem;
at a public record with PublicCut and a stored plan p4_of_cut (Att/GuardPublicCut.lean). Who pays
hds: at a description's stretch Att/K05DataRounds.lean's k5_public_at_data has the three facts that
it gives, under that theorem's own premise on the declared rounds. D AND rad ARE FREE: TIED TO Wv BY
NOTHING. The guard gives K5Public at every D and rad, for AttOK's five tests read neither. But the
relation in front (attBase, attLin) and the pin's signature (attSg x D rad) are made of them. AT THE
FILE's OWN D AND rad ALONE THE RELATION IS THE MEANT ONE: at another (the empty one) the law is true
and speaks of zeros: a symbol, a mask entry or a cell without a seat is read as 0 in silence. What
guards that reading (AttReadsOK, Look/K3CallerAtt.lean: sampled, keptSame, seated, cellsIn) IS ASKED
BY NOBODY, and no law of K5's files takes it as a premise but for cellsIn's like in K05_means_ord.
So the public side is closed for what the proof spends, not for what the statement means. What a
binder would need: D's codes, shape and layout are fields of the planner's record of the first chain
(Params.First), a function of the three public files, not of Wv alone; makers of D.arrayOf and of
rad are not met. THE NUMBER 128 stands twice: in Err.cap 128 here and in the guard's heldN 128.
WHAT IS LEFT BESIDES: K5AtOn (three fields, at each statement in front with "on") and K5Behind (two
fields, where LaidBehind holds): shown of nothing here. BOTH ARE OWED AT THE STORED RECORD's tl
(a.seam.tl), which stands in their types: whoever pays them at the planner's record owes the move.
hok is on blk's own planOk: from an entry's planOk it follows where the entry's is blk.planOk &&
‹more›. THE PIECE BEARS blk BARE. Between blk and a description's own entry lie wrappers that refuse
more (a guard on marks, a guard on the reply, a name, the driver's stamp of the place): the step
"the law at blk gives the law at the entry" is not made here. EMPTY AT: on := False · R' := False.
NOT SHOWN: that a description's block at link 2 g + 1 is k5AtN Wv (2 g + 1) g before at these
letters. What stands beside the law and is no field: see Att/K05LawOne.lean.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.GuardNLaw
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.First.Att.K05DataRounds
import Johnson.Desc.First.Att.K05WorthPlFor

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (dimOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc (Claim RoundAsG)

/-- **The block k5AtN is the kind's, with its four runs and one more test on the plan.** -/
theorem k5AtN_is (Wv : Verify.Public) (l g : ℕ) (before : List (ℕ × ℕ))
    (b : VerifiableInference.Desc.Block First.S Claim) (h : k5AtN Wv l g before = some b) :
    ∃ a, Wv.A[g]? = some a ∧
      b = { attentionKind seatSO (runsN a) (parO Wv l a before) with
        planOk := (attentionKind seatSO (runsN a) (parO Wv l a before)).planOk && claimsOkAtO a } := by
  unfold k5AtN at h
  cases hg : Wv.A[g]? with
  | none => rw [hg] at h; cases h
  | some a =>
    rw [hg] at h
    exact ⟨a, rfl, (Option.some.inj h).symm⟩

/-- A yes of the block's own test on the plan. -/
theorem planOk_of_blk {Wv : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)}
    {b : VerifiableInference.Desc.Block First.S Claim} (h : k5AtN Wv l g before = some b)
    (hok : b.planOk = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a) :
    planOk (parO Wv l a before) = true ∧ claimsOkAtO a = true := by
  obtain ⟨a', ha', rfl⟩ := k5AtN_is Wv l g before b h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  exact Bool.and_eq_true_iff.1 hok

/-- **The two letters are bound**: the place by the guard's yes; the planner's return by publicOf's.
-/
theorem guard_binds {Wv : Verify.Public} (hP : PlanIs Wv) {l g : ℕ} {a : Attention.Plan}
    (ha : Wv.A[g]? = some a) (hG : k5GuardN Wv l g = true) :
    ∃ x A0, lookAt Wv l false = some x ∧
      Attention.plan a.settings a.inp a.S.cf = Except.ok A0 ∧
      ∃ pf, a = { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } } := by
  obtain ⟨A0, pf, hA, e⟩ := hP g a ha
  unfold k5GuardN k5ListN at hG
  rw [ha] at hG
  cases hx : lookAt Wv l false with
  | none => rw [hx] at hG; cases hG
  | some x => exact ⟨x, A0, rfl, hA, pf, e⟩

open Classical in
/-- **KIND K5's LAW AT THE SEATED BLOCK, FROM THE BLOCK's OWN TEST AND THE GUARD**, at the stored
plan's own
letters. -/
theorem K05_law_one_guard {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (g : ℕ) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true)
    (hG : k5GuardN Wv (2 * g + 1) g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv (2 * g + 1) false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv (2 * g + 1) a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns a.seam.tl) (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (Rd : Rides Fr base)
    (R' : First.S × Fr.E.Str → W → Prop)
    (On : K5AtOn x a.seam.tl D rad claim (parO Wv (2 * g + 1) a before) ns base x0 gOf pl on I Rd)
    (Bh : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv (2 * g + 1) a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj gOf on I R') :
    (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).GoodIn
      on (fun b => LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b ∧ Rd.q (Rd.rq b.1) b.2)
      (fun a' w => ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') (I.part w)) R' := by
  obtain ⟨hb, hc⟩ := planOk_of_blk hblk hok ha
  obtain ⟨x', A0, hx', ⟨pf, e⟩, Pb⟩ :=
    guard_gives hP h4 g before D rad ha hG hb hc ds (public_of_as _ hds)
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  obtain ⟨a', ha', rfl⟩ := k5AtN_is Wv (2 * g + 1) g before blk hblk
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst e
  exact K05_law_one (A := A0) x _ D rad Ex Wp α claim _ (runsN _) (parO Wv (2 * g + 1) _ before) ns base 128 ds _ _ tj x0
    yOf gOf pl on I Rd R' Pb On
    ⟨(billsWorthJ_withNC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A0 _ _ (by rfl)).1 Bh.worth, Bh.item⟩

open Classical in
/-- **The same with what the kind's rounds mean in front.** -/
theorem K05_law_one_guard_means {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (g : ℕ) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true)
    (hG : k5GuardN Wv (2 * g + 1) g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv (2 * g + 1) false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv (2 * g + 1) a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns a.seam.tl) (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (Rd : Rides Fr base)
    (R' : First.S × Fr.E.Str → W → Prop)
    (On : K5AtOn x a.seam.tl D rad claim (parO Wv (2 * g + 1) a before) ns base x0 gOf pl on I Rd)
    (Bh : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv (2 * g + 1) a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj gOf on I R') :
    (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).GoodIn
      on (fun b => LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b ∧ Rd.q (Rd.rq b.1) b.2)
      (fun a' w => OwnMeans x a.S a.seam.tl D rad (x0 a').2.1.pt (I.part w)) R' := by
  obtain ⟨hb, hc⟩ := planOk_of_blk hblk hok ha
  obtain ⟨x', A0, hx', ⟨pf, e⟩, Pb⟩ :=
    guard_gives hP h4 g before D rad ha hG hb hc ds (public_of_as _ hds)
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  obtain ⟨a', ha', rfl⟩ := k5AtN_is Wv (2 * g + 1) g before blk hblk
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst e
  exact K05_law_one_means (A := A0) x _ D rad Ex Wp α claim _ (runsN _) (parO Wv (2 * g + 1) _ before) ns base 128 ds _ _ tj x0
    yOf gOf pl on I Rd R' Pb On
    ⟨(billsWorthJ_withNC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A0 _ _ (by rfl)).1 Bh.worth, Bh.item⟩

open Classical in
/-- **The same at the block with another test on the plan in planOk's place**: for a lot that lays
{ blk with planOk := blk.planOk && ‹one more test› }. The premise hok is still on blk's own. -/
theorem K05_law_one_guard_ok {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (g : ℕ) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true) (ok' : Bool)
    (hG : k5GuardN Wv (2 * g + 1) g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv (2 * g + 1) false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv (2 * g + 1) a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns a.seam.tl) (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (Rd : Rides Fr base)
    (R' : First.S × Fr.E.Str → W → Prop)
    (On : K5AtOn x a.seam.tl D rad claim (parO Wv (2 * g + 1) a before) ns base x0 gOf pl on I Rd)
    (Bh : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv (2 * g + 1) a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj gOf on I R') :
    (⟨{ blk with planOk := ok' }, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).GoodIn
      on (fun b => LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b ∧ Rd.q (Rd.rq b.1) b.2)
      (fun a' w => ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') (I.part w)) R' := by
  obtain ⟨hb, hc⟩ := planOk_of_blk hblk hok ha
  obtain ⟨x', A0, hx', ⟨pf, e⟩, Pb⟩ :=
    guard_gives hP h4 g before D rad ha hG hb hc ds (public_of_as _ hds)
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  obtain ⟨a', ha', rfl⟩ := k5AtN_is Wv (2 * g + 1) g before blk hblk
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst e
  exact K05_law_one (A := A0) x _ D rad Ex Wp α claim ok' (runsN _) (parO Wv (2 * g + 1) _ before) ns base 128 ds _ _ tj x0
    yOf gOf pl on I Rd R' Pb On
    ⟨(billsWorthJ_withNC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A0 _ _ (by rfl)).1 Bh.worth, Bh.item⟩

/-- **What a yes of every named test of k5AsksDescN gives**, in one statement. -/
theorem K05_law_one_asks {Xi : Type} (pol lay KL : ByteArray)
    (F : VerifiableInference.Desc.FileDescription Xi) (h : ∀ t ∈ k5AsksDescN pol lay KL F, t.2 = true) :
    ∃ Wv, Model.Verify.publicOf pol KL (some lay) = .ok Wv ∧
      (∀ y ∈ attLinksN Wv, k5GuardN Wv y.1 y.2 = true) ∧
      (∀ b ∈ F.first.blocksInOrder, b.place.kind = .K5 →
        ∃ y ∈ attLinksN Wv, b.place = ⟨1, some y.1, 3, .K5⟩) ∧
      (∀ y ∈ attLinksN Wv, ∃ b ∈ F.first.blocksInOrder, b.place = ⟨1, some y.1, 3, .K5⟩) ∧
      (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ .K5) ∧ ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ .K5 := by
  obtain ⟨Wv, hW, hg, hw⟩ := asksDesc_give pol lay KL F h
  exact ⟨Wv, hW, hg, walk_gives Wv F hw⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5AtN_is
#print axioms VerifiableInference.Desc.First.Att.P.planOk_of_blk
#print axioms VerifiableInference.Desc.First.Att.P.guard_binds
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_guard
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_guard_means
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_guard_ok
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_asks
