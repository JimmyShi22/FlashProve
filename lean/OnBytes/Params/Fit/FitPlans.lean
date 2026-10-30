-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitPlans.lean: the routines that make the plans of a key file's and of a proof
file's chains keep the property Small of entries (FitCalc.lean in this folder), under caps on the
setting and on the sizes from which they plan, and if the sub-proofs' routines keep it; so, under
these premises, every entry of the six plans that configure returns is Small.

FitSmall.lean shows it of the routines of OnBytes/Params/Planner.lean, one block each. The six plans
are made by routines above these: OnBytes/Params/DeriveLin.lean (the test on the table),
OnBytes/Params/DeriveReq.lean (the frame of a chain of links), OnBytes/Plan/Ranges.lean and
OnBytes/Plan/KeyOneTime.lean (a key's first chain). This file walks them, in the steps in which
OnBytes/Plan/PlanListsReq.lean, PlanListsKey.lean and OnBytes/Params/PlanListsChains.lean walk them
for the lists of rounds.

Main names:
  SendOk codes sent: of the oracle messages of one prover's message: the cube of each that has a
    sample has at most 2 ^ 32 variables; if the number of their trees follows, it is at most two.
  LinCap codes x, FrameCap z l gs links, ReqCap z, KeyCap z: the caps on the sizes of the
    test on the table, of the frame from group number l on, of a proof's and of a key's chains.
  SubKeeps s sub: the sub-proofs' routines keep Small.
  linSize_ok; keeps_linPlanFirst, keeps_linPlanShared, keeps_linPlanSecond;
    keeps_reqSend, keeps_reqMoments, keeps_reqPlanFrom, keeps_firstRounds;
    keeps_rangesPlan, keeps_oneTimeRounds.
  sharedPlan_small, secondPlan_small, firstPlan_small, oneTimePlan_small: of a plan that is
    returned.
  made_small: of the six plans of a key file and of a proof file that configure returns.
Limits: of a routine that refuses nothing is said. SetCap, SubKeeps and the caps are premises here.
That the caps hold at the sizes which the planner derives from public files: FitCaps.lean and
KeyCaps.lean in this folder; all four premises of made_small wherever Verify.planned returns:
OnBytes/Model/Fit/FitTop.lean and FitPlanned.lean. The plan of an entry's chain (Configured.entry)
is not treated. The program does not import this file.


-/
import OnBytes.Params.Fit.FitSmall
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

open OnBytes.Plan (membersOf sentAtMoment closedGroup KeySized RangesSized rangesPlan
  oneTimeRounds oneTimePlan)

theorem nf_reply : NameOk "REPLY" := ⟨by decide +kernel, by decide⟩

/-! ## Small laws -/

section
variable {s : Setting} {Q : Fmt.Entry → Prop} {m : Nat}

/-- Setting the scope leaves setting, rounds and open roots. -/
theorem keeps_scopeRequest :
    KeepsAt s Q m m (modify fun p => { p with scope := .request } : Planning PUnit) :=
  keeps_modify _ (fun _ => rfl) (fun _ => rfl) fun _ h => h

/-- A routine that is run or left out, and what follows in both cases. -/
theorem keeps_when {β : Type} {P : Prop} [Decidable P] {x : Planning PUnit}
    {k : PUnit → Planning β} {R : β → Prop} {m' : Nat} (h1 : KeepsAt s Q m m x)
    (h2 : KeepsAt s Q m m' (k ()) R) :
    KeepsAt s Q m m' (if P then x >>= k else pure PUnit.unit >>= k) R :=
  keeps_ite (fun _ => keeps_bind h1 fun _ _ => h2)
    fun _ => keeps_bind (R := fun _ => True) (keeps_pure trivial) fun _ _ => h2

end

/-- No or one root of a fresh mask. -/
theorem ahead_le (b : Bool) : (if b = true then 0 else 1) ≤ 2 := by
  split <;> omega

/-- One sample. -/
theorem one_cube {a : SampleSize} (ha : a.cubeBits ≤ 2 ^ 32) :
    ∀ y ∈ [a], y.cubeBits ≤ 2 ^ 32 :=
  cons_cube ha fun _ h => absurd h (by simp)

/-! ## The caps -/

/-- Of the oracle messages of one prover's message. -/
structure SendOk (codes : Codes) (sent : List OracleNotice) : Prop where
  cubes : ∀ n ∈ sent, 0 < n.shape.answers → cubeBitsOf codes n.shape ≤ 2 ^ 32
  trees : ∀ k, treesOf codes sent.toArray = some k → k ≤ 2

/-- Of the sizes of the test on the table. -/
structure LinCap (codes : Codes) (x : LinSized) : Prop where
  table : TableOk x.table
  w : cubeBitsOf codes x.shape.w ≤ 2 ^ 32
  u : cubeBitsOf codes x.shape.fold.u ≤ 2 ^ 32
  omega : cubeBitsOf codes x.shape.omega ≤ 2 ^ 32
  split : cubeBitsOf codes x.shape.sharedSplit ≤ 2 ^ 32
  kLo : x.shape.kLo ≤ 2 ^ 32
  kRow : x.shape.kRow ≤ 2 ^ 32
  treesW : ∀ a k, linMessageW x.shape = some a → treesOf codes a = some k → k ≤ 2
  treesU : ∀ a k, linMessageU x.shape = some a → treesOf codes a = some k → k ≤ 2
  treesOmega : ∀ k, treesOf codes (linMessageOmega x.shape) = some k → k ≤ 2
  own : ∀ t ∈ x.own.stages, StageOk t
  folded : ∀ t ∈ x.folded.stages, StageOk t
  omegaT : ∀ t ∈ x.omega.stages, StageOk t

/-- The oracle messages of the prover's message with which group number l begins. -/
def sentOf (z : ProofSized) (l : Nat) (g : ReqGroup) (msgs : List ReqMessage) :
    List OracleNotice :=
  if l == 0 then membersOf z l g msgs ++ z.request.atStart else membersOf z l g msgs

/-- Of the frame from group number l on: at each group, of the message with which it begins and of
the messages of its link's moments. It goes through groups and links as reqPlanFrom does. -/
def FrameCap (z : ProofSized) : Nat → List ReqGroup → List ReqLink → Prop
  | _, [], _ => True
  | l, g :: gs, links =>
    SendOk z.codes (sentOf z l g ((links.head?.map (·.messages)).getD [])) ∧
      (∀ mo, SendOk z.codes (sentAtMoment ((links.head?.map (·.messages)).getD []) mo)) ∧
      FrameCap z (l + 1) gs (links.drop 1)

/-- Of the sizes of a proof's chains. -/
structure ReqCap (z : ProofSized) : Prop where
  lin : LinCap z.codes z.batch
  link : z.link.group.main.logN ≤ 64
  last : ∀ t ∈ z.last.stages, StageOk t
  frame : FrameCap z 0 (reqGroups z.request).toList z.request.link

/-- Of the sizes of a key's chains. -/
structure KeyCap (z : KeySized) : Prop where
  lin : LinCap z.codes z.once
  input : cubeBitsOf z.codes z.once.input.shape ≤ 2 ^ 32
  message : cubeBitsOf z.codes z.ranges.x.message.shape ≤ 2 ^ 32
  trees : ∀ k, treesOf z.codes (Wf.messageOf z.ranges.x) = some k → k ≤ 2
  test : ∀ t ∈ z.ranges.test.stages, StageOk t

/-- The sub-proofs' routines keep Small. -/
structure SubKeeps (s : Setting) (sub : Subproofs) : Prop where
  plan : ∀ l m, Keeps s Small (sub.plan l m)
  after : Keeps s Small sub.afterLinks

/-! ## The test on the table -/

/-- The sizes that the plans of the test's rounds read are in order. -/
theorem linSize_ok {codes : Codes} {x : LinSized} {ls : LinSize} (h : LinCap codes x)
    (e : linSizeOf codes x = some ls) : LinOk ls := by
  unfold linSizeOf at e
  extract_lets at e
  obtain ⟨a1, h1, e⟩ := opt_bind e
  obtain ⟨k1, g1, e⟩ := opt_bind e
  obtain ⟨a2, h2, e⟩ := opt_bind e
  obtain ⟨k2, g2, e⟩ := opt_bind e
  obtain ⟨k3, g3, e⟩ := opt_bind e
  cases e
  refine ⟨h.w, h.u, h.omega, fun _ hy => absurd hy (by simp), ?_, h.kLo, h.kRow,
    h.treesW a1 k1 h1 g1, h.treesU a2 k2 h2 g2, h.treesOmega k3 g3⟩
  intro y hy
  have hy' : y ∈ (if x.shape.sharedSplitNeeded = true then
      [(⟨cubeBitsOf codes x.shape.sharedSplit, [x.folded.first, x.omega.first]⟩ : SampleSize)]
      else []) := hy
  split at hy'
  · rw [List.mem_singleton.1 hy']
    exact h.split
  · exact absurd hy' (by simp)

section
variable {s : Setting} (S : SetCap s)
include S

theorem keeps_linPlanFirst {codes : Codes} {x : LinSized} (h : LinCap codes x) :
    Keeps s Small (linPlanFirst codes x) := by
  unfold linPlanFirst
  exact keeps_bind (keeps_must _ _) fun ls hl => keeps_linFirst S ls (linSize_ok h hl)

theorem keeps_linPlanShared {codes : Codes} {x : LinSized} (h : LinCap codes x) :
    Keeps s Small (linPlanShared codes x) := by
  unfold linPlanShared
  refine keeps_bind keeps_setting fun _ _ => keeps_bind (keeps_must _ _) fun ls hl => ?_
  refine keeps_bind (keeps_linShared S x.table ls h.table (linSize_ok h hl)) fun _ _ => ?_
  refine keeps_bind (keeps_needs _ _) fun _ _ => keeps_ite (fun _ => ?_) fun _ => ?_
  · exact keeps_bind keeps_split fun _ _ =>
      keeps_bind (keeps_iopp S _ _ _ _ h.folded (ahead_le _)) fun _ _ =>
        keeps_iopp S _ _ 1 _ h.omegaT (by omega)
  · exact keeps_iopp S _ _ _ _ h.folded (ahead_le _)

theorem keeps_linPlanSecond {codes : Codes} {x : LinSized} (h : LinCap codes x) :
    Keeps s Small (linPlanSecond x) := by
  unfold linPlanSecond
  exact keeps_bind keeps_setting fun _ _ => keeps_iopp S _ _ _ _ h.own (ahead_le _)

theorem sharedPlan_small {codes : Codes} {x : LinSized} (h : LinCap codes x) {P : Planned}
    (e : sharedPlan s codes x = .ok P) : ∀ r ∈ P.rounds, Small r.entry :=
  finishHeld_all (keeps_bind (keeps_linPlanShared S h) fun _ _ => keeps_seal) e

theorem secondPlan_small {codes : Codes} {x : LinSized} (h : LinCap codes x) {P : Planned}
    (e : secondPlan s x = .ok P) : ∀ r ∈ P.rounds, Small r.entry :=
  finishHeld_all (keeps_linPlanSecond S h) e

/-! ## The frame of a chain of links -/

theorem keeps_reqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) (own : Bool) (h : SendOk codes sent) :
    Keeps s Small (reqSend codes sent group atStart riders own) := by
  unfold reqSend
  refine keeps_bind (keeps_must _ _) fun n hn => keeps_send S _ n own ?_ (h.trees n hn)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  have hz := (List.mem_filter.1 hy).1
  rw [zipT_eq] at hz
  exact h.cubes y.2 (List.of_mem_zip hz).2 (of_decide_eq_true (List.mem_filter.1 hy).2)

variable {z : ProofSized} {sub : Subproofs} (K : SubKeeps s sub)
include K

theorem keeps_reqMoments (l : Nat) (msgs : List ReqMessage)
    (hm : ∀ mo, SendOk z.codes (sentAtMoment msgs mo)) :
    ∀ fuel moment : Nat, Keeps s Small (reqMoments z sub l msgs fuel moment)
  | 0, _ => keeps_pure trivial
  | fuel + 1, moment => by
    unfold reqMoments
    exact keeps_bind (keeps_reqSend S _ _ _ _ _ _ (hm moment)) fun _ _ =>
      keeps_bind (K.plan l moment) fun _ _ => keeps_bind keeps_scopeRequest fun _ _ =>
        keeps_bind (keeps_reqMoments l msgs hm fuel (moment + 1)) fun _ _ => keeps_pure trivial

/-- What follows the sending and the round of positions in a group. -/
theorem keeps_reqTail (hlast : ∀ t ∈ z.last.stages, StageOk t) (l : Nat) (link : Option ReqLink)
    (msgs : List ReqMessage) (hm : ∀ mo, SendOk z.codes (sentAtMoment msgs mo))
    (fuel o C rows : Nat) (closed : GroupSize) {next : Planning Unit}
    (ih : Keeps s Small next) :
    Keeps s Small
      (match link with
      | none => planIopp z.last.stages (C + rows) 0 z.request.choice.masksRide
      | some _ => do
        sub.plan l 0
        modify fun p => { p with scope := .request }
        let more ← reqMoments z sub l msgs fuel 1
        planBat [closed] (o + C + rows + more)
        planFold closed 0
        next) := by
  cases link with
  | none => exact keeps_iopp S _ _ 0 _ hlast (by omega)
  | some v =>
    exact keeps_bind (K.plan l 0) fun _ _ => keeps_bind keeps_scopeRequest fun _ _ =>
      keeps_bind (keeps_reqMoments S K l msgs hm fuel 1) fun _ _ =>
        keeps_bind (keeps_bat _ _) fun _ _ =>
          keeps_bind (keeps_fold closed 0 (by omega)) fun _ _ => ih

omit S K in
/-- The reply in plain, if the link has one, and what follows. -/
theorem keeps_reqReply (n : Nat) {k : Unit → Planning Unit} (h : Keeps s Small (k ())) :
    Keeps s Small
      (if (n != 0) = true then do
        planScalars n
        let y ← closeNone "REPLY"
        k y
      else do
        let y ← pure PUnit.unit
        k y) :=
  keeps_ite
    (fun _ => keeps_bind (keeps_scalars n) fun _ _ =>
      keeps_bind (keeps_silent nf_reply) fun _ _ => h)
    fun _ => keeps_bind (R := fun _ => True) (keeps_pure trivial) fun _ _ => h

omit K in
/-- The sending of a group's oracle messages and, from the second group on, the round of positions
at which the group before is opened; and what follows. -/
theorem keeps_reqMid (l : Nat) (codes : Codes) (sent : List OracleNotice)
    (sg atStart : GroupSize) (riders : Nat) (before : GroupSize) (hs : SendOk codes sent)
    (hb : before.main.logN ≤ 64) (A B : Nat) {k : Nat → Planning Unit}
    (hk : ∀ C, Keeps s Small (k C)) :
    Keeps s Small
      (do
        reqSend codes sent sg atStart riders (l == 0)
        if 0 < l then do
          let t ← planLoc before
          let y ← pure (A + t * B)
          k y
        else do
          let y ← pure 0
          k y) :=
  keeps_bind (keeps_reqSend S _ _ _ _ _ _ hs) fun _ _ =>
    keeps_ite
      (fun _ => keeps_bind (keeps_loc S before hb) fun _ _ =>
        keeps_bind (R := fun _ => True) (keeps_pure trivial) fun y _ => hk y)
      fun _ => keeps_bind (R := fun _ => True) (keeps_pure trivial) fun y _ => hk y

/-- The frame's rounds from group number l on. -/
theorem keeps_reqPlanFrom (hlast : ∀ t ∈ z.last.stages, StageOk t)
    (hlink : z.link.group.main.logN ≤ 64) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize), FrameCap z l gs links → before.main.logN ≤ 64 →
      Keeps s Small (reqPlanFrom z sub l gs links open_ before)
  | [], _, _, _, _, _, _ => by
    unfold reqPlanFrom
    exact keeps_pure trivial
  | g :: gs, l, links, open_, before, hF, hb => by
    unfold FrameCap at hF
    unfold reqPlanFrom
    refine keeps_reqReply _ ?_
    exact keeps_reqMid S l _ _ _ _ _ before hF.1 hb _ _ fun C =>
      keeps_reqTail S K hlast l _ _ hF.2.1 _ _ C _ _
        (keeps_reqPlanFrom hlast hlink gs (l + 1) (links.drop 1) (open_.drop 1)
          (closedGroup z g gs) hF.2.2 hlink)

/-- The routine of a proof's first chain. -/
theorem keeps_firstRounds (C : ReqCap z) :
    Keeps s Small
      (do
        reqPlan z sub
        sub.afterLinks
        modify fun p => { p with scope := .request }
        if 1 < sub.pendingRows then planBatt sub.pendingRows z.batch.shape.kCol
        linPlanFirst z.codes z.batch
        planSeal) := by
  unfold reqPlan
  exact keeps_bind (keeps_reqPlanFrom S K C.last C.link _ 0 _ _ _ C.frame C.link) fun _ _ =>
    keeps_bind K.after fun _ _ => keeps_bind keeps_scopeRequest fun _ _ =>
      keeps_when (keeps_batt _ _)
        (keeps_bind (keeps_linPlanFirst S C.lin) fun _ _ => keeps_seal)

theorem firstPlan_small (hs : z.set = s) (C : ReqCap z) {P : Planned}
    (e : firstPlan z sub = .ok P) : ∀ r ∈ P.rounds, Small r.entry := by
  subst hs
  exact finishHeld_all (keeps_firstRounds S K C) e

end

/-! ## A key's first chain -/

section
variable {s : Setting} (S : SetCap s)
include S

theorem keeps_rangesPlan (codes : Codes) (z : RangesSized)
    (hm : cubeBitsOf codes z.x.message.shape ≤ 2 ^ 32)
    (ht : ∀ k, treesOf codes (Wf.messageOf z.x) = some k → k ≤ 2)
    (hs : ∀ t ∈ z.test.stages, StageOk t) : Keeps s Small (rangesPlan codes z) := by
  unfold rangesPlan
  refine keeps_bind (keeps_must _ _) fun n hn => ?_
  exact keeps_bind (keeps_send S _ n true (one_cube hm) (ht n hn)) fun _ _ =>
    keeps_bind (keeps_forEach _ fun a _ => keeps_lookup S a) fun _ _ =>
      keeps_bind (keeps_needs _ _) fun _ _ =>
        keeps_bind (keeps_iopp S _ _ _ _ hs (ahead_le _)) fun _ _ =>
          keeps_ite (fun _ => keeps_batt _ _) fun _ => keeps_pure trivial

theorem keeps_oneTimeRounds {z : KeySized} (C : KeyCap z) :
    Keeps s Small (oneTimeRounds z) := by
  unfold oneTimeRounds
  exact keeps_bind (keeps_record _ C.lin.table) fun _ _ =>
    keeps_bind (keeps_send S _ 1 true (one_cube C.input) (by omega)) fun _ _ =>
      keeps_bind (keeps_rangesPlan S _ _ C.message C.trees C.test) fun _ _ =>
        keeps_bind (keeps_linPlanFirst S C.lin) fun _ _ => keeps_seal

theorem oneTimePlan_small {z : KeySized} (hs : z.set = s) (C : KeyCap z) {P : Planned}
    (e : oneTimePlan z = .ok P) : ∀ r ∈ P.rounds, Small r.entry := by
  subst hs
  exact finishHeld_all (keeps_oneTimeRounds S C) e

end

/-! ## The six plans that configure returns -/

/-- Every entry of the six plans that configure returns is Small, if SetCap holds of the setting,
ReqCap and KeyCap of the two records of sizes, and the sub-proofs' routines keep Small (SubKeeps).
The four are premises here; OnBytes/Model/Fit/FitTop.lean and FitPlanned.lean show them wherever
Verify.planned returns. -/
theorem made_small {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x cfg bits = .ok made) (S : SetCap (settingOf l))
    (R : ReqCap made.sized.proof) (C : KeyCap made.sized.key)
    (K : SubKeeps (settingOf l) x.sub) :
    ∀ P ∈ made.key ++ made.proof, ∀ r ∈ P.rounds, Small r.entry := by
  obtain ⟨hz, _, P1, P2, P3, ek, h1, h2, h3, _⟩ := configure_plans h
  obtain ⟨F, S2, S3, ep, f1, f2, f3⟩ := configure_proofPlans h
  have sp : made.sized.proof.set = settingOf l := (configure_proof_sizes h).2.1
  have ss : made.sized.set = settingOf l := (sized_link hz).1
  have sk : made.sized.key.set = settingOf l := (Plan.keySized_oneTime (sized_key hz)).2
  rw [ss] at h2 h3
  rw [sp] at f2 f3
  intro P hP
  rw [ek, ep] at hP
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact oneTimePlan_small S sk C h1
  · exact sharedPlan_small S C.lin h2
  · exact secondPlan_small S C.lin h3
  · exact firstPlan_small S K sp R f1
  · exact sharedPlan_small S R.lin f2
  · exact secondPlan_small S R.lin f3

end OnBytes.Params
