-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MsgsSeat.lean: EVERY
MAKER OF onlineDescription's SEAT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, AND THE SEAL: under an
invariant A of the verifier's state that every maker keeps: a yes of its block's decision adds to
THE NUMBER OF ORACLE MESSAGES THAT THE STATE HAS RECEIVED (s.st.oracles.size) just what the block
tells (toldMsgs, Johnson/Goal/Meaning/CarryTold.lean); every run leaves the number. UNDER THREE
NAMED PREMISES.

For the third conjunct of bookAt (Johnson/Desc/First/Borders.lean), a fixed clause of the
promise at every border.
  seatCarry_msgs: **H : Meaning.K2.SeatKeeps (InvR A) okB okP · K1Told · K2Adds A ok2 ⇒ SeatCarry
      (StepOn A msgsOf) (KeptOn A msgsOf) (oksOf okB okP ok2)**: all nineteen fields.
  seatCarry_or: **K1Told ⇒ SeatCarry (fun b => Marked drawsPos b ∨ StepAll msgsOf b) … oksOr**: THE
      CODE SWITCHES SET APART BY THE MARK drawsPos, "a declared round that draws positions"
      (k2_or: a switch's block bears the
      mark, or fails its test on the plan): NO INVARIANT, NO
      PREMISE ON K2: every other maker's block adds what it tells. (seatKeeps_top, whole_top,
      fn_top, wp_inr, carriedAll_or.)
THE THREE PREMISES, AND WHO CAN PAY.
  H: every maker keeps A: the structure SeatKeeps (Johnson/IMR/SeatKeeps.lean) at the relation InvR
      A s t := A s → A t. A IS A LETTER: whoever pays K2Adds chooses it.
  K1Told: ∀ P, K1.planOkOwn P = true → the tenants that K1.oracles P tells number P.sent.size. PAID
      IN OTHER FILES, TO THE LETTER: K1.told_tenants_own (Johnson/Desc/K1/Law/ToldCounts.lean).
      NOT JOINED HERE: this file does not import that one.
      Joined in Johnson/IMR/ToldPaid.lean: k1Told_paid.
  K2Adds A ok2: at the seat's own numbers, under A, a yes of the code switch adds as many messages
      as its block tells. OWED. k2Adds_of_count brings it down, by yes_size, to the letters of K2's
      files: ok2 p · the test on the plan · A s · A YES of decideWith sendByL8 p at s · FrontOf p
      s x ⇒ (switchNotices x.T x.others).size = toldMsgs (codeSwitchKind p) (the first clause of K2.Fence,
      Johnson/Top/H0/Tw/K2C/SendsOn.lean, as a count). WHAT LIES FOR IT (by texts of this project
          that are not in this repository):
      notices_sent (the planner's list is switchNotices at a frame of the plan's shape and groups) ·
      told_tenants (oraclesAt's tenants number sent.size) · the switch's own guard [G35] (the opened
      group's number is p.grp; the lot lays grp := l). WHAT LACKS: an invariant that ties the number
      of groups to the walk's frame's link.
HOW THE OTHER FIELDS ARE PAID. "THE NUMBER STAYS": calls of framesOf_three,
closeOf_three, batch_three, whole_three (Johnson/Goal/Meaning/SizeSeated.lean) at RcM, over its
Whole Quiet lemmas; K2's four quiet steps: headFrontQ_size, headOpenQ_size, finishFrontQ_size,
finishBehindQ_size (Johnson/Top/H0/Tw/K2C/StillKeeps.lean). "TELLS NOTHING", TYPED HERE: k7_told,
k8_told, batch_told: rfl · k3Own_told, k3_told, k4_told, k5_told, k6_told, k11_told, closeOf_told,
reads_told: by the field's text (a list of empty lists). K1's TWO: commitAtS_msgs, firstAtS_msgs:
commitAtS_seated, firstAtS_seated (field msgs) with K1Told. THE SEAL hands the
state back.
OBJECT: the laid makers. USER: Johnson/IMR/MsgsCut.lean. LETTERS: A, okB, okP, ok2: free.



Compiled with the whole library.
Limits. Nothing behind the last link. No member. Book-keeping. Nothing on soundness.
-/
import Johnson.IMR.RootsSeat
import Johnson.IMR.SizeSeat
import Johnson.Goal.Meaning.CarryTold
import Johnson.Goal.Meaning.SizeSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core ByC)
open VerifiableInference.Desc.K1.RelCore (coreS)
open ProofFile (Lot Ground Pub)

/-- The number of oracle messages that the verifier's state has received. -/
abbrev msgsOf (s : S) : Nat := s.st.oracles.size

/-- An invariant of the state, as a relation. -/
def InvR (A : S → Prop) : S → S → Prop := fun s t => A s → A t

abbrev PrM (A : S → Prop) {Cl : Type} (b : Block S Cl) : Prop := StepOn A msgsOf b
abbrev RM (A : S → Prop) : S → S → Prop := KeptOn A msgsOf

/-- The number of messages stays, on the three that the plain ground writes. -/
def RcM : Core → Core → Prop := fun a b => b.st.oracles.size = a.st.oracles.size

theorem rcM_three : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
    b.roots = a.roots → RcM a b := fun _ _ h _ _ => h

variable {A : S → Prop}

theorem whole_kept {Cl : Type} {b : Block S Cl} (W₁ : Whole (ByC RcM coreS) b)
    (W₂ : Whole (InvR A) b) : Whole (RM A) b :=
  ⟨fun s rs gs s' h => ⟨W₁.1 s rs gs s' h, W₂.1 s rs gs s' h⟩,
    fun c hc n s y h => ⟨W₁.2.1 c hc n s y h, W₂.2.1 c hc n s y h⟩,
    fun c hc s s' h => ⟨W₁.2.2 c hc s s' h, W₂.2.2 c hc s s' h⟩⟩

theorem fn_kept {f : S → Except String S} (h₁ : Fn (ByC RcM coreS) f) (h₂ : Fn (InvR A) f) :
    Fn (RM A) f := fun s s' h => ⟨h₁ s s' h, h₂ s s' h⟩

theorem told_zero {T Cl : Type} {b : Block T Cl} (h : ∀ l ∈ b.oracles, l = []) :
    toldMsgs b = 0 := by
  have e : b.oracles.flatten = [] := List.flatten_eq_nil_iff.2 h
  unfold toldMsgs
  rw [e]
  rfl

/-- A maker that tells nothing. -/
theorem wp_silent {Cl : Type} {b : Block S Cl} (h0 : toldMsgs b = 0) (W : Whole (RM A) b) :
    WP (fun {_} b => PrM A b) (RM A) b :=
  ⟨⟨fun _ s s' rs gs _ h => by rw [h0, Nat.add_zero]; exact (W.1 s rs gs s' h).1,
    fun s s' rs gs ha h => (W.1 s rs gs s' h).2 ha⟩, W.2.1, W.2.2⟩

theorem carriedAll_told : CarriedAll (fun {_} b => PrM A b) (RM A) where
  each _ := carried_told A msgsOf
  retype {_ _ b} W :=
    ⟨fun hp s s' rs gs ha h =>
      W.1 ((Bool.and_eq_true _ _ ▸ (show (b.planOk && b.claims.isEmpty) = true from hp)).1) s s' rs
        gs ha h, W.2⟩

/-! ## The plan's side: who tells nothing -/

theorem map_nil_mem {α β : Type} {l : List α} {x : List β} (h : x ∈ l.map fun _ => ([] : List β)) :
    x = [] := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 h
  rfl

theorem k8_told (p : K8.ParW) : toldMsgs (K8.whole p) = 0 := rfl

theorem k7_told (W : Verify.Public) (l : Nat) : toldMsgs (Kinds.Reply.blockOf W l) = 0 := rfl

theorem batch_told (p : K9.Where) (claims : S → Except String (List Claim × S)) :
    toldMsgs (K9.batch K9.atS p claims) = 0 := rfl

theorem k4_told (p : OnBytes.Desc.First.K4.Par) :
    toldMsgs (OnBytes.Desc.First.K4.blockAtC p) = 0 := told_zero fun _ h => map_nil_mem h

theorem k11_told (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    toldMsgs (Johnson.Desc.First.ForkMerge.headClaimMergeKind P) = 0 :=
  told_zero fun _ h => (List.mem_replicate.1 h).2

theorem closeOf_told (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Unit) p P, toldMsgs b = 0 := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · rfl
  · exact told_zero fun _ h => map_nil_mem h
  · rfl

theorem reads_told {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit}
    (h : ProofFile.readsQuietAt G l X piece = some b) : toldMsgs b = 0 := by
  have hA : ∀ {W : Verify.Public} {l g : Nat} {b : Block S Unit}, Att.readsAtO W l g = some b →
      toldMsgs b = 0 := by
    intro W l g b h
    unfold Att.readsAtO at h
    obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  have hB : ∀ {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL} {Hp : Head.HPlanH2}
      {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit},
      K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b → toldMsgs b = 0 := by
    intro G hS HLy Hp kinds l b h
    unfold K8.ReadsQuiet.blockAt at h
    obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl
    · split at h
      · cases h
        rfl
      · cases h
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact hA h
    | exact hB h
    | cases h

theorem k3Own_told {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : toldMsgs b = 0 := by
  unfold K3.theOwn at h
  split at h
  · cases h
  obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨digits, -, h⟩ := List.exists_of_findSome?_eq_some h
  split at h
  · cases h
  obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sent, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨laid, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨key, -, h⟩ := Option.map_eq_some_iff.1 h
  dsimp only at h
  split at h
  · subst h
    exact told_zero fun _ k => map_nil_mem k
  · subst h
    exact told_zero fun _ k => map_nil_mem k

theorem k3_told (claim : Aff → ProofFile.Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S ProofFile.Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : toldMsgs b = 0 := by
  unfold K3.theStated at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have e : toldMsgs b = toldMsgs w := by
    split at h
    · cases h
      rfl
    · split at h
      · cases h
        rfl
      · split at h
        · cases h
          rfl
        · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
          rfl
  rw [e]
  unfold K3.theWhole at hw
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hw
  have k := k3Own_told claim true X codes shape a ho
  split
  · rw [toldMsgs_andThen, k]
    rfl
  · exact k

theorem k5_told (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) {b : Block S Claim}
    (h : Att.P.k5AtN W l g before = some b) : toldMsgs b = 0 := by
  unfold Att.P.k5AtN at h
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact told_zero fun _ k => map_nil_mem k

theorem k6_told {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)} {b : Block S Claim}
    (h : Kinds.Head.seatedClaims W l before = some b) : toldMsgs b = 0 := by
  obtain ⟨b0, h0, rfl⟩ := Kinds.Head.Law.seatedClaims_some h
  unfold Kinds.Head.blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  exact told_zero fun _ k => map_nil_mem k

/-! ## The senders: what is owed, by name -/

/-- **OWED (the plan's side at K1)**: the tenants that a sending's block tells are as many as the
messages that it sends. -/
def K1Told : Prop := ∀ P : K1.Par, K1.planOkOwn P = true →
  ((K1.oracles P).flatten.map fun o => o.tenants.length).sum = P.sent.size

/-- **OWED (at K2)**: under the invariant, at the seat's own numbers: a yes of the code switch adds
as many messages as its block tells. (The switch's decision does not read what its block tells.) -/
def K2Adds (A : S → Prop) (ok2 : K2.P2 → Prop) : Prop :=
  ∀ p : K2.P2, ok2 p → (K2.codeSwitchKind p : Block S Unit).planOk = true →
    ∀ (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), A s →
      (K2.codeSwitchKind p : Block S Unit).decide s rs gs = .ok s' →
      msgsOf s' = msgsOf s + toldMsgs (K2.codeSwitchKind p : Block S Unit)

/-- **What K2Adds comes down to, in the letters of K2's files** (FrontOf; the first clause of
K2.Fence, as a count: Johnson/Top/H0/Tw/K2C/SendsOn.lean): under the invariant, at the seat's own
numbers, AT A YES: the front that the switch takes off the state announces as many messages as the
block tells. By yes_size. -/
theorem k2Adds_of_count {ok2 : K2.P2 → Prop}
    (hF : ∀ p : K2.P2, ok2 p → (K2.codeSwitchKind p : Block S Unit).planOk = true →
      ∀ (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), A s →
        K2.decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s' → ∀ x, K2.FrontOf p s x →
        (_root_.Tw.K2.switchNotices x.T x.others).size = toldMsgs (K2.codeSwitchKind p : Block S Unit)) :
    K2Adds A ok2 := by
  intro p hp hpl s s' rs gs ha h
  obtain ⟨x, hx, e1, -, e2, -⟩ := K2.yes_size h
  show s'.st.oracles.size = s.st.oracles.size + _
  rw [e2, e1, hF p hp hpl s s' rs gs ha h x hx]

theorem commitAtS_msgs (h1 : K1Told) (P : K1.Par) (link moment : Nat)
    (arrays : Option (List Nat))
    (hp : (K1.commitAtS (Cl := Unit) P link moment arrays).planOk = true) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS (Cl := Unit) P link moment arrays).decide s rs gs = .ok s') :
    msgsOf s' = msgsOf s + toldMsgs (K1.commitAtS (Cl := Unit) P link moment arrays) := by
  have h2 : ∃ a b, rs = [a, b] := by
    have h' := h
    unfold K1.commitAtS at h'
    dsimp only at h'
    split at h'
    · obtain ⟨y, hy, -⟩ := (K1.map_ok _ _ _).1 h'
      obtain ⟨ids, d₁, f', k, -⟩ := K1.commitOwn_ok P link moment arrays _ y _ gs hy
      exact send_two k
    · cases h'
  obtain ⟨a, b, rfl⟩ := h2
  have hp' : (K1.planOkOwn P && arrays.isSome) = true := hp
  rw [Bool.and_eq_true] at hp'
  have e : toldMsgs (K1.commitAtS (Cl := Unit) P link moment arrays) = P.sent.size := h1 P hp'.1
  rw [e]
  exact (K1.commitAtS_seated P link moment arrays s s' a b gs h).msgs

theorem firstAtS_msgs (h1 : K1Told) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (hp : (K1.firstSegmentOpening (Cl := Unit) q gp).planOk = true) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Unit) q gp).decide s rs gs = .ok s') :
    msgsOf s' = msgsOf s + toldMsgs (K1.firstSegmentOpening (Cl := Unit) q gp) := by
  have h2 : ∃ a b, rs = [a, b] := by
    obtain ⟨c, d', k, -, -⟩ := K1.firstAtS_ok q gp s s' rs gs h
    obtain ⟨g, d₁, ids, d₂, -, h4, -⟩ := K1.firstOwn_ok _ _ _ _ _ _ _ k
    exact send_two h4
  obtain ⟨a, b, rfl⟩ := h2
  have hp' : (K1.planOkOwn (K1.firstPar q gp) && K1.firstPlanOk q gp.samples) = true := hp
  rw [Bool.and_eq_true] at hp'
  have e : toldMsgs (K1.firstSegmentOpening (Cl := Unit) q gp) = (K1.firstPar q gp).sent.size :=
    h1 _ hp'.1
  rw [e]
  exact (K1.firstAtS_seated q gp s s' a b gs h).msgs

/-! ## The seat's makers, all -/

/-- A sender that states no run. -/
theorem wp_sender {Cl : Type} {b : Block S Cl}
    (hc : b.planOk = true → ∀ (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      A s → b.decide s rs gs = .ok s' → msgsOf s' = msgsOf s + toldMsgs b)
    (W : Whole (InvR A) b) (h1 : b.claims = []) (h2 : b.after = []) :
    WP (fun {_} b => PrM A b) (RM A) b :=
  ⟨⟨hc, fun s s' rs gs ha h => W.1 s rs gs s' h ha⟩, (fun c k => by rw [h1] at k; cases k),
    (fun c k => by rw [h2] at k; cases k)⟩

/-- At which numbers the fields are asked. -/
def oksOf (okB : Array Stages.LinkH → Prop) (okP : K2.HeadPar → Prop) (ok2 : K2.P2 → Prop) : Oks :=
  { B := okB, g := fun gp => gp.firstTree = 0, P := okP, p2 := fun p => p.firstTree = 0 ∧ ok2 p }

/-- **EVERY MAKER OF THE SEAT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, AND THE SEAL**: under an
invariant A that every maker keeps: a yes adds to the number of oracle messages just what the block
tells; every run leaves the number. UNDER THE TWO THAT ARE OWED. -/
theorem seatCarry_msgs {okB : Array Stages.LinkH → Prop} {okP : K2.HeadPar → Prop}
    {ok2 : K2.P2 → Prop} (H : Meaning.K2.SeatKeeps (InvR A) okB okP) (h1 : K1Told)
    (h2 : K2Adds A ok2) : SeatCarry (fun {_} b => PrM A b) (RM A) (oksOf okB okP ok2) where
  frames := fun hB h f hf =>
    have a := Meaning.K2.framesOf_three rcM_three h f hf
    have b := H.frames hB h f hf
    ⟨fn_kept a.1 b.1, fn_kept a.2.1 b.2.1, fn_kept a.2.2 b.2.2⟩
  k1First := fun q gp h0 =>
    wp_sender (fun hp _ _ _ _ _ h => firstAtS_msgs h1 q gp hp h) (H.k1First q gp h0) rfl rfl
  k1Later := fun q gp l p m a h0 =>
    wp_sender (fun hp _ _ _ _ _ h => commitAtS_msgs h1 _ l m a hp h) (H.k1Later q gp l p m a h0)
      rfl rfl
  reads := fun h => wp_silent (reads_told h)
    (whole_kept (Meaning.K2.whole_three rcM_three (Meaning.K2.readsQuietAt_quiet h)) (H.reads h))
  k3 := fun c r X cs sh a _ h => wp_silent (k3_told c r X cs sh a h)
    (whole_kept (Meaning.K2.whole_three rcM_three (Meaning.K2.theStated_quiet c r X cs sh a h))
      (H.k3 c r X cs sh a h))
  k4 := fun p => wp_silent (k4_told p)
    (whole_kept (Meaning.K2.whole_three rcM_three (Meaning.K2.blockAtC_quiet p)) (H.k4 p))
  k5 := fun W l g bf _ h => wp_silent (k5_told W l g bf h)
    (whole_kept (Meaning.K2.whole_three rcM_three (Meaning.K2.k5AtN_quiet W l g bf h))
      (H.k5 W l g bf h))
  k6 := fun h => wp_silent (k6_told h)
    (whole_kept (Meaning.K2.whole_three rcM_three (Meaning.K2.seatedClaims_quiet h)) (H.k6 h))
  k7 := fun W l => wp_silent (k7_told W l)
    (whole_kept (Meaning.K2.whole_three rcM_three (Meaning.K2.k7Of_quiet W l)) (H.k7 W l))
  k8 := fun p => wp_silent (k8_told p)
    (whole_kept (Meaning.K2.whole_three rcM_three (Meaning.K2.k8Whole_quiet p)) (H.k8 p))
  k11 := fun Q => wp_silent (k11_told Q)
    (whole_kept (Meaning.K2.whole_three rcM_three (Meaning.K2.headMerge11_quiet Q)) (H.k11 Q))
  closeOf := fun p P b hb => wp_silent (closeOf_told p P b hb)
    (whole_kept (Meaning.K2.closeOf_three rcM_three p P b hb) (H.closeOf p P b hb))
  batch := fun p claims hcl => wp_silent (batch_told p claims)
    (whole_kept
      (Meaning.K2.batch_three rcM_three (fun h k => Eq.trans k h) p fun s y h => (hcl s y h).1)
      (H.batch p fun s y h => (hcl s y h).2))
  k2 := fun p hp => wp_sender (h2 p hp.2) (H.k2 p hp.1) rfl rfl
  front := fun tl => fn_kept (fun _ _ h => K2.headFrontQ_size h) (H.front tl)
  openQ := fun P hP => fn_kept (fun _ _ h => K2.headOpenQ_size h) (H.openQ P hP)
  finFront := fn_kept (fun _ _ h => K2.finishFrontQ_size h) H.finFront
  finBehind := fn_kept (fun _ _ h => K2.finishBehindQ_size h) H.finBehind
  theSeal := fun inFront => by
    have key : ∀ (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        (ChainEnd.chainEnd 1 5 true inFront endAsks : Block S Unit).decide s rs gs = .ok s' →
        s' = s := by
      intro s s' rs gs h
      obtain ⟨_, -, rfl⟩ := Keeps.emap_ok h
      rfl
    exact ⟨fun _ s s' rs gs _ h => by rw [key s s' rs gs h]; rfl,
      fun s s' rs gs ha h => by rw [key s s' rs gs h]; exact ha⟩

/-! ## The code switches set apart -/

/-- The mark: a declared round that draws positions: a code switch's second round ("LOC"). -/
def drawsPos (r : Fmt.DeclaredRound) : Prop := r.entry.poss ≠ 0

/-- The block declares a round that draws positions, or a yes adds to the number of oracle messages
what the block tells. -/
abbrev PrO {Cl : Type} (b : Block S Cl) : Prop := Marked drawsPos b ∨ StepAll msgsOf b

abbrev RO : S → S → Prop := KeptOn (fun _ => True) msgsOf

theorem whole_top {Cl : Type} (b : Block S Cl) : Whole (InvR fun _ => True) b :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩

theorem fn_top (f : S → Except String S) : Fn (InvR fun _ => True) f := fun _ _ _ _ => trivial

theorem seatKeeps_top : Meaning.K2.SeatKeeps (InvR fun _ => True) where
  refl := fun _ => id
  trans := fun _ _ _ _ _ _ => trivial
  frames := fun _ _ _ _ => ⟨fn_top _, fn_top _, fn_top _⟩
  k1First := fun _ _ _ => whole_top _
  k1Later := fun _ _ _ _ _ _ _ => whole_top _
  reads := fun _ => whole_top _
  k3 := fun _ _ _ _ _ _ _ _ => whole_top _
  k4 := fun _ => whole_top _
  k5 := fun _ _ _ _ _ _ => whole_top _
  k6 := fun _ => whole_top _
  k7 := fun _ _ => whole_top _
  k8 := fun _ => whole_top _
  k11 := fun _ => whole_top _
  closeOf := fun _ _ _ _ => whole_top _
  batch := fun _ _ _ => whole_top _
  k2 := fun _ _ => whole_top _
  front := fun _ => fn_top _
  openQ := fun _ _ => fn_top _
  finFront := fn_top _
  finBehind := fn_top _

theorem wp_inr {Cl : Type} {b : Block S Cl}
    (W : WP (fun {_} b => PrM (fun _ => True) b) RO b) : WP (fun {_} b => PrO b) RO b :=
  ⟨Or.inr W.1, W.2⟩

theorem carriedAll_or : CarriedAll (fun {_} b => PrO b) RO where
  each _ := carried_or drawsPos msgsOf
  retype W := W.elim (fun ⟨r, hr, h⟩ => Or.inl ⟨r, hr, h⟩)
    fun W => Or.inr (carriedAll_told.retype W)

/-- A code switch's block bears the mark; where its plan draws no position its test on the plan says
no, and nothing is asked. -/
theorem k2_or (p : K2.P2) : PrO (K2.codeSwitchKind p : Block S Unit) := by
  by_cases h0 : p.positions = 0
  · refine Or.inr ⟨fun hp => ?_, fun _ _ _ _ _ _ => trivial⟩
    exfalso
    have hp' : (Decidable.decide (0 < p.positions) && p.sent.length == p.roots &&
      K2.increasing (p.read.map (·.1)) && Decidable.decide (p.logN ≤ 32)) = true := hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
    omega
  · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h0⟩

/-- At which numbers the fields are asked: K1's at a first tree of the number 0. -/
def oksOr : Oks := { g := fun gp => gp.firstTree = 0 }

/-- **EVERY MAKER OF THE SEAT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, AND THE SEAL: IT IS A
CODE SWITCH, OR A YES ADDS TO THE NUMBER OF ORACLE MESSAGES JUST WHAT ITS BLOCK TELLS.** Under
K1Told alone. -/
theorem seatCarry_or (h1 : K1Told) : SeatCarry (fun {_} b => PrO b) RO oksOr :=
  have M := seatCarry_msgs (ok2 := fun _ => False) seatKeeps_top h1 fun _ hp => hp.elim
  { frames := fun _ h => M.frames trivial h
    k1First := fun q gp h0 => wp_inr (M.k1First q gp h0)
    k1Later := fun q gp l p m a h0 => wp_inr (M.k1Later q gp l p m a h0)
    reads := fun h => wp_inr (M.reads h)
    k3 := fun c r X cs sh a _ h => wp_inr (M.k3 c r X cs sh a h)
    k4 := fun p => wp_inr (M.k4 p)
    k5 := fun W l g bf _ h => wp_inr (M.k5 W l g bf h)
    k6 := fun h => wp_inr (M.k6 h)
    k7 := fun W l => wp_inr (M.k7 W l)
    k8 := fun p => wp_inr (M.k8 p)
    k11 := fun Q => wp_inr (M.k11 Q)
    closeOf := fun p P b hb => wp_inr (M.closeOf p P b hb)
    batch := fun p _ hcl => wp_inr (M.batch p hcl)
    k2 := fun p _ => ⟨k2_or p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
    front := M.front
    openQ := fun P _ => M.openQ P trivial
    finFront := M.finFront
    finBehind := M.finBehind
    theSeal := fun inFront => Or.inr (M.theSeal inFront) }

#print axioms seatCarry_msgs
#print axioms seatCarry_or

end Meaning.Carry
