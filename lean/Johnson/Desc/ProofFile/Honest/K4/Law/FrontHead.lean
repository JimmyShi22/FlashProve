-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FrontHead.lean: CONDITIONAL. Statements with their proofs.

What is here. Three clauses of `K4FrontAt` (Honest/K4/Law/Kept.lean, whose head says who has each of
its clauses): asks, names and reads, each in its own text, at every accepted step of the member of
the feed-forward layers' own rounds (sub-protocol K4) where a thread of the first chain stands, at
the public files' own data, any prover and a run's input (`lettersHead`,
Honest/Thread/FirstHead.lean). The clause stated is not here: Law/StatedHead.lean.

How. The library derives the three from tests with code on the verifier's state in front of the
member, inside the proof of its `own_at` (Johnson/Road/K4/More/OwnAtState.lean), out of one
structure, `More.OwnFront`; and it makes that structure of the promise's public tests inside the
proofs of `eleven_at_all` and `made_eleven` (Johnson/Road/K4/More/). Section 1 types these two roads
again, after the library's proof texts, and ends in the three clauses; for the clause reads it goes
after the first lines of the proof of the library's `four_of_kept`
(Johnson/Road/K4/Rec/InTFour.lean). Section 2 has section 1's premises where the thread stands: the
promise's tests out of the thread's form; `K4Fence` (`k4Fence_at`, Law/BehindHead.lean;
`k4_heard_head`, Law/ReadyHead.lean); the hypotheses on the public parameters (`nine_head`,
`named_head`, Law/ElevenHead.lean).

  `ownFront_at_all`   the library's `More.OwnFront` from the promise's public test, the book-keeping
      and `K4Fence`
  `front_three_at_all`   **asks, names, reads behind an accept**, at the composed meaning's own
      public tests
  `ePubAt_of_held`   the promise's public test under its other name
  `thr_tests`   where the thread stands: the promise's test on the state's shape, its public test
      and its test on the book accept
  `front_three_head`   the three clauses at the thread, together
  `asks_head`, `names_head`, `reads_head`   **the three clauses at the thread**

Not shown here. THAT THE THREAD HOLDS AT ANY RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: hT and hS
are hypotheses. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). h: the library's hypothesis on the public files (`P5J.AtMgA`). Of
h together with hb, hT and hS this file gives no example (`LaidK4`: h gives it at each group:
`laid_at`, Law/LaidAtGroup.lean). THE FULL SIZE's WRITTEN LISTS ALONE; section 2: the format's
second hash function alone (`OnBytes.secondHashFunction`) besides. Nothing on what any form is worth. A LAW, NOT A PART:
no file that defines a part of the proof file's description may import this one: its imports reach
Johnson/Goal/, as those of Law/ElevenHead.lean do. Following import lines, and stopping unopened at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module
whose name begins Cb.Bridge, its imports reach 70 modules under Johnson/Goal/, 7 under
Johnson/Bridge/ and 1 whose name begins Cb.Bridge, and none of the others; what lies behind these is
not counted; 46 of the modules that it reaches have RecCompile in their names, none of them
RecCompile's Honest*, Both or PassH*. Nothing on soundness, on completeness or on any other
property.

Kin. The clause names is, word for word, also the field names of the library's `InTAsks`
(Johnson/Road/K4/InT/Statement.lean); that structure's field reads is another sentence than the
clause reads. `thr_tests` begins as the proof of `k4ReadyS_head` (Law/ReadyHead.lean) does: from the
thread's form to the promise's tests. The library's `xk_of_form` (Honest/Thread/FormXK.lean) with
`IM.xk_parts` (Johnson/IMR/HandsDef.lean) has the promise's six tests from the thread's form at any
letters of the first chain: `thr_tests` has three of them, at `lettersHead`: the public test and the
test on the book in the spelling in which section 1 asks them, and the test on the state's shape,
which no statement of this file asks; `thr_pub` and `thr_pubI` (Honest/Thread/FormLaw.lean,
Honest/Thread/FormLawI.lean) hand out the public test item by item. `ePubAt_of_held` is the
library's `ePubAt_pubHeld` (Johnson/Desc/First/EPubAt.lean) under two equations on the meaning. None
of these five of the library's is called here.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead
import Johnson.Desc.ProofFile.Honest.K4.Law.ReadyHead
import Johnson.Desc.ProofFile.Honest.K4.Law.BehindHead
import Johnson.Road.K4.More.ElevenAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4 (AtK4 K4OnX K4OnD K4NamedW CellsK KeptAtS kept_atS parOf readsArrayB
  k4DataWide k4Means_mgWide k4RowPlan_wide k4PlaceAt)
open OnBytes.Road.K4.Rec (recPlanOf recMeans_of_means recIs_at_state recIs_behind readsArray_plan)
open OnBytes.Road.K4.Riders (keptAsks_of_front padNames_of_left)
open OnBytes.Road.K4.More (PS K4Fence front_mem hasAtK4 has_ledger has_freeAbove has_look
  has_linkFresh has_lookLeft has_sentIs has_treesAre)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Wit)
open VerifiableInference.Desc.First (S pubAll ePubAt shapeAt bookAt pubHeld pubWide_hand onAt
  openSets pubSets start)
open VerifiableInference.Desc.First.FillK4 (isLay look_agrees)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT mgWide MgData WideData mgBase linksFull moreAll
  mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead noStrs)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Sits_head)

/-- The table's public items (`Pub` alone would name another type in this namespace). -/
local notation "PubI" => VerifiableInference.Desc.First.Pub

/-! ## 1 At the composed meaning's own public tests -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X} {E : WideData P}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

variable {k m : ℕ} {pl : Place} {par : Par}
  {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
  {layout : Option ByteArray} {n : ℕ}

/-- **The library's `More.OwnFront` at a state in front of the member**, after the proof texts of
the library's `eleven_at_all` and `made_eleven`. CONDITIONAL on every hypothesis named. -/
theorem ownFront_at_all (hH : isLay Dm.links (headLink X) = false) (H : AtK4 linksFull PS k m pl)
    (Sx : K4OnX X pol KL layout m par) (Sd : K4OnD Dm m par n) (Sn : K4NamedW Dm E k m par told n)
    {z : P} {s : S} (hE : ePubAt (pubAll Dm.pubD (Bm).pub) moreAll linksFull PS k (z, s) = true)
    (hb : bookAt Dm.N PS[k]? s = true) (Fc : K4Fence Dm E m s) :
    OnBytes.Road.K4.More.OwnFront par (recPlanOf (k4DataWide Dm E Bm) (k4DataWide Dm E Bm).sd)
      ((k4DataWide Dm E Bm).N.msgsAt PS[k]?) m par.hp.ns s := by
  have Em := k4Means_mgWide Dm E Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have Pl := k4RowPlan_wide Dm E H Sx Sd Sn
  have hand : ∀ (q : PubI), VerifiableInference.Desc.First.classA q = false → ∀ a,
      (mgWide Dm E Bm).pub q a = pubAll Dm.pubD (Bm).pub q a := fun q hq a =>
    pubWide_hand E.d12 E.dP Dm.pubD (Bm).pub q hq a
  have fr : ∀ {f : ℕ → PubI}, hasAtK4 moreAll linksFull PS f = true →
      VerifiableInference.Desc.First.classA (f m) = false →
      (mgWide Dm E Bm).pub (f m) (z, s) = true := fun {f} hf hc => by
    rw [hand _ hc]
    exact List.all_eq_true.1 hE _ (front_mem H hf)
  have hl : isLay (k4DataWide Dm E Bm).links m = true := by
    rw [Pl.linksIs]
    unfold isLay
    rw [H.sub]
    rfl
  have RM := recMeans_of_means Em (k4DataWide Dm E Bm).sd Em.sentIs Em.treesAre
  have f1 := fr (f := fun m => .ledger m) has_ledger rfl
  have f2 := fr (f := fun m => .freeAbove m) has_freeAbove rfl
  have f3 := fr (f := fun m => .look m) has_look rfl
  have f4 := fr (f := fun m => .linkFresh m) has_linkFresh rfl
  have f7 := fr (f := fun m => .more (some m) "K4.lookLeft") has_lookLeft rfl
  have f9 := fr (f := fun m => .more (some m) "frame.sentIs") has_sentIs rfl
  have f10 := fr (f := fun m => .more (some m) "ledger.treesAre") has_treesAre rfl
  have f13 : (mgWide Dm E Bm).pub (VerifiableInference.Desc.First.Look.liveItem m) (z, s) =
      true := by
    rw [Em.liveIs]
    exact Fc.live
  have g13 : (mgWide Dm E Bm).pub (.more (some m) "frame.liveIs") (z, s) = true := f13
  rw [Em.ledger] at f1
  rw [Em.freeAbove, Pl.nsOf] at f2
  have f2' : VerifiableInference.Desc.First.freeAboveB par.hp.ns s = true := by simpa using f2
  rw [Em.look m _ hl] at f3
  rw [RM.fresh] at f4
  rw [Em.lookLeft m _ hl] at f7
  rw [Em.sentIs] at f9
  rw [Em.treesAre] at f10
  rw [RM.live] at g13
  have hb' := hb
  simp only [bookAt, Bool.and_eq_true, beq_iff_eq] at hb'
  exact
    { ledger := f1
      free := f2'
      look := f3
      lookLeft := f7
      live := g13
      fresh := f4
      seats := Fc.seats
      shapes := Fc.shapes
      sent := f9
      trees := f10
      codes := Fc.codes
      places := hb'.1.2.trans hb'.2
      msgs := hb'.2
      heard := Pl.shape ▸ Fc.heard }

/-- **ASKS, NAMES AND READS BEHIND AN ACCEPT**, each in the text of `K4FrontAt`'s clause.
CONDITIONAL on every hypothesis named. -/
theorem front_three_at_all (hH : isLay Dm.links (headLink X) = false)
    (H : AtK4 linksFull PS k m pl) (Sx : K4OnX X pol KL layout m par) (Sd : K4OnD Dm m par n)
    (Sn : K4NamedW Dm E k m par told n) {z : P} {s s' : S} (K : KeptAtS par s s')
    (hE : ePubAt (pubAll Dm.pubD (Bm).pub) moreAll linksFull PS k (z, s) = true)
    (hb : bookAt Dm.N PS[k]? s = true) (Fc : K4Fence Dm E m s) :
    (∃ (P₀ : Layer.Pub) (o₀ : Own), KeptAsks par s s' P₀ o₀) ∧
      (∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F) ∧
      readsArrayB par.hp s' = true := by
  have OF := ownFront_at_all hH H Sx Sd Sn hE hb Fc
  have Pl := k4RowPlan_wide Dm E H Sx Sd Sn
  have hag : ∀ al, s.here = .lay al → al.fo = al.lookHeard := fun al hal =>
    look_agrees OF.look hal
  obtain ⟨o₀, A⟩ := keptAsks_of_front K OF.ledger OF.free OF.lookLeft hag OF.heard Pl.front
  refine ⟨⟨par.P, o₀, A⟩, fun al fo' hal hfo' =>
    padNames_of_left OF.lookLeft hal (hag al hal) hfo', ?_⟩
  have K0 := K
  obtain ⟨a, _, _, _, ha, _, _, _, _, _, _, _, hR, _⟩ := K0
  obtain ⟨A₀, hA₀, _, _⟩ := OnBytes.Desc.First.K4.InT.segAt_lay ha
  have r := recIs_at_state hA₀ OF.live OF.fresh OF.seats OF.shapes OF.sent OF.trees OF.codes
    OF.places OF.msgs
  obtain ⟨a', ha', _⟩ := hR.here a ha
  obtain ⟨A', hA', _, _⟩ := OnBytes.Desc.First.K4.InT.segAt_lay ha'
  have r' := recIs_behind K (OnBytes.Road.K4.Rec.sized_of_ledgerB OF.ledger) hA₀ hA' r
  rw [readsArray_plan r' par.hp ha' hA']
  exact Pl.readsP

/-- The promise's public test, under the name by which the library's statements ask it. -/
theorem ePubAt_of_held {Mg : VerifiableInference.Desc.First.Meaning P
      (Wit (CellsK rows cols) Tok MsgT)}
    (ePub : Mg.pub = pubAll Dm.pubD (Bm).pub) (eMore : Mg.more = moreAll) {z : P} {s : S}
    (h : pubHeld Mg ((openSets linksFull PS (start linksFull))[k]?.getD [])
      ((pubSets Mg.more linksFull PS)[k]?.getD []) (z, s) = true) :
    ePubAt (pubAll Dm.pubD (Bm).pub) moreAll linksFull PS k (z, s) = true := by
  rw [← ePub, ← eMore]
  exact h

end

/-! ## 2 At a thread of the first chain, at the public files' own data and any prover -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **Where the thread stands**: the promise's test on the state's shape, its public test and its
test on the book accept. CONDITIONAL on hT. -/
theorem thr_tests {k : ℕ} {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    shapeAt linksFull PS[k]? s = true ∧
      pubHeld (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP
        ((openSets linksFull PS (start linksFull))[k]?.getD [])
        ((pubSets (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP.more linksFull
          PS)[k]?.getD []) (mm.st.input.x.pub, s) = true ∧
      bookAt (P5J.At.N Zp cF) PS[k]? s = true := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -⟩ := hT'
  have hm : s.failed = none := by
    have e : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.mp e
  have ha : onAt (P5J.At.N Zp cF) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP
      linksFull PS[k]? ((openSets linksFull PS (start linksFull))[k]?.getD [])
      ((pubSets (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP.more linksFull
        PS)[k]?.getD []) (mm.st.input.x.pub, s) noStrs := hF.2
  have hB := (ha.2.resolve_left fun e => e hm).1
  simp only [Bool.and_eq_true] at hB
  exact ⟨hB.1.1.1.1.1, hB.1.2, hB.2⟩

/-- **THE THREE CLAUSES AT THE THREAD, TOGETHER.** CONDITIONAL: on h, Lh, hb, hT and hS. -/
theorem front_three_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk)
    {c : Coins Bk} {s s' : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
      cols s') :
    (∃ (P₀ : Layer.Pub) (o₀ : Own), KeptAsks (parOf x) s s' P₀ o₀) ∧
      (∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F) ∧
      readsArrayB (parOf x).hp s' = true := by
  have A := atK4_of_laid Lh
  obtain ⟨hH, Sx, Sd, _, hbd⟩ := nine_head h Lh
  have Sn := named_head h Lh
  obtain ⟨_, hdec⟩ := k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh blk hb s _ _ s' _
    hS.2
  have K : KeptAtS (parOf x) s s' := kept_atS hdec
  obtain ⟨_, t2, t3⟩ := thr_tests h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  have heard := k4_heard_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) hH A Sx Sd c s mm E hT
  have Fc := k4Fence_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A.here A.link
    (by rw [A.piece]; exact Nat.le_succ 2) (by omega) hT heard
  exact front_three_at_all hH A Sx Sd Sn K
    (ePubAt_of_held (Dm := h.𝔇)
      (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
      (mgAll_more_base h.𝔇) t2) t3 Fc

/-- **THE CLAUSE asks.** CONDITIONAL: on h, Lh, hb, hT and hS. -/
theorem asks_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk)
    {c : Coins Bk} {s s' : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
      cols s') :
    ∃ (P₀ : Layer.Pub) (o₀ : Own), KeptAsks (parOf x) s s' P₀ o₀ :=
  (front_three_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hb hT hS).1

/-- **THE CLAUSE names.** CONDITIONAL: on h, Lh, hb, hT and hS. -/
theorem names_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk)
    {c : Coins Bk} {s s' : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
      cols s') :
    ∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F :=
  (front_three_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hb hT hS).2.1

/-- **THE CLAUSE reads.** CONDITIONAL: on h, Lh, hb, hT and hS. -/
theorem reads_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk)
    {c : Coins Bk} {s s' : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
      cols s') :
    readsArrayB (parOf x).hp s' = true :=
  (front_three_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hb hT hS).2.2

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.ownFront_at_all
#print axioms ProofFile.Honest.K4.front_three_at_all
#print axioms ProofFile.Honest.K4.ePubAt_of_held
#print axioms ProofFile.Honest.K4.thr_tests
#print axioms ProofFile.Honest.K4.front_three_head
#print axioms ProofFile.Honest.K4.asks_head
#print axioms ProofFile.Honest.K4.names_head
#print axioms ProofFile.Honest.K4.reads_head
