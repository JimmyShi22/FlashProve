-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/EntersFirst.lean: the first thread holds at the start of a run.
A run's start is what ready returns. The invariant at border 0 has seven clauses. Five follow from
ready, the instance's test and the description's own first state: the stored table, the fit of the
challenges, what was made, the riders and the input. The public promise at the first state follows from the head, where
the request's bytes parse. The items open at the chain's start follow from a served request and the
ties between the Script and the honest trace (ScriptTies), by opened_at_start_of_mark_pile.

What the theorem does not give. It is general in the Script: a stand at the real file is one where
ScriptTies is paid at the honest prover's Script, and at the same parts at which the thread's laws
stand. The index i and the request served are letters: ScriptTies ties them to the Script's cells
and messages, and nothing here ties these to the run's w₀ or to the run's field trace. At the honest
prover's Script those two ties come from the Script's own values: its cells are read off w₀, and its
messages off the trace.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.Thread.AskedIsToken
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Goal.HonestTrace.ConstrItemsAtStart
import Johnson.P5J.MgAtAll
import Johnson.P5J.TieAtStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (FileDescription)
open VerifierAndGoals.AtTheName (dpZ)
open P5J (TS CellsM)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open OnBytes.HonestTrace (ScriptTies ServesAt)
open Inst.Model Inst.Model.All

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {h : HeadAtReturn files A} {parts : FirstThreadParts A} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
  {k : Coins A.B} {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}

/-- At a return of the maker the prover's key is the instance's. -/
theorem key_at_return (h : HeadAtReturn files A) (x : ProofFile.Inst) : A.H.key x = x.pub.key := by
  obtain ⟨P, hP⟩ := h.returned
  rw [(atPure_ok hP).2.2.2.2.2.2.1]
  rfl

/-- Where the statement's words are read, the request is the words laid. -/
theorem stFromCall_req {P Q : Array UInt32} {T : Nat} {so : OnBytes.Model.Head.StOwn}
    (h : OnBytes.Model.Head.stFromCall P Q T = .ok so) : so.req = P := by
  unfold OnBytes.Model.Head.stFromCall at h
  simp only [OnBytes.Model.Head.needed, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl

/-- Where the covered positions are read, the request passes the first state's test. -/
theorem reqOk_of_coveredOf {s : VerifiableInference.Desc.First.S} {T V : Nat}
    {so : OnBytes.Model.Head.StOwn} {c : OnBytes.Model.Head.Covered} (hq : s.req = so.req)
    (hc : OnBytes.Model.Head.coveredOf so T V = .ok c) : s.reqOk T V = true := by
  have hy := coveredOf_y hc
  have h2 : (so.req.size == T + 2) = true := by
    cases e : (so.req.size == T + 2) with
    | true => rfl
    | false =>
      exfalso
      have e' : OnBytes.Model.Head.coveredOf so T V = .error "token-length" := by
        unfold OnBytes.Model.Head.coveredOf
        simp [OnBytes.Model.Head.needed, hy, e, bind, Except.bind]
      rw [e'] at hc
      cases hc
  have hsz : so.req.size = T + 2 := by simpa using h2
  have h3 : ((so.req.extract 0 T).map (·.toNat)).all (fun v => decide (v < V)) = true := by
    cases e : ((so.req.extract 0 T).map (·.toNat)).all (fun v => decide (v < V)) with
    | true => rfl
    | false =>
      exfalso
      have e' : OnBytes.Model.Head.coveredOf so T V = .error "token-range" := by
        unfold OnBytes.Model.Head.coveredOf
        simp only [OnBytes.Model.Head.needed, hy, h2, e, bind, Except.bind]
        simp
      rw [e'] at hc
      cases hc
  have h4 : (!(decide ((so.req.getD T 0).toNat ≥ (so.req.getD (T + 1) 0).toNat) ||
      decide ((so.req.getD (T + 1) 0).toNat > T))) = true := by
    cases e : (!(decide ((so.req.getD T 0).toNat ≥ (so.req.getD (T + 1) 0).toNat) ||
      decide ((so.req.getD (T + 1) 0).toNat > T))) with
    | true => rfl
    | false =>
      exfalso
      have e' : OnBytes.Model.Head.coveredOf so T V = .error "statement-range" := by
        unfold OnBytes.Model.Head.coveredOf
        simp only [OnBytes.Model.Head.needed, hy, h2, h3, e, bind, Except.bind]
        simp
      rw [e'] at hc
      cases hc
  have hT : s.reqT = T := by
    unfold VerifiableInference.Desc.First.S.reqT
    rw [hq, hsz]
    rfl
  unfold VerifiableInference.Desc.First.S.reqOk VerifiableInference.Desc.First.S.tokv
    VerifiableInference.Desc.First.S.rowR VerifiableInference.Desc.First.S.rowE
  rw [hT, hq, h2, h3, h4]
  rfl

/-- **Where the test on the instance says yes, the first state bears no mark.** -/
theorem no_mark_at_start (h : HeadAtReturn files A) (x : ProofFile.Inst)
    (hok : ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links A.Z x = true) :
    (ProofFile.startS A.Z x.pub).failed = none := by
  unfold ProofFile.okBy at hok
  cases hh : ProofFile.holdBy OnBytes.secondHashFunction ProofFile.pureRoad.links A.Z x with
  | error e =>
    rw [hh] at hok
    cases hok
  | ok g =>
    unfold ProofFile.holdBy at hh
    obtain ⟨_, -, hh⟩ := ok_of_bind hh
    obtain ⟨so, hso, hh⟩ := ok_of_bind hh
    obtain ⟨cov, hcov, -⟩ := ok_of_bind hh
    have hreq := stFromCall_req (ok_of_held hso)
    have hr : (A.Z.s₀.withReq (OnBytes.Model.Verify.words32 x.pub.request)).reqOk A.Z.p.X.T
        A.Z.p.X.P.h.V = true :=
      reqOk_of_coveredOf hreq.symm (ok_of_held hcov)
    have e := VerifiableInference.Desc.First.startP_is (P5J.pubBy_start h.head.toAtMg.laid.pub)
    unfold ProofFile.startS
    simp only
    rw [if_pos hr, e]
    rfl

/-- **At the first chain's last border the challenges heard are the chain's rounds**: the number that
lastWitness cuts off. -/
theorem heard_at_first_end {w : Local W₀ Rc ProofFile.Inst Tr} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (firstThread h parts w) h.description.first.blocksInOrder.length k s m E) :
    m.st.heard.length =
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length :=
  drawsFit_length _ _ hT.2.1

/-- **The entries of the layout's seats turn with no challenge**: at each of them the Script's message
reads the same at every list of challenges. The messages themselves may turn: what a later member
sends reads the challenges in front of it; the entries that hold the trace's symbols do not. -/
def SeatsTurnWithNoChallenge {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Zp : ProofFile.Pub)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) : Prop :=
  let X := P5J.At.X Zp
  let s := Meaning.sizesOf X
  let f := Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)
  ∀ m < 25, ∀ a < (s m).NM, ∀ i' < Alg.symRows ((s m).m a), ∀ c < (s m).k a,
    ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (h₁ h₂ : List Fmt.Drawn),
      Q.msg (f (Meaning.labAt X m a) i' c).1 k v h₁ false (f (Meaning.labAt X m a) i' c).2.1
          (f (Meaning.labAt X m a) i' c).2.2 =
        Q.msg (f (Meaning.labAt X m a) i' c).1 k v h₂ false (f (Meaning.labAt X m a) i' c).2.1
          (f (Meaning.labAt X m a) i' c).2.2

/-- **At one list of challenges the seats' entries hold the packing of the trace.** The list is meant
to be long enough for every sender: the lookups' law on LaysFilling is of that form. -/
def SymbolsAtOneList {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Zp : ProofFile.Pub)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (i : Cm.Idx) (x : Instance ppref)
    (long : List Fmt.Drawn) : Prop :=
  let X := P5J.At.X Zp
  let s := Meaning.sizesOf X
  let f := Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp)
  ∀ m < 25, ∀ a < (s m).NM, ∀ i' < Alg.symRows ((s m).m a), ∀ c < (s m).k a,
    Q.msg (f (Meaning.labAt X m a) i' c).1 k v
        (long.take (Q.fixedMsg (f (Meaning.labAt X m a) i' c).1)) false
        (f (Meaning.labAt X m a) i' c).2.1 (f (Meaning.labAt X m a) i' c).2.2 =
      Meaning.msgOf s (OnBytes.HonestTrace.theTrace (P5J.At.X Zp) i x) (Meaning.labAt X m a) false i' c

/-- **ScriptTies from one list of challenges**: where the seats' entries turn with no challenge, the
equation of the symbols at one list gives it at every list, the empty one too. -/
theorem scriptTies_of_one_list {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
    {xp : VerifiableInference.Desc.First.Look.Place}
    (hd : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) {Bk : ProverCoinCounts} {W₀ Rc T : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {k : Coins Bk} {v : Local W₀ Rc ProofFile.Inst T} {i : Cm.Idx} {x : Instance ppref}
    (hc : Holds (Q.cells v) i)
    (hr : (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
      (P5J.tokVOf (Q.tok v))).val = x)
    (F : SeatsTurnWithNoChallenge Zp Q) (long : List Fmt.Drawn)
    (R : SymbolsAtOneList Zp Q k v i x long) :
    ScriptTies Z Zp cF Q k v i x := by
  have raw : OnBytes.HonestTrace.ScriptSymsRawOn Zp Q k v
      (OnBytes.HonestTrace.theTrace (P5J.At.X Zp) i x) (fun _ _ => True) := by
    intro h₁ m hm a ha _ i' hi c hc'
    rw [F m hm a ha i' hi c hc' k v _ (long.take _)]
    exact R m hm a ha i' hi c hc'
  exact OnBytes.HonestTrace.scriptTies_of_rawOn hd (P₁ := fun _ _ => True) (P₂ := fun _ _ => True)
    (fun _ _ => Or.inl trivial) hc hr raw raw

/-- **The public promise holds at the first state**, where the request's bytes parse. -/
theorem firstThread_promise (w : Local W₀ Rc ProofFile.Inst Tr) (p : ProofFile.InstPub)
    (hReq : (_root_.Meaning.backReq (h.head.𝔇.reqB p)).isSome = true) :
    (firstThread h parts w).formP 0 (p, h.description.start₁ p) := by
  have T := h.head.tieStart (dpZ files)
  have hps : P5J.At.ps[0]? = some VerifiableInference.Desc.First.frontPlace := T.front_place_first
  have front := P5J.At.front_at (Zp := A.Z) (cF := h.firstChain)
  show VerifiableInference.Desc.First.onAt (P5J.At.N A.Z h.firstChain)
    (firstLetters h parts w).mgP P5J.At.links P5J.At.ps[0]? _ _ _ noStrs
  rw [hps, VerifiableInference.Desc.First.openSets_head, VerifiableInference.Desc.First.pubSets_head]
  refine VerifiableInference.Desc.First.onAt_start _ _ _ _ _
    (T.start_is_the_requests p) trivial ?_ ?_ ?_ front.1 front.2
  · intro _
    show (true && (_root_.Meaning.backReq (h.head.𝔇.reqB p)).isSome) = true
    rw [hReq]
    rfl
  · intro hz
    exact VerifiableInference.Desc.Sound.start_items_at (𝔇 := h.head.𝔇)
      (Mg₀ := VerifiableInference.Desc.Sound.mgBase) rfl rfl p _ _ _ _ _
      (P5J.start_lawful OnBytes.secondHashFunction A.Z h.places h.firstChain h.head.toAtMg.laid.pub p hz)
  · intro _
    exact VerifiableInference.Desc.Sound.start_says (𝔇 := h.head.𝔇)
      (Mg₀ := VerifiableInference.Desc.Sound.mgBase) (fun _ => ⟨rfl, rfl⟩) rfl _

/-- **The first thread holds at the start that ready gives**, under the instance's test, the parse of
the request's bytes, a served request and the Script's ties to it. -/
theorem enters_firstThread
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (hok : h.description.okStart x = true)
    (hReq : (_root_.Meaning.backReq (h.head.𝔇.reqB x.pub)).isSome = true)
    {i : Cm.Idx} {served : Instance ppref} (Sv : ServesAt (P5J.At.X A.Z) i served)
    (Ti : ScriptTies files A.Z h.firstChain parts.script k R.own i served) :
    Enters₁ h.description A.H (firstThread h parts R.own) w₀ rc x k R := by
  obtain ⟨-, tr, -, hown, -, -, -, -⟩ := ready_ok hR
  have hrd := readyInput_of_ready hR hok
  have hf : (h.description.start₁ (h.description.pub x)).failed = none := by
    have hb : (ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links A.Z x && _) = true := hok
    exact no_mark_at_start h x (Bool.and_eq_true_iff.1 hb).1
  have hmark : (h.description.start₁ (h.description.pub x)).failed.isNone = true := by
    rw [hf]
    rfl
  have hPromise : (firstThread h parts R.own).formP 0
      ((firstThread h parts R.own).seat k (R.start₁ A.H)
        (h.description.start₁ (h.description.pub x))) := by
    have e : R.own.x = x := by rw [hown]
    show (firstThread h parts R.own).formP 0 (R.own.x.pub, h.description.start₁ x.pub)
    rw [e]
    exact firstThread_promise R.own x.pub hReq
  have hItems : (firstThread h parts R.own).Items ((firstThread h parts R.own).opened 0) k
      (h.description.start₁ (h.description.pub x)) (R.start₁ A.H)
      (envOf (A.H.storedWords w₀ rc) (fun _ _ => none) []) := by
    have hlaw := P5J.start_lawful OnBytes.secondHashFunction A.Z h.places h.firstChain h.head.toAtMg.laid.pub
      (h.description.pub x) hf
    refine OnBytes.HonestTrace.opened_at_start_of_mark_pile h.head A.H parts.script _ _ _ _ _ _ _ _
      _ _ k (R.start₁ A.H) Sv Ti _ _ hf ?_
    intro ds j hj
    obtain rfl := List.mem_singleton.1 hj
    show ∀ r ∈ VerifiableInference.Desc.First.S.rows (h.description.start₁ (h.description.pub x)), _
    rw [hlaw]
    intro r hr
    cases hr
  unfold Enters₁ Thr Thread.Hand Thread.Fit Thread.Form Thread.Made
  refine ⟨⟨fun i p => ?_, fun σ hσ => ?_⟩, rfl, ⟨hmark, hPromise⟩, hItems, ⟨rfl, rfl, rfl,
    fun _ _ => rfl, h.description.start₁ (h.description.pub x), [], ?_, rfl, rfl⟩, ?_, ⟨rfl, hrd⟩⟩
  · show A.H.storedWords w₀ rc i p = A.H.storedWords R.own.w₀ R.own.rc i p
    rw [hown]
  · have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  · show h.description.start₁ (h.description.pub x) = ProofFile.startS A.Z R.own.x.pub
    rw [hown]
    rfl
  · refine ⟨fun hb => absurd hb (by decide), fun c hc hlo _ => ?_⟩
    exfalso
    rcases csHead_span hc with ⟨a, -⟩ | ⟨l, -, e, -⟩ | ⟨g, -, e, -⟩ | ⟨g, -, e, -⟩ <;> omega

/-- **The shared thread holds at the start that ready gives**, under the form outside K14's borders
at the chain's first state, the stored table's pin there, and what rides there. -/
theorem enters_sharedThread {Wt : Type} {reads : IndexReaders W₀ Rc}
    {shared : SharedThreadParts A Wt}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (hshape : shared.shape 0 (h.description.start₂ (h.description.pub x)) = true)
    (hpin : ∀ ds, (sharedThread h reads shared R.common).means R.common .pinT
      ((sharedThread h reads shared R.common).seat k (R.start₂ A.H)
        (h.description.start₂ (h.description.pub x)))
      ((sharedThread h reads shared R.common).strs
        (envOf (A.H.storedWords w₀ rc) (fun _ _ => none) []))
      ((sharedThread h reads shared R.common).wit k R.common ((R.start₂ A.H).st.heard ++ ds)))
    (hrides : shared.rides 0 R.common (h.description.start₂ (h.description.pub x))) :
    Enters₂ h.description A.H (sharedThread h reads shared R.common) w₀ rc x k R := by
  have hkey := key_at_return h x
  have hform : (sharedThread h reads shared R.common).form 0
      ((sharedThread h reads shared R.common).seat k (R.start₂ A.H)
        (h.description.start₂ (h.description.pub x))) = true := by
    show (ProofFile.Honest.K14.form2 (VerifiableInference.Desc.K1.qAt A.Z h.places) shared.shape 0
        (h.description.start₂ (h.description.pub x)) && _) = true
    have e : ProofFile.Honest.K14.form2 (VerifiableInference.Desc.K1.qAt A.Z h.places) shared.shape 0
        (h.description.start₂ (h.description.pub x)) =
          shared.shape 0 (h.description.start₂ (h.description.pub x)) :=
      if_neg (by omega)
    rw [e, hshape]
    rfl
  have horder : (sharedThread h reads shared R.common).formP 0
      ((sharedThread h reads shared R.common).seat k (R.start₂ A.H)
        (h.description.start₂ (h.description.pub x))) :=
    OnBytes.Means.InOrder.start _
  have hItems : (sharedThread h reads shared R.common).Items
      ((sharedThread h reads shared R.common).opened 0) k
      (h.description.start₂ (h.description.pub x)) (R.start₂ A.H)
      (envOf (A.H.storedWords w₀ rc) (fun _ _ => none) []) := by
    intro ds i hi
    have hi' : i ∈ [VerifiableInference.Desc.Shared.ItemS.pinT] := hi
    obtain rfl := List.mem_singleton.1 hi'
    exact hpin ds
  obtain ⟨ht, tr, -, -, hcom, -, -, -⟩ := ready_ok hR
  unfold Enters₂ Thr Thread.Hand Thread.Fit Thread.Form Thread.Made
  refine ⟨⟨fun i p => ?_, fun σ hσ => ?_⟩, rfl, ⟨hform, horder⟩, hItems, ⟨rfl, rfl, rfl,
    fun _ _ => rfl, h.description.start₂ (h.description.pub x), [], ?_, rfl, rfl⟩, hrides, ?_⟩
  · show A.H.storedWords w₀ rc i p = A.H.storedWords R.common.w₀ R.common.rc i p
    rw [hcom]
  · have hσ' : σ ∈ ([] : List Fmt.TreeSource) := hσ
    cases hσ'
  · have ek : R.common.key = x.pub.key := by
      rw [hcom]
      exact hkey
    show h.description.start₂ (h.description.pub x) =
      _root_.Desc.K14.first (VerifiableInference.Desc.K1.qAt A.Z h.places).codes R.common.key
    rw [ek]
    rfl
  · refine ⟨rfl, ?_⟩
    show A.H.inRange R.common.w₀ = true
    rw [hcom]
    exact tests_inRange ht

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.enters_sharedThread
#print axioms ProofFile.Honest.FirstThread.heard_at_first_end
#print axioms ProofFile.Honest.FirstThread.scriptTies_of_one_list
#print axioms ProofFile.Honest.FirstThread.key_at_return
#print axioms ProofFile.Honest.FirstThread.no_mark_at_start
#print axioms ProofFile.Honest.FirstThread.firstThread_promise
#print axioms ProofFile.Honest.FirstThread.enters_firstThread
