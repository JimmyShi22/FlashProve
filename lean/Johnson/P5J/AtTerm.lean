-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/AtTerm.lean: THE PROOF FILE's ROWS (RowsTied, Johnson/P5J/SevenOfTied.lean) AT THE SEATED DESCRIPTION's OWN TERM, WITH WHAT "ONE DECODER" PROVES THERE, IN ONE TERM. One abbreviation, two definitions of letters, seven theorems, one term whose type is what Lean infers, two controls. (EachGood is asked KIND BY KIND: ∀ K, KindTied Nn ‹the first meaning› fullLinks ps ‹the table's extractor› ‹the first chain's pieces› K: through eachTied_of_kinds, Johnson/Desc/Sound/TiedPlaces.lean; its premise on the lengths is TablesFit's len₁. Filled too: TablesFit's START · fin_is_canonical · public_part_free_of_reply · start_is_the_requests, where Zp is the plain road's public part.) A joint build of several kinds' files.

THE LETTERS THAT ARE FILLED: F₀ := F0T o Zp Np cF (= descZ … (secondAt …) …, Johnson/Desc/Sound/AtDescPure.lean: the term that the description's maker's value is) · XiP := ProofFile.Inst · instP := LPFD.Full.instanceAsPlainRecord (the seated map) · N := numsFull · getS := the identity · reqB := the public part's field request · asked := ProofFile.Inst.asked ·
DT := dtK: THE FIRST TABLE's DECODER := decShared: the shared chain's decK at the term's own start₂ · kS₂ := ksK: first codes (keyOf of the record). ALL OTHER LETTERS STAY LETTERS, TYPED AT THE TERM (their list is the tower's own, taken off its file by program).
  hdec_at_term · fin_at_term · pub_free_at_term: the tower's premise hdec and its fields fin_is_canonical | public_part_free_of_reply, to the letter, at these fillings.
  orSay_ok · pubBy_start: the public part's first record s₀ IS what the road's start made (read off pubBy's text, beside pubBy_made) · start_at_term: the field start_is_the_requests at codes := the first chain's codes, rq := the request's words: one call of the table's isStart_if.
  start3_no_mark_at_term: TablesFit's START: where the last chain has a first record the first chain's last record bears no mark: the frame's start₃'s own first test.
  rows_at_term: **RowsTied AT THE TERM FROM WHAT IS LEFT**: a term (it takes hs · hpub · hN · hG · hTP · hpT): RowsTied.mk with requests_to_instances (all three conjuncts) · start_is_the_requests · fin_is_canonical · public_part_free_of_reply · shared_start_is_the_records · tables_fit's TP, PW and START FILLED (TP | PW by tp_by_make | pw_by_make, Johnson/Desc/Sound/OneByMake.lean, at st₂ := the term's own start₂ IN BOTH the decoder and the joint; that the tower's first meaning's decodes | pinW ARE decodesOf | pinWOf dtK: rfl, through its two wrappers); at any Pm | MgS
    whose tablePromise | pinT are decK's (hTP | hpT: equations that can only be WRITTEN where the second state's type is St); the other fields are its arguments, in the structure's order. ITS TYPE IS WHAT LEAN INFERS (#check prints it).
  TWO CONTROLS: hTP | hpT ARE MET, by rfl, at the shared table's named fillings pmPoint | mgJoint (Johnson/Desc/Sound/PointAtFilling.lean | JointFilling.lean).
WHAT IT SHOWS: that the tower's letters CAN be filled at the seated term by terms typed at St, and that these fields are then proved together. WHAT IT DOES NOT: any other field: EachGood, shared_joint_count, leads3_last_chains_table and the rest stay premises, and no filling is known at which they are met together.

Limits. The full size alone. cF (the first chain) is a letter. NO MEMBER. Nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.SevenOfTied
import Johnson.Desc.Sound.AtDescPure
import Johnson.Desc.Sound.JointFilling
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Sound.TiedPlaces

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open Desc.K14 (St first p14Of beforePointOf)
open Desc.K14.Law (descZ secondAt fullShapeB full_index decShared decK heldFull rankLib hd_at_seat tp_by_make pw_by_make)

/-- **The seated description's own term.** -/
abbrev F0T (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) : FileDescription ProofFile.Inst :=
  descZ o Zp Np (secondAt Zp Np) cF

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp)) (DP : WholeD)
  (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  (hs : fullShapeB (p14Of Zp.p.chains (beforePointOf Np)).par.S = true) (err : ℕ) {Tok : Type}
  (d₀ : TReq) (cs : OnBytes.Codes) (arr : ℕ → ℕ
  → ℕ) (ms : List Mem) (Nn : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (f : Tok → Fin ppref.V)
  (hN : SeatsNamed arr Nn s seat) (hG : GroupsSeated ms Nn)
  (Q₀ : PlacesAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (F0T o Zp Np cF) (Wit (CellsM numsFull) Tok MsgT))
  (Mg : VerifiableInference.Desc.First.Meaning (F0T o Zp Np cF).XiPub (Wit (CellsM numsFull) Tok MsgT))
  (ps : List Place)
  (headPart : TPart → Cm.Idx → (F0T o Zp Np cF).XiPub × TS → Strs → Wit (CellsM numsFull) Tok MsgT → Prop)
  (digitsPart : ℕ → (F0T o Zp Np cF).XiPub × TS → Strs → Wit (CellsM numsFull) Tok MsgT → Prop)
  {Xg : Type} (Gd : FileDescription Xg)
  (smp : (F0T o Zp Np cF).XiPub × TS → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (c₀ : CellsM numsFull) (tokOf : (F0T o Zp Np cF).XiPub × TS → Tok)
  (Ns : NumbersS) (MgS : MeaningS (F0T o Zp Np cF).S₂ ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) (Wit (CellsM numsFull) Tok MsgT))
  (ML : MeaningL (F0T o Zp Np cF).S₃ (Wit (CellsM numsFull) Tok MsgT)) (Pm : PromMeaning (F0T o Zp Np cF).S₂)
  (PLm : PromMeaningL (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).S₃ ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁)) (split : Bool)
  (Q₂ : ℕ → (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str →
    (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (rP : RecFull) (depthReq : ℕ)
  (c₁ : Block (F0T o Zp Np cF).S₁ (F0T o Zp Np cF).Cl) (k₁ : List (Block (F0T o Zp Np cF).S₁ (F0T o Zp Np cF).Cl)) (c₂ : Block (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).Cl)
  (k₂ : List (Block (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).Cl)) (c₃ : Block (F0T o Zp Np cF).S₃ (F0T o Zp Np cF).Cl) (k₃ : List (Block (F0T o Zp Np cF).S₃ (F0T o Zp Np cF).Cl))
  (e₁ : (i : ℕ) → (ds : List RDT) → ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM numsFull) Tok MsgT → Wit (CellsM numsFull) Tok MsgT)
  (e₂ : (i : ℕ) → (ds : List RDT) → (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM numsFull) Tok MsgT → Wit (CellsM numsFull) Tok MsgT)
  (e₃ : (i : ℕ) → (ds : List RDT) → (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) × (F0T o Zp Np cF).S₃) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃
        (F0T o Zp Np cF).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM numsFull) Tok MsgT → Wit (CellsM numsFull) Tok MsgT)
  (dW wEnd : Wit (CellsM numsFull) Tok MsgT) 


/-- **The first table's decoder at the term**: the shared chain's guarded decoder at the term's own start₂. -/
def dtK : (ℕ → Option (ℕ × List UInt64)) → (F0T o Zp Np cF).XiPub × TS → Option (CellsM numsFull) :=
  decShared (p14Of Zp.p.chains (beforePointOf Np)).par err 2852142980
    (rankLib (p14Of Zp.p.chains (beforePointOf Np)).par.S.fold)
    (heldFull (p14Of Zp.p.chains (beforePointOf Np)).par err
      (p14Of Zp.p.chains (beforePointOf Np)).par.S.fold.index.saltBytes
      (full_index (p14Of Zp.p.chains (beforePointOf Np)).par.S hs) numsFull pp E)
    (F0T o Zp Np cF).start₂

/-- The shared chain's first state, of the key file's record. -/
def ksK (rec : RecFull) : (F0T o Zp Np cF).S₂ :=
  first (p14Of Zp.p.chains (beforePointOf Np)).codes (keyOf (fun β : NZ => β.val) rec)

/-- **hdec at the term.** -/
theorem hdec_at_term (z : (kcReq numsFull pp E).conf.X × (kcReq numsFull pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) :
    dtK E o Zp Np cF hs err
        (strsOf (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0)
          (y, fun _ => [])).cell
        ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z),
          (F0T o Zp Np cF).start₁ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z))) =
      (kcReq numsFull pp E).conf.D y z.2 :=
  hd_at_seat o ProofFile.pureRoad.links Zp Zp.p.chains (beforePointOf Np) _ [] _ _ (secondAt Zp Np) (fun s => s)
    (ProofFile.startS Zp) cF err hs pp E z DP (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0
    (y, fun _ => []) _

omit hs in
/-- **fin_is_canonical at the term**: the last test's yes holds S.finAsked at what the instance asks: the first of the four conjuncts of the frame's own text. (`fileDescBy_fin`, Johnson/Desc/ProofFile/Law/FileFields.lean, states the same at the frame with parameters for the seats.) -/
theorem fin_at_term (ξ : ProofFile.Inst) (s₁ : (F0T o Zp Np cF).S₁) (s₂ : (F0T o Zp Np cF).S₂)
    (s₃ : (F0T o Zp Np cF).S₃) (hf : (F0T o Zp Np cF).fin ξ s₁ s₂ s₃ = true) :
    (s₁ : TS).finAsked ξ.asked = true := by
  have hf' : ((s₁ : TS).finAsked ξ.asked &&
      (s₁ : TS).req == OnBytes.Model.Verify.words32 ξ.pub.request &&
      ((Desc.K14.Law.seatZ Zp Np).ended s₂).isSome && (secondAt Zp Np).done s₃) = true := hf
  simp only [Bool.and_eq_true] at hf'
  exact hf'.1.1.1

omit hs in
/-- **public_part_free_of_reply at the term**: the seated map lays the request file's bytes and the record's key; the request file at the instance without its reply is the one at the instance (requestBytesOf_withoutReply, Johnson/Flat/WordsBytes.lean). -/
theorem pub_free_at_term (x : (kcReq numsFull pp E).conf.X) (rec : (kcReq numsFull pp E).conf.Rec) :
    (F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord (reqWithoutReply x, rec)) =
      (F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord (x, rec)) := by
  have ext : ∀ a b : ProofFile.InstPub, a.request = b.request → a.key = b.key → a = b := by
    intro a b h1 h2
    cases a
    cases b
    simp_all
  refine ext _ _ ?_ rfl
  show (LPFD.Full.instanceAsPlainRecord (reqWithoutReply x, rec)).pub.request = (LPFD.Full.instanceAsPlainRecord (x, rec)).pub.request
  rw [LPFD.Full.instOf_request, LPFD.Full.instOf_request]
  rfl

/-- Where "or say" returns, its option held a value. -/
theorem orSay_ok {α : Type} {why : String} {x : Option α} {a : α} (h : ProofFile.orSay why x = .ok a) :
    x = some a := by
  cases x with
  | none => cases h
  | some b => exact congrArg some (Except.ok.inj h)

/-- **The public part's first record is what the road's start made**: read off the maker of the public part (Johnson/Desc/ProofFile/Pub.lean: pubBy), beside pubBy_made (Johnson/Desc/ProofFile/Law/MakerPublic.lean). THE PROOF HOLDS BY THE SHAPE OF pubBy's TEXT: it fails to compile at the first change of pubBy: a guard. -/
theorem pubBy_start
    {made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made} {st : ProofFile.Starts}
    {pol lay KL : ByteArray} {Zq : ProofFile.Pub} (h : ProofFile.pubBy made st pol lay KL = .ok Zq) :
    st.start (st.par Zq.made.p.chains.proof.first) Zq.made.p.chains.proof.first = some Zq.s₀ := by
  unfold ProofFile.pubBy at h
  obtain ⟨m, _, h⟩ := ProofFile.Law.bind_ok h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; exact orSay_ok (by assumption))

omit hs in
/-- **start_is_the_requests at the term**: where Zp is the plain road's public part of three files: the first chain's first record is a start at the request's words. One call of the table's isStart_if; on this base the start's other name is the plain one's by definition. -/
theorem start_at_term {pol lay KL : ByteArray} (hpub : ProofFile.pubPlain o pol lay KL = .ok Zp)
    (p : (F0T o Zp Np cF).XiPub) :
    VerifiableInference.Desc.First.IsStart Zp.made.p.chains.proof.first.codes
      (OnBytes.Model.Verify.words32 (p : ProofFile.InstPub).request) ((F0T o Zp Np cF).start₁ p) :=
  VerifiableInference.Desc.First.isStart_if
    (Pp := VerifiableInference.Desc.First.parP Zp.made.p.chains.proof.first)
    (shape := Zp.made.p.chains.proof.first.shape) (layout := Zp.made.p.chains.proof.first.layout)
    (pubBy_start hpub) Zp.p.X.T Zp.p.X.P.h.V (OnBytes.Model.Verify.words32 (p : ProofFile.InstPub).request)

omit hs in
/-- **TablesFit's START at the term**: where the last chain has a first record, the first chain's last record bears no mark: the frame's start₃ asks S.fin of it in its first line (Frames1.lean), and S.fin's first conjunct is "no mark". -/
theorem start3_no_mark_at_term (p : (F0T o Zp Np cF).XiPub) (s₁ : (F0T o Zp Np cF).S₁)
    (s₂ : (F0T o Zp Np cF).S₂) (s : (F0T o Zp Np cF).S₃)
    (h : ((F0T o Zp Np cF).start₃ p s₁ s₂).toOption = some s) : (s₁ : TS).failed = none := by
  have h' : (if (!(s₁ : TS).fin) = true then
        (Except.error "the first chain does not stand at its end" : Except String (secondAt Zp Np).σ)
      else
        match (Desc.K14.Law.seatZ Zp Np).ended s₂ with
        | none => .error "the shared chain has not ended"
        | some e => (secondAt Zp Np).start p s₁ e).toOption = some s := h
  by_cases hf : (!(s₁ : TS).fin) = true
  · rw [if_pos hf] at h'
    cases h'
  · have hf' : (s₁ : TS).fin = true := by simpa using hf
    unfold VerifiableInference.Desc.First.S.fin at hf'
    simp only [Bool.and_eq_true] at hf'
    exact Option.isNone_iff_eq_none.1 hf'.1.1

/-- **RowsTied AT THE TERM, FROM WHAT IS LEFT.** Its type is what Lean infers. -/
def rows_at_term {pol lay' KL : ByteArray} (hpub : ProofFile.pubPlain o pol lay' KL = .ok Zp)
    (hTP : Pm.tablePromise = decodesOf (decK (p14Of Zp.p.chains (beforePointOf Np)).par err 2852142980
      (rankLib (p14Of Zp.p.chains (beforePointOf Np)).par.S.fold)
      (heldFull (p14Of Zp.p.chains (beforePointOf Np)).par err
        (p14Of Zp.p.chains (beforePointOf Np)).par.S.fold.index.saltBytes
        (full_index (p14Of Zp.p.chains (beforePointOf Np)).par.S hs) numsFull pp E)))
    (hpT : MgS.pinT = pinWOf (decK (p14Of Zp.p.chains (beforePointOf Np)).par err 2852142980
      (rankLib (p14Of Zp.p.chains (beforePointOf Np)).par.S.fold)
      (heldFull (p14Of Zp.p.chains (beforePointOf Np)).par err
        (p14Of Zp.p.chains (beforePointOf Np)).par.S.fold.index.saltBytes
        (full_index (p14Of Zp.p.chains (beforePointOf Np)).par.S hs) numsFull pp E))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 l1 l2 l3 tEND tSH tSH3 tPOf tPOb tStep a10 a12 a13 a14 a15 a16 =>
    (RowsTied.mk (Z := Z) (lay := lay) (X := X) (N := numsFull) (E := E) (DP := DP) (F₀ := F0T o Zp Np cF)
      (instP := LPFD.Full.instanceAsPlainRecord) (getS := fun s => s) (reqB := fun q : ProofFile.InstPub => q.request)
      (DT := dtK E o Zp Np cF hs err) (asked := ProofFile.Inst.asked) (d₀ := d₀) (cs := cs) (arr := arr) (ms := ms)
      (Nn := Nn) (s := s) (seat := seat) (f := f) (hN := hN) (hG := hG) (Q₀ := Q₀) (Mg := Mg) (ps := ps)
      (headPart := headPart) (digitsPart := digitsPart) (Gd := Gd) (smp := smp) (c₀ := c₀) (tokOf := tokOf)
      (Ns := Ns) (MgS := MgS) (ML := ML) (Pm := Pm) (PLm := PLm) (split := split) (Q₂ := Q₂)
      (depthReq := depthReq) (c₁ := c₁) (k₁ := k₁) (c₂ := c₂) (k₂ := k₂) (c₃ := c₃) (k₃ := k₃) (e₁ := e₁)
      (e₂ := e₂) (e₃ := e₃) (dW := dW) (wEnd := wEnd) (kS₂ := ksK o Zp Np cF) (codes := Zp.made.p.chains.proof.first.codes)
      (rq := fun p : ProofFile.InstPub => OnBytes.Model.Verify.words32 p.request)
      a1 a2 a3 a4 (VerifiableInference.Desc.Sound.eachTied_of_kinds _ _ _ _ _ _
        (Nat.le_of_eq ((Nat.add_comm _ 1).trans l1)) a5) a6 a7 a8
      ⟨l1, l2, l3, tEND,
        tp_by_make _ err 2852142980 _ _ _ _ _ _ _ _ _ _ _ _ _ (F0T o Zp Np cF).start₂ _ _ (fun _ => rfl) _ _ _ Pm
          rfl hTP,
        tSH,
        pw_by_make _ err 2852142980 _ _ _ _ _ _ _ _ _ _ _ _ (F0T o Zp Np cF).start₂ _ _ (fun _ => rfl) _ _ _ MgS
          rfl hpT,
        start3_no_mark_at_term o Zp Np cF, tSH3, tPOf, tPOb, tStep⟩
      a10 (start_at_term o Zp Np cF hpub) a12 a13 a14 a15 a16
      ⟨hdec_at_term E DP o Zp Np cF hs err, LPFD.Full.instOf_request, fun _ => rfl⟩
      (fin_at_term o Zp Np cF) (pub_free_at_term E o Zp Np cF) (fun _ _ => rfl) hN hG)

end P5J

-- TWO CONTROLS: the two equations that rows_at_term asks of the shared table's letters hold at that table's named fillings: by rfl
example {Xi Cells : Type} (cs : OnBytes.Codes) (G : VerifiableInference.Desc.FileDescription Xi) (smp₂ ms₂) (p : Desc.Plain.Par)
    (err₂ eM : Nat) (rank) (held) (stOf₂ bookOf₂ Pm₀) :
    (Desc.K14.Law.pmPoint (Cells := Cells) cs G smp₂ ms₂ p err₂ eM rank held stOf₂ bookOf₂ Pm₀).tablePromise =
      VerifiableInference.Desc.Sound.decodesOf (Desc.K14.Law.decK p err₂ eM rank held) := rfl

example {Xi P₀ P₁ Cells Tok : Type} (cs : OnBytes.Codes) (G : VerifiableInference.Desc.FileDescription Xi) (arr)
    (get : P₁ → P₀ × VerifiableInference.Desc.First.S) (smp₁ ms₁ xW smp₂ ms₂ lay₀ stOf tabP rg omW)
    (p : Desc.Plain.Par) (e' gOf) (err₂ eM : Nat) (rank) (held) (Pw matC Mg₀) :
    (Desc.K14.Law.mgJoint (Cells := Cells) (Tok := Tok) cs G arr get smp₁ ms₁ xW smp₂ ms₂ lay₀ stOf tabP rg omW p e' gOf
      err₂ eM rank held Pw matC Mg₀).pinT =
      VerifiableInference.Desc.Sound.pinWOf (Desc.K14.Law.decK p err₂ eM rank held) := rfl

#check @P5J.rows_at_term
#print axioms P5J.hdec_at_term
#print axioms P5J.pubBy_start
#print axioms P5J.start_at_term
#print axioms P5J.start3_no_mark_at_term
#print axioms P5J.fin_at_term
#print axioms P5J.pub_free_at_term
#print axioms P5J.rows_at_term
