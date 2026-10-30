-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06AtConst.lean: THE SHARE OF THE SUB-PROTOCOL AT THE OUTPUT
HEAD IN THE CHAIN OF PROMISES, AT THE CLOSED TERM FOR THE COMPOSED MEANING: mgAtAll h
(Johnson/P5J/MgAtAll.lean), UNDER ITS ONE HEAD AtMgA (in scope · the verifier's own value is laid ·
the named tests accept · what is handed in): AtMgA → ONE NAMED CONDITION → KindTiedR ... K6 at
mgAtAll h, GENERAL IN "REACHED" (the letter Rch), IN THE ROW OF PIECES (the letter l) AND IN THE
LETTER o FOR THE SECOND HASH FUNCTION.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  paid_at_const: at the closed term fourteen fields of K6DueMg hold (Law/K6DueSplit.lean: K6PaidMg):
      hid, head, wt, lay, uH, blind BY DEFINITION (rfl) · sorts by mH_is · laid, place:
      fields of its head · seg: a theorem in the goals' scope · ns, treesB, roomC:
      Law/K6BuiltAtConst.lean · readers: by the make of the runs' readers, where Lk is segment 24 of
      the head's own letter for the first chain (LaidAt.linkAt, Johnson/P5J/ChainFree.lean).
  back_at_const: under the promise the public part's bytes spell a request: the promise's own clause
      "in order".
  reqW_at_const, rqX_at_const: then the words of the request, and the caller's request, are those of
      the request that the hidden values read (other files' backReq_words, requestOf_words).
  K6Cond: THE ONE CONDITION · cond_of_fold: its two fields on fold facts from AtMgR
      (Johnson/P5J/AtMgR.lean) · k06_at_const: THE STATEMENT. `AtMgR` is declared in Johnson/P5J/AtMgR.lean, and cond_of_fold in this file (line 150) takes it as the type of its premise hF.

THE ONE CONDITION, K6Cond h Fr piece6 Lk Rch Lp Mm l: FIVE FIELDS: fold, reqIs (six of AtMgR's
facts on every reached state, at border 341 alone) · link (cF.links[24]? = some Lk) · state
(K6StateMg: nine fields on reached states and on that segment) · piece (the piece at number 341 of l
is seated: Seated, Johnson/Desc/Sound/K6Tied.lean; with K6RowMg: three fields, and K6LeftMg: nine:
Law/K6DueSplit.lean). PAID HERE, OF THE TEN THAT STAND BESIDE K6DueMg: hMore, hMg, hPubH, hreq (by
definition) · hPP (another file's pubP_open342_mgBase) · hput (another file's putReq_keeps) · hreqW,
hrqX (from the promise). K6Cond HOLDS NONE OF THE CONCLUSION: no field speaks of TiedAtR, of a
relation or of an extractor's output; of errors only cap.
THE LETTERS piece6, Lk, Lp, Mm stand in front of K6Cond and in it alone: a wrong choice makes the
condition false, not the statement empty. Lk is pinned by link; piece6 by runs3 and back3
(Law/K06AtHead.lean: 4); Lp, Mm by fold and seatsC (cond_of_fold: the laid list of
AtMgR, Johnson/P5J/AtMgR.lean; the closed list of the messages' shapes).
Seated stands for Object61 (the law spends no more).

What it does not say. The join's own forms: Law/K06Kind.lean, Law/K06AtHead.lean, and
Johnson/Goal/Skeleton/Kinds/K6Bridge.lean, which calls k06_at_const at its folder's own "reached".
THAT AtMgA OR K6Cond CAN BE MET: NO EXAMPLE. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6DueSplit
import Johnson.Desc.Kinds.Law.K6BuiltAtConst
import Johnson.P5J.ChainFree
import Johnson.Desc.Kinds.Law.K6RestOfFold
import Johnson.P5J.AtMgR
import Johnson.Meaning.ReqBytesBack
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Piece Frame MsgT onQ extQAt linksFull KindTiedR mgAll mgBase)
open P5J (AtMgA mgAtAll At.layout At.num At.reqB At.reqW At.d₀ At.decT At.EAt At.tabH At.X tokVOf
  tokHOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA o Z Dw r Zp Np cF x)

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- **At the closed term fourteen fields hold**, one of them where Lk is the chain's segment 24. -/
theorem paid_at_const (Lk : Link S Claim) (hlk : cF.links[24]? = some Lk) :
    K6PaidMg (dAt h) (At.layout Zp) (At.num Zp) tokVOf
      (fun a => (Meaning.backReq (At.reqB a.1)).getD At.d₀)
      (fun a y => At.decT o Zp Np cF (At.EAt Z) h.plan.shape y.cell a) h.plan.hN h.plan.hG
      (At.tabH x) tokHOf Lk K9.smallReader x :=
  have hseg : VerifiableInference.OnPublicFiles.headLink (At.X Zp) = 24 := by
    obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
    unfold VerifiableInference.OnPublicFiles.headLink
    rw [p4, ng]
    rfl
  { seg := hseg
    readers := by
      show K9.readersAt (dAt h).lk (At.X Zp) (VerifiableInference.OnPublicFiles.headLink (At.X Zp)) 24 = _
      have hlk' : (dAt h).lk 24 = some Lk := (h.laid.linkAt 24).trans hlk
      rw [K9.readersAt_some _ _ _ _ _ hlk', hseg]
      rfl
    sorts := P5J.At.mH_is.1
    hid := rfl
    head := rfl
    wt := rfl
    laid := h.plan.laid
    place := h.headAt
    lay := rfl
    uH := rfl
    blind := ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    ns := ns_at_const h
    treesB := trees_at_const h
    roomC := room_at_const h }

/-- **The words of the request, where the public part's bytes spell a request.** -/
theorem reqW_at_const (a : ProofFile.InstPub × S) (hb : (Meaning.backReq a.1.request).isSome = true) :
    At.reqW a.1 = OnBytes.Flat.requestWordsOf ((dAt h).H.req a).val := by
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hb
  show OnBytes.Model.Verify.words32 a.1.request =
    OnBytes.Flat.requestWordsOf ((Meaning.backReq a.1.request).getD At.d₀).val
  rw [hR]
  exact Meaning.backReq_words hR

/-- **The caller's request is the hidden values'**, where the public part's bytes spell a request.
-/
theorem rqX_at_const (a : ProofFile.InstPub × S) (hb : (Meaning.backReq a.1.request).isSome = true) :
    (dAt h).rq a.1 = reqX ((dAt h).H.req a).val :=
  Came.requestOf_words _ _ (reqW_at_const h a hb)

section
variable (Fr : Frame) (piece6 : ℕ) (Lk : Link S Claim)
  (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop) (Lp : K12.Door.Laid) (Mm : List OracleShape)
  (l : List (Piece (_root_.Run.ckP .two) Fr (ProofFile.InstPub × S) Claim
    (Wit (Fin numsFull.rows → Fin (P5J.colsAt numsFull) → GE) P5J.At.Tok MsgT)))

/-- **THE ONE CONDITION FOR THIS KIND OF STEP, AT THE CLOSED TERM.** -/
structure K6Cond : Prop where
  /-- five fold facts at border 341 (FoldAt) -/
  fold : ∀ a, Rch 341 a → a.1.2.failed = none →
    AtFold.FoldAt Lp Mm (dAt h).cs (dAt h).shape (At.layout Zp) a.1.2
  /-- a sixth: the state's words of the request are the public part's -/
  reqIs : ∀ a, Rch 341 a → a.1.2.failed = none → a.1.2.req = At.reqW a.1.1
  /-- Lk is segment 24 of the head's own letter for the first chain -/
  link : cF.links[24]? = some Lk
  /-- nine fields on reached states and on that segment (Law/K6DueSplit.lean: K6StateMg) -/
  state : K6StateMg (dAt h) mgBase Fr piece6 Lk Rch
  /-- the piece at number 341 is seated (Seated), and meets what is left of the
      structure of premises (Law/K6DueSplit.lean: K6RowMg: three fields; K6LeftMg: nine) -/
  piece : ∀ q, l[341]? = some q → ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim)
    (numD : Fmt.TreeSource → Nat) (bs : List (Block (ProofFile.InstPub × S) Claim)),
      Seated (At.X Zp) .two Fr q 24 bef B bS ∧
      K6RowMg Fr numD bs q ∧
      K6LeftMg (dAt h) mgBase (At.layout Zp) (At.num Zp) Fr x Rch Lp Mm bs

/-- **The two fields on fold facts, from the head with the facts on every reached
state** (Johnson/P5J/AtMgR.lean), at its own closed numbers
(Johnson/P5J/FoldAt.lean):
so that the join holds them once; the list of the messages' shapes is a closed term there. -/
theorem cond_of_fold (hF : P5J.AtMgR o Z Dw r Zp Np cF Rch (fun a => a.1) Lp)
    (hlink : cF.links[24]? = some Lk) (hstate : K6StateMg (dAt h) mgBase Fr piece6 Lk Rch)
    (hpiece : ∀ q, l[341]? = some q → ∃ (bef : List (ℕ × ℕ)) (bS B : Block S Claim)
      (numD : Fmt.TreeSource → Nat) (bs : List (Block (ProofFile.InstPub × S) Claim)),
        Seated (At.X Zp) .two Fr q 24 bef B bS ∧
        K6RowMg Fr numD bs q ∧
        K6LeftMg (dAt h) mgBase (At.layout Zp) (At.num Zp) Fr x Rch Lp
          (K12.Door.msgsOfChain Zp.made.proof.1) bs) :
    K6Cond h Fr piece6 Lk Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1) l :=
  { fold := fun a hr hm => AtFold.foldAt_of_facts (dAt h) (At.layout Zp) Fr Rch
      (P5J.At.foldD Zp cF Lp) At.reqW hF.fold rfl rfl 341 a hr hm
    reqIs := fun a hr hm => hF.fold.reqIs 341 a hr hm
    link := hlink
    state := hstate
    piece := hpiece }

/-- **Under the promise the public part's bytes spell a request**: it is the promise's own clause
"in order" at the closed term. -/
theorem back_at_const (k : ℕ) (a : (ProofFile.InstPub × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) (dAt h).N (mgAtAll h) linksFull PS (fun a => a) k a)
    (hm : a.1.2.failed = none) : (Meaning.backReq a.1.1.request).isSome = true :=
  (Sound.onParts_of_on (dAt h).N (mgAtAll h) linksFull PS (fun a => a) k a ha hm).order

/-- **THE STATEMENT.** -/
theorem k06_at_const (c₀ : Fin numsFull.rows → Fin (P5J.colsAt numsFull) → GE)
    (tokOf : ProofFile.InstPub × S → P5J.At.Tok)
    (C : K6Cond h Fr piece6 Lk Rch Lp Mm l) :
    KindTiedR (dAt h).N (mgAtAll h) linksFull PS Rch
      (fun i => extQAt (dAt h).cs (dAt h).G (dAt h).arr (dAt h).smp (dAt h).ms (dAt h).decT c₀ tokOf
          (dAt h).N linksFull PS
        (fun a => a) i) l .K6 :=
  kindTied_K6_mgAll (dAt h) mgBase c₀ (At.layout Zp) (At.num Zp) tokVOf
    (fun a => (Meaning.backReq (At.reqB a.1)).getD At.d₀)
    (fun a y => At.decT o Zp Np cF (At.EAt Z) h.plan.shape y.cell a) h.plan.hN h.plan.hG
    (At.tabH x) tokHOf Fr tokOf piece6 Lk K9.smallReader x Rch Lp Mm h.scope h.reads h.pubOne l
        rfl
    (pubP_open342_mgBase (dAt h)) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) At.reqW C.fold C.reqIs
    (fun a ha hr hm => reqW_at_const h a.1 (back_at_const h Fr 341 a ha hm)) Came.putReq_keeps
    (fun a ha hr hm => rqX_at_const h a.1 (back_at_const h Fr 341 a ha hm))
    (fun q hq => by
      obtain ⟨bef, bS, B, numD, bs, Hs, Rw, L⟩ := C.piece q hq
      exact ⟨bef, bS, B, numD, bs, Hs, due_of_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bS numD
        bs q (paid_at_const h Lk C.link) Rw C.state L⟩)

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.paid_at_const
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.reqW_at_const
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.rqX_at_const
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.back_at_const
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_of_fold
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_at_const
