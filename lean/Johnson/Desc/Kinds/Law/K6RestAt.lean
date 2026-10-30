-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6RestAt.lean: WHAT THE LAW OF THE OUTPUT HEAD'S OWN ROUNDS ASKS OF THE
VERIFIER'S STATE BEHIND AN ACCEPT OF THESE ROUNDS (Law/K6RecordAt.lean: RecordRest, seven clauses;
MatsSeated at the planes' matrix), AT THE COMPOSED MEANING mgAll D Mg, FROM: the table's
promise in front; five facts on the state in front (FoldAt); one test with code on public parameters
(Law/K6SeatsTest.lean: seatsK6C); one equation on a parameter of the composed meaning. Statements
and proofs.

How. An accept of these rounds turns three fields of the head's part of the state and nothing else
(another author's k6_behind): so the open segment's frame, layout and list of arrays, the statement
and the book behind are those in front. In front, the promise itself says four things
(Law/K6FrontSays.lean). With the five facts every reader through which RecordRest reads the state is
a term off the public parameters (StateIsPlan), and the test's accept gives the clauses.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold).
  FoldAt Lp M cs shape lay s   the five facts at a state s: the book's places are the first of the
      listed seats; the statement's messages' shapes are the first of the listed shapes; the codes,
      the shape and the layout of the copy in use are the public ones.
  segAt_parts          where a segment is open with a ledger and a tail, the open segment's part is
      there, with these. link_of_seg: the open segment's part holds the open link.
  arrays_of_fresh      another author's public test linkFreshB arrs, at a state with an open
      segment's part aK: aK.L.arrayOf = arrs.
  stateIsPlan_behind   StateIsPlan at the state behind an accept.
  **recordRest_behind**  RecordRest behind an accept.
  **matsB_behind**     MatsSeated at the planes' matrix, at THE open segment's part behind an
      accept.

Every letter under "there is". aK: pinned by K9.segAt? at the state behind (RecordRest's first
clause); cU: by the open segment's list of arrays at the number of the reads' array (its fifth).
What it does not say. That the test accepts: no theorem (one evaluation: see its file). FoldAt at
any state. The equation huH: the parameter uH of the composed meaning is open. That any statement is
inside the promise. The full chain alone. Nothing on soundness. 
-/
import Johnson.Desc.Kinds.Law.K6SeatsTest
import Johnson.Desc.Kinds.Law.K6FrontSays
import Johnson.Desc.Kinds.Law.K6LedgerAt
import Johnson.Desc.Kinds.Law.HeadPlanesNu
import Johnson.Desc.First.Look.K3KeepsFree
import Johnson.Desc.Sound.StatedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open OnBytes.Model (Fork LinkCtx HTailF2)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning pubFit)
open VerifiableInference.Desc.Sound (Piece Frame MsgT onQ linksFull MgData mgAll)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable

/-- **The five facts on the state in front.** -/
structure FoldAt (Lp : K12.Door.Laid) (M : List OracleShape) (cs : Codes) (shape : ReqShape)
    (lay : ReqLayout) (s : S) : Prop where
  seats : K12.Door.atFirstSeats Lp s = true
  msgs : K12.Door.atFirstShapes M s = true
  codes : s.st.codes = cs
  shape : s.live.frame.shape = shape
  layout : s.live.rows.layout = lay

/-- Where a segment is open with a ledger and a tail, the open segment's part is there. -/
theorem segAt_parts (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) (h1 : s.link? = some L)
    (h2 : s.fork? = some F) (h3 : s.tl? = some tl) :
    ∃ aK, K9.segAt? s = some aK ∧ aK.L = L ∧ aK.d.st = s.st ∧ aK.d.book = s.book := by
  refine ⟨{ owed := K9.owedOf s, used := (K9.usedOf s).getD 0, laid := K9.laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } },
    ?_, rfl, rfl, rfl⟩
  unfold K9.segAt?
  rw [h1, h2, h3]
  rfl

/-- The open segment's part holds the open link. -/
theorem link_of_seg {s : S} {aK : K9.Part} (h : K9.segAt? s = some aK) : s.link? = some aK.L := by
  unfold K9.segAt? at h
  cases hL : s.link? with
  | none =>
    rw [hL] at h
    cases h
  | some L =>
    cases hF : s.fork? with
    | none =>
      rw [hL, hF] at h
      cases h
    | some F0 =>
      cases hT : s.tl? with
      | none =>
        rw [hL, hF, hT] at h
        cases h
      | some t0 =>
        rw [hL, hF, hT] at h
        rw [← Option.some.inj h]

/-- **Another author's public test linkFreshB gives the open segment's list of arrays.** -/
theorem arrays_of_fresh {arrs : Array (ℕ × String)} {s : S} {aK : K9.Part}
    (h : VerifiableInference.OnPublicFiles.linkFreshB arrs s = true) (hK : K9.segAt? s = some aK) :
    aK.L.arrayOf = arrs := by
  unfold VerifiableInference.OnPublicFiles.linkFreshB at h
  rw [Bool.and_eq_true, link_of_seg hK] at h
  exact eq_of_beq h.2

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
  (Fr : Frame) (Lp : K12.Door.Laid) (M : List OracleShape)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

variable {bef : List (ℕ × ℕ)} {B bS : Block S Claim}
  {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}

/-- **Behind an accept every reader is a term off the public parameters.** -/
theorem stateIsPlan_behind (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hfit : pubFit (MGA).more linksFull PS = true) (hp : PS[341]? = some placeK6)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b) (F : FoldAt Lp M D.cs D.shape lay6 a.1.2) :
    ∃ aK, StateIsPlan lay6 D.cs D.shape D.pubD.dS Lp M (D.sent.arrayOf.getD 24 #[])
      (D.N.msgsAt PS[341]?) b.1.2 aK ∧ ∃ o : First.HeadOwn, b.1.2.here = .head o := by
  obtain ⟨o, F1, X, Q, ho, hop, _, e⟩ := k6_behind Hs a b τ hb
  have e2 : b.1.2 =
      { a.1.2 with here := .head { o with F := F1, x := some X, squaresP := some Q } } :=
    congrArg Prod.snd e
  have hLa : a.1.2.link? = some o.L := by
    unfold First.S.link?
    rw [ho]
    show (if o.opened = true then some o.L else none) = _
    rw [if_pos hop]
  have hLb : b.1.2.link? = some o.L := by
    rw [e2]
    show (if o.opened = true then some o.L else none) = _
    rw [if_pos hop]
  have hFb : b.1.2.fork? = some F1 := by
    rw [e2]
    show (if o.opened = true then some F1 else none) = _
    rw [if_pos hop]
  have hTb : b.1.2.tl? = some o.tl := by
    rw [e2]
    show (if o.opened = true then some o.tl else none) = _
    rw [if_pos hop]
  have hst : b.1.2.st = a.1.2.st := by rw [e2]
  have hbk : b.1.2.book = a.1.2.book := by rw [e2]
  have hlive : a.1.2.live = o.L.check := by
    unfold First.S.live
    rw [hLa]
  obtain ⟨aK, k1, k2, k3, k4⟩ := segAt_parts b.1.2 o.L F1 o.tl hLb hFb hTb
  have hS := sentIs_front D Mg Fr hfit hp a ha hm
  have hfr := fresh_front D Mg Fr hfit hp a ha hm
  have hbo := book_front D Mg Fr a ha hm
  unfold VerifiableInference.OnPublicFiles.linkFreshB at hfr
  rw [Bool.and_eq_true, hLa] at hfr
  have harr : o.L.arrayOf = D.sent.arrayOf.getD 24 #[] := eq_of_beq hfr.2
  unfold First.bookAt at hbo
  simp only [Bool.and_eq_true, beq_iff_eq] at hbo
  refine ⟨aK, ⟨k1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, _, by rw [e2]⟩
  · intro born message
    rw [k2]
    exact First.FillSent.whereIs_of_sentIs hLa hS born message
  · rw [k2]
    exact First.FillSent.link_of_sentIs hLa hS
  · rw [k2, ← hlive]
    exact F.shape
  · rw [k2, ← hlive]
    exact F.layout
  · rw [k2]
    exact harr
  · rw [k3, hst]
    exact F.codes
  · rw [k3, hst]
    exact F.msgs
  · rw [k4, hbk]
    exact F.seats
  · rw [k4, hbk, hbo.1.2, hbo.2]
  · rw [k3, hst, hbo.2]

/-- **MatsSeated at the planes' matrix, at the open segment's part behind an accept.** -/
theorem matsB_behind (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hfit : pubFit (MGA).more linksFull PS = true) (hp : PS[341]? = some placeK6)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b) (F : FoldAt Lp M D.cs D.shape lay6 a.1.2)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    (aK : K9.Part) (hK : K9.segAt? b.1.2 = some aK) :
    MatsSeated (colsB Wp) D.arr D.N Wp (D.N.sent 24 0) aK num lay6 := by
  obtain ⟨aK', I, _⟩ := stateIsPlan_behind D Mg lay6 Fr Lp M Hs hfit hp a b τ ha hm hb F
  obtain rfl : aK' = aK := Option.some.inj (I.seg.symm.trans hK)
  exact matsSeated_of_C hC I _ fun x _ hx => by
    have e : x = Wp.hS.NHf + 2 := hx
    omega

/-- **RecordRest behind an accept.** -/
theorem recordRest_behind (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hfit : pubFit (MGA).more linksFull PS = true) (hp : PS[341]? = some placeK6)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b) (F : FoldAt Lp M D.cs D.shape lay6 a.1.2)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    (huH : D.uH 24 = uHeadK6 Wp 24) :
    ∃ aK cU, RecordRest D.arr D.N Wp lay6 num (num 24 0) 0 (p8K6 Wp 24) D.St b.1.2 aK cU := by
  obtain ⟨aK, I, o', ho'⟩ := stateIsPlan_behind D Mg lay6 Fr Lp M Hs hfit hp a b τ ha hm hb F
  obtain ⟨cU, c1, c2⟩ := reads_of_C hC I
  refine ⟨aK, cU, I.seg, I.layout, matsSeated_of_C hC I _ ?_, maskSeated_of_C hC I, c1, ?_, ?_⟩
  · intro x c hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  · have hno : Sound.linkNo b.1.2 = 24 := by
      unfold Sound.linkNo
      rw [link_of_seg I.seg]
      exact I.link
    have h1 := Sound.stated_head D.uL D.uA D.uH b.1.2 o' ho'
    rw [hno, huH] at h1
    exact statedAt_of_is Wp 24 D.St b.1.2 cU h1 c2
  · intro gk hg
    obtain ⟨p, _, ⟨h, _, L⟩, _⟩ := left_front D Mg Fr hfit hp a ha hm
    obtain ⟨_, g, _, hg', he, _⟩ := VerifiableInference.OnPublicFiles.leftAt_cEnd _ _ _ _ _ _ _ L
    rw [lookHeard_behind Hs a b τ hb] at hg
    obtain rfl : g = gk := Option.some.inj (hg'.symm.trans hg)
    exact he

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.stateIsPlan_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.matsB_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.recordRest_behind
