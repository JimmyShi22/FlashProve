-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HeadSentence.lean: THE OUTPUT HEAD's
"SENTENCE ON THE RUN" AS A THEOREM, UNDER ONE SENTENCE ON THE LOOKUP's PART: AT THE THREAD UNDER THE
LIBRARY's HEAD, BEHIND THE ACCEPTED STEP OF THE READS' MEMBER OF THE HEAD's SEGMENT (number 342 of
the first chain's flat list): THE LIST OF TABLES IN THE SMALLNESS TEST's RECORD IS THE LIST THAT THE
MAKER OF THE HEAD's TABLES RETURNS AT WHAT THE FILLER MAKES OF THE CHALLENGES HEARD. Three
statements and their proofs. No definition. A rider rides with it: "an
implication: no member: that the thread stands in front of that member at any run is shown by
nobody".

  tables_whole  at one list of the sub-protocol's own challenges the maker gives one answer,
                whatever the request and the token, at two lookups' data that agree in five fields
  head_sentence the sentence, with four letters (N, base, g₂, q) for the filler's terms
  head_clause   the last clause of HeadPlanS (TieReadsHeadAtS.lean in this folder) in its own
                spelling, at lettersHead and b = 342

THE ROAD, SEVEN LINKS. (1) From the thread's clause Made at 342 to ONE state in front of member 341,
reached, at which that member's step says yes on rounds whose challenges are its own slice of what
was heard: made_member_reach (Johnson/Desc/ProofFile/Honest/Thread/MemberFrom.lean). (2) The fold
behind it runs over the empty list: the state behind 341 is the stand's: foldBlocks_nil. (3) The
ledger in front is well laid: P4.wellLaid_341 (Johnson/P4R/FreeAt341N.lean). (4) What the member's
yes leaves, and that the maker reads of it what headHeardWhole has: tables_at_accept
(Johnson/Desc/ProofFile/Honest/K6/HeardAtYes.lean), at the member that P4.k6_member_at_mg
(Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean) finds. (5) Through the reads' member: head_record
(HeadRecord.lean in this folder); commitAtS_here, commitAtS_slots, commit_head (Johnson/Desc/K1/):
the sending turns the link and the ledger alone. (6) The spelling: the filler's cut of what was
heard is the member's slice. (7) One answer: tables_whole; tables_at_stand (ReqAtStand.lean in this
folder) for the covered positions.

THE PREMISES, BY KIND. THE HEAD: h : P5J.AtMgA: A HYPOTHESIS. THE THREAD's OWN: hT (Thr at 342), hS
(the member's accepted step), htl (the record is there). PUBLIC, ON PLANS AND NUMBERS, ASKED, NONE
EVALUATED AT THE HEAD: hGW (the filler's ground has the head's public part), hquiet (which block the
quiet half is: a payer lies: k1Quiet_head, Johnson/Desc/K8/Honest/ReadsSeat.lean, from G.built[24]?
= some X and X.kind = 2; not called), hTT, hVV (the head's shape has the filler's T and V), hU (the
member's form), hb, hbase (K6's place in the filler's cuts is the number of rounds in front of
member 341), hlen (the filler's count of K6's rounds is the member's: for one half a payer lies:
front_eight, Johnson/Desc/ProofFile/Honest/K6/Law/HidesAtRow.lean; not called), hcut (the filler's
cut reaches behind K6's rounds). THE MAKER's TWO RETURNS: hx, ht: the clause's own. ON THE LETTER
wit, IN head_clause ALONE: hwit: at the run's input wit hands the input's own instance on: HeadPlanS
has wit a free letter: so head_clause pays the clause at those wit alone that keep the instance;
nobody is named that meets it. sg AND A ARE FREE LETTERS THERE: meant at sg = 24: elsewhere hbase
can hardly hold, and the clause is paid at nothing. ON THE RUN: ONE: hLook: ON THE VERIFIER's STATE
AND WHAT WAS HEARD: the state's copy of what the lookup on the head's calls left agrees with the
filler's k4LookOf in zx, zk, zb0, zb1 and shape. It names no witness, no Script's field, no input
and no coin. Of the input the instance's public request alone is read (in covOf); the run's coins
stand as a bound letter, handed on whole to the thread's stand and step.

KIN. No file of the seal or of laws.12's closed list joins made_member with tables_at_accept (sought
by name and by the end ".funs = ... .funs": 100 lines in 66 files, none on the honest side). NEAR:
HeadListAt343 (Johnson/P1K8R/HeadListAtBatchStatement.lean): at every state reached at 343 there are
x and t such that the record has t's list; its head: "THAT IT IS WHAT THE HEAD's OWN SUB-PROTOCOL
LAID OF ITS CHALLENGES AT 341 IS NOT SAID HERE": that is said here. FOR hLook: head_calls_tie
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadCallsTie.lean): behind member 340 the returned
structure agrees with lookHeardAt's text in eleven fields; not called here: from 340 to the stand at
342, and lookHeardAt against k4LookOf, are not looked at.

NO NEGATIVE TEST. lettersHead is without code: no test with code reaches the thread
(Johnson/Desc/ProofFile/Honest/Thread/ReachFacts.lean's own Limits). Of head_sentence's fifteen
premises fourteen are called by name in its proof; hcut is spent by an omega.

Limits. AT lettersHead ALONE, at the class Claim: no letter L. ONE SEGMENT OF 25. IT PAYS ONE CLAUSE
OF HeadPlanS: the clauses on the book, the part, the layout and the makers' returns stay. IT
EXCHANGES THAT CLAUSE FOR hLook, WHICH IS NOT PAID HERE (see `head_look`, HeadLook.lean). It stands
over MemberFrom.lean, another house's file that is on no row, and over files of ours that are in no
seal. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.HeadRecord
import Johnson.Desc.ProofFile.Honest.K1.Law.ReqAtStand
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.Thread.MemberFrom
import Johnson.Desc.ProofFile.Honest.K6.HeardAtYes
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.P4R.FreeAt341N
import Johnson.Desc.K1.Law.LaterAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.K8.ReadsQuiet (head)
open VerifiableInference.Desc.Kinds (Head.Par Head.Request)
open VerifiableInference.Desc.Kinds.Head (requestOf)
open VerifiableInference.Desc.Kinds.Head.Law (p8K6 readsOf K6MemberIs)
open VerifiableInference.Desc.K1 (commitAtS_here commitAtS_slots commit_head)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace.U3 (covOf u3Seats placeIn)
open ProofFile.Honest.K4 (k4LookOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K6 (headHeardWhole headHeardWholeAt headHearingOf headParAt headInFront
  tables_nine tables_heardOf tables_at_accept)
open ProofFile.Honest.FirstThread (Script lettersHead WtF tables_at_stand)

/-! ## 1 The maker of the head's tables at two hearings of one list -/

/-- **AT ONE LIST OF THE SUB-PROTOCOL's OWN CHALLENGES THE MAKER OF THE HEAD's TABLES GIVES ONE
ANSWER, WHATEVER THE REQUEST AND THE TOKEN**, at two lookups' data that agree in five fields. Two
calls: tables_heardOf, tables_nine (Johnson/Desc/ProofFile/Honest/K6/HeardWhole.lean). -/
theorem tables_whole (hS : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (p : Head.Par) (q q' : Head.Request) (y y' : ℕ) {g g' : Forest.Heard} (own : List Fmt.Drawn)
    (k0 : g.zx = g'.zx) (k1 : g.zk = g'.zk) (k2 : g.zb0 = g'.zb0) (k3 : g.zb1 = g'.zb1)
    (k4 : g.shape = g'.shape) :
    ReadsQuiet.tables hS L hp cov (headHeardWhole p q y g own) =
      ReadsQuiet.tables hS L hp cov (headHeardWhole p q' y' g' own) := by
  have s1 : ReadsQuiet.tables hS L hp cov (headHeardWhole p q y g own) =
      ReadsQuiet.tables hS L hp cov (headHeardWhole p q y g' own) := by
    letI := p.sizes
    letI := q
    letI : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
    exact tables_heardOf hS L hp cov g g' (headHearingOf p own) (headHearingOf p own) rfl rfl rfl
      rfl rfl k0 k1 k2 k3 k4
  exact s1.trans (tables_nine hS L hp cov rfl rfl rfl rfl rfl rfl rfl rfl rfl)

/-! ## 2 The sentence -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE HEAD's SENTENCE ON THE RUN, UNDER ONE SENTENCE ON THE LOOKUP's PART.** At lettersHead's
thread, at the stand in front of member 342 (the reads of the head's segment) and behind that
member's accepted step: the record's list of tables IS the list that the maker of the head's tables
returns at what headHeardWholeAt makes of the challenges heard, at the filler's covered positions.
hLook: THE ONE PREMISE ON THE RUN: the state's copy g₁ of what the lookup on the head's calls left
agrees with the letter g₂ in five fields. N, base, g₂, q are letters: head_clause has them at the
filler's own terms. -/
theorem head_sentence (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Zq : ProofFile.Pub} {G : ProofFile.Ground} {Xl : LinkH} {pr : ℕ} {reads : Option (List ℕ)}
    (hGW : G.W = P5J.At.X Zp) (hquiet : IM.k1Quiet G 24 Xl = head (p8K6 G.W 24))
    (hTT : G.W.hS.T = G.W.T) (hVV : G.W.hS.V = G.W.P.h.V)
    {blk : Block TS ProofFile.Cl}
    (hU : blk.UnderR ((IM.k1Reads Zq G 24 Xl pr reads).retype : Block TS ProofFile.Cl))
    (hb : 342 ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 342 k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s')
    {tl : HTailF2} (htl : s'.tl? = some tl) {N base : ℕ}
    (hbase : base =
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front + roundsTo cF.blocksInOrder 341)
    (hlen : ∀ b₆, cF.blocksInOrder[341]? = some b₆ → headInFront (headParAt G) 8 = b₆.rounds.length)
    (hcut : base + headInFront (headParAt G) 8 ≤ N) {g₂ : Forest.Heard}
    (hLook : ∀ o g₁, s.here = .head o → o.lookHeard = some g₁ →
      g₁.zx = g₂.zx ∧ g₁.zk = g₂.zk ∧ g₁.zb0 = g₂.zb0 ∧ g₁.zb1 = g₂.zb1 ∧ g₁.shape = g₂.shape)
    {q : Head.Request} {xm : Head.Heard} {t : Head.Tables}
    (hx : headHeardWholeAt (headParAt G) q 0 g₂ base (m.st.heard.take N) = .ok xm)
    (ht : ReadsQuiet.tables G.W.hS G.W.HLy G.W.H
      ((covOf Zq G m.st.input.x).toOption.getD default) xm = .ok t) :
    tl.funs = t.funs := by
  -- (1) K6's member, and the one state in front of it
  obtain ⟨b₆, hb₆, M₀⟩ := P4.k6_member_at_mg h.toAtMg
  have M : K6MemberIs G.W 24 ProofFile.sameReply IM.k6Place b₆ := by
    rw [hGW]
    exact M₀
  have hM : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Made 342 k s m E := by
    have hT' := hT
    unfold Thr at hT'
    exact hT'.2.2.2.2.1
  obtain ⟨sj, sj', rs, c, n, rs', c', hR, hst, hdr, hfold⟩ :=
    made_member_reach (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ProofFile.startS Zp) m.st.input.x.pub (b := 342) (j := 341) (by omega) hb hb₆ (fun _ h0 => h0) hM
  -- (2) the fold behind it is empty
  have hnil : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.take 342).drop
      (341 + 1) = [] := List.drop_eq_nil_of_le (by rw [List.length_take]; omega)
  rw [hnil] at hfold
  obtain rfl : s = sj' := congrArg Prod.fst (foldBlocks_nil _ _ _ _ _ hfold)
  -- (3) the ledger in front is well laid
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hWL := P4.wellLaid_341 h.scope h.reads O
    (fun b hb' => P5J.flat_ok h.toAtMg b (List.mem_of_getElem? hb')) hR G.W.hS
    (VerifiableInference.Desc.Kinds.Head.Law.readsOf G.W)
  -- (4) what the member's yes leaves
  obtain ⟨o, x₀, g₁, yk, hso, hox, hol, -, -, -, -, -, -, htab⟩ := tables_at_accept M hst hWL
  -- (5) through the reads' member
  obtain ⟨r₁, r₂, gs, gs₁, rs₂, gs₂, s₁, a, cov, x₁, t₁, -, h1, -, ha, hcov, hx₁, ht₁, -, -,
    hfun⟩ := head_record hquiet hU hS htl
  obtain ⟨-, -, hh⟩ := commitAtS_here _ _ _ _ s s₁ _ _ h1
  have hop : o.opened = true := by
    rcases hh with ⟨a', _, e, _⟩ | ⟨a', _, e, _⟩ | ⟨a', _, e, _, e2, _⟩
    · rw [hso] at e
      cases e
    · rw [hso] at e
      cases e
    · rw [hso] at e
      cases e
      exact e2
  obtain ⟨_, _, _, yy, _, _, _, e1, _⟩ := commitAtS_slots h1
  have hs₁ := e1.trans (commit_head hso hop _ _ _)
  rw [hs₁] at ha hcov
  have hax : a.x = o.x := by
    cases ha
    rfl
  have hxx : x₁ = x₀ := by
    rw [hax, hox] at hx₁
    exact (Option.some.inj hx₁).symm
  subst hxx
  have hcs : s.covered G.W.T G.W.P.h.V = .ok cov := by
    rw [← hTT, ← hVV]
    exact hcov
  -- (6) the spelling
  have hxm : xm = headHeardWhole (headParAt G) q 0 g₂
      (((m.st.heard.take N).drop base).take (headInFront (headParAt G) 8)) := by
    unfold headHeardWholeAt at hx
    dsimp only at hx
    split at hx
    · exact (Except.ok.inj hx).symm
    · cases hx
  have hown : ((m.st.heard.take N).drop base).take (headInFront (headParAt G) 8) =
      rs.map (·.drawn) := by
    rw [hdr, List.drop_take, List.take_take, Nat.min_eq_left (by omega), hbase, hlen b₆ hb₆]
    rfl
  -- (7) one answer
  obtain ⟨k0, k1, k2, k3, k4⟩ := hLook o g₁ hso hol
  have E1 : ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x₁ =
      ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov xm := by
    rw [htab, hxm, hown]
    exact tables_whole _ _ _ _ (headParAt G) _ q _ 0 _ k0 k1 k2 k3 k4
  have E2 := tables_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT Zq G hcs G.W.hS
    G.W.HLy G.W.H xm
  have E3 : (Except.ok t₁ : Except String Head.Tables) = .ok t :=
    ht₁.symm.trans (E1.trans (E2.symm.trans ht))
  rw [hfun, Except.ok.inj E3]

/-- **THE LAST CLAUSE OF HeadPlanS (K1/Law/TieReadsHeadAtS.lean), IN ITS OWN SPELLING**, at
lettersHead and b = 342. hLook: the same premise at the filler's own term k4LookOf. hwit: wit hands
the input's own instance on: a rider, in marks: "on the letter wit: the
public instance alone; by unfolding at K1's reader as the fillings lay it". sg is meant as 24. -/
theorem head_clause (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Zq : ProofFile.Pub} {G : ProofFile.Ground} {Xl : LinkH} {pr : ℕ} {reads : Option (List ℕ)}
    (hGW : G.W = P5J.At.X Zp) (hquiet : IM.k1Quiet G 24 Xl = head (p8K6 G.W 24))
    (hTT : G.W.hS.T = G.W.T) (hVV : G.W.hS.V = G.W.P.h.V)
    {blk : Block TS ProofFile.Cl}
    (hU : blk.UnderR ((IM.k1Reads Zq G 24 Xl pr reads).retype : Block TS ProofFile.Cl))
    (hb : 342 ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 342 k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s')
    {tl : HTailF2} (htl : s'.tl? = some tl)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst)
    (hwit : (wit m.st.input).x = m.st.input.x) {sg : ℕ} {A : MsgAddr}
    (hbase : ∀ (sps : List Spot) (k6 : Spot × ℕ), spotsOf Zq.cuts = some sps →
      placeIn Zq sps sg .K6 = .ok k6 → k6.2 =
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
          roundsTo cF.blocksInOrder 341)
    (hlen : ∀ b₆, cF.blocksInOrder[341]? = some b₆ → headInFront (headParAt G) 8 = b₆.rounds.length)
    (hcut : ∀ (sps : List Spot) (k6 : Spot × ℕ), spotsOf Zq.cuts = some sps →
      placeIn Zq sps sg .K6 = .ok k6 →
      k6.2 + headInFront (headParAt G) 8 ≤ OnBytes.HonestTrace.heardOf (u3Seats Zq G) A)
    (hLook : ∀ (sps : List Spot) (k3 : Spot × ℕ), spotsOf Zq.cuts = some sps →
      placeIn Zq sps sg .K3 = .ok k3 → ∀ o g₁, s.here = .head o → o.lookHeard = some g₁ →
      g₁.zx = (k4LookOf G.W.HLy.fs k3.2
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A))).zx ∧
        g₁.zk = (k4LookOf G.W.HLy.fs k3.2
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A))).zk ∧
        g₁.zb0 = (k4LookOf G.W.HLy.fs k3.2
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A))).zb0 ∧
        g₁.zb1 = (k4LookOf G.W.HLy.fs k3.2
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A))).zb1 ∧
        g₁.shape = (k4LookOf G.W.HLy.fs k3.2
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A))).shape) :
    ∀ (sps : List Spot) (k6 k3 : Spot × ℕ) (x : OnBytes.Model.Head.Heard)
      (t : OnBytes.Model.Head.Tables), spotsOf Zq.cuts = some sps →
      placeIn Zq sps sg .K6 = .ok k6 → placeIn Zq sps sg .K3 = .ok k3 →
      headHeardWholeAt (headParAt G) (Kinds.Head.requestOf Zq.s₀) 0
        (k4LookOf G.W.HLy.fs k3.2
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A))) k6.2
        (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A)) = .ok x →
      ReadsQuiet.tables G.W.hS G.W.HLy G.W.H
        ((covOf Zq G (wit m.st.input).x).toOption.getD default) x = .ok t → tl.funs = t.funs := by
  intro sps k6 k3 xm t h1 h2 h3 hx ht
  rw [hwit] at ht
  exact head_sentence h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hGW hquiet hTT hVV hU hb hT hS htl
    (hbase sps k6 h1 h2) hlen (hcut sps k6 h1 h2) (hLook sps k3 h1 h3) hx ht

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tables_whole
#print axioms ProofFile.Honest.K1.head_sentence
#print axioms ProofFile.Honest.K1.head_clause
