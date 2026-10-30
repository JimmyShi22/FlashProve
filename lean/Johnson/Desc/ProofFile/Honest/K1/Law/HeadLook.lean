-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HeadLook.lean: THE ONE PREMISE ON THE
RUN OF THE OUTPUT HEAD's "SENTENCE ON THE RUN" (hLook of head_sentence, HeadSentence.lean in this
folder) IS PAID, BY CALLS OF ANOTHER HOUSE's ROW AND OF SEALED LAWS: SO THE LAST CLAUSE OF HeadPlanS
(TieReadsHeadAtS.lean in this folder) STANDS AT THE THREAD UNDER THE LIBRARY's HEAD, AT THE READS'
MEMBER OF THE HEAD's SEGMENT (number 342), WITH NO PREMISE ON THE RUN BUT THE THREAD's OWN. Three
statements and their proofs. No definition. A rider rides with it: "an
implication: no member: that the thread stands in front of that member at any run is shown by
nobody".

  lookHeardAt_k4    the two houses' texts for what a lookup has sampled, lookHeardAt and k4LookOf,
                    lay the fields zx, zk, zb0, zb1 and shape by the same terms: by unfolding. NOT
                    CALLED: head_look's last line goes by the same unfolding: the lemma says aloud
                    what that step leans on
  head_look         at the stand in front of member 342 the state's copy of what the lookup on the
                    head's calls left agrees with k4LookOf of what was heard, in these five fields
  head_clause_paid  the clause in its own spelling: head_clause, its hLook paid by head_look

THE ROAD OF head_look. The thread's clause Made at 342 hands out the fold over the first 341 members
and the state sj that it leads to: made_member_from
(Johnson/Desc/ProofFile/Honest/Thread/MemberFrom.lean). AT THAT VERY FOLD THE LOOKUPS'
head_calls_tie (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadCallsTie.lean) SAYS: what sj holds
as the lookup's structure agrees with lookHeardAt's text, at the shape of the site on the calls at
link 24 and the rounds of the first 340 members, in the eleven fields of OpenSame
(Johnson/Desc/ProofFile/Honest/K3/HeardWhole.lean): the five are among them. Member 341's yes keeps
the field: k6_keeps_of_member_step (Johnson/Desc/K6/Honest/Law/KeepsMember.lean), K6Keeps.own
(Keeps.lean there), at the member that P4.k6_member_at_mg finds. The state behind 341 is the
stand's: foldBlocks_nil. The list of challenges: what was seen is what was heard (Made's first
clause); the thread has nothing ahead of its chain: its front is 0 by its text.

THE PREMISES OF head_clause_paid, BY KIND. THE HEAD: h : P5J.AtMgA: A HYPOTHESIS. THE THREAD's OWN:
hT, hS, htl. THE MAKER's TWO RETURNS: the clause's own. PUBLIC, ON PLANS AND NUMBERS, ASKED, NONE
EVALUATED AT THE HEAD: head_clause's nine (hGW, hquiet, hTT, hVV, hU, hb, hbase, hlen, hcut) AND TWO
THAT ENTER HERE: hfs (the shape of the site on the calls at link 24 is the filler's G.W.HLy.fs), hk3
(K3's place in the filler's cuts is the number of rounds of the first 340 members). ON THE LETTER
wit: hwit, as in head_clause. ON THE RUN: NONE. No witness, no Script's field and no coin is read;
of the input the instance's public request alone; the run's coins stand as a bound letter, handed on
whole to the thread's stand and step.

WHICH OF THESE FORMS STAND ALREADY, AND WHO HAS A PAYER. FORMS THAT STAND: h (sealed); hb and hT
(the two premises of thr_reach, Johnson/Desc/ProofFile/Honest/Thread/ReachFacts.lean); hS,
htl, hU, hquiet (the premises of head_record, HeadRecord.lean in this folder). NEW
IN THESE TWO FILES, EACH AN EQUATION OR AN INEQUALITY BETWEEN PUBLIC TERMS, NONE ON THE SCRIPT, THE
WITNESS OR COINS: hGW, hTT, hVV, hbase, hlen, hcut (HeadSentence.lean), hfs, hk3 (here); and hwit,
on the letter wit at the run's input. G, Zq AND Zp ARE LETTERS HERE: ONCE THEY ARE THE HEAD's OWN,
AT THE LIBRARY's WRITTEN CONSTANTS, THESE ARE CLOSED FACTS WHICH LEAN's KERNEL MIGHT PAY: NOT TRIED:
hb, hTT, hVV, hbase, hlen, hcut, hfs, hk3. PAYERS THAT LIE, NOT CALLED: for hquiet k1Quiet_head
(Johnson/Desc/K8/Honest/ReadsSeat.lean); for one half of hlen front_eight
(Johnson/Desc/ProofFile/Honest/K6/Law/HidesAtRow.lean); near hfs head_calls_site_found
(HeadCallsTie.lean): headCallsShape is the shape of a site that is there. FOR hGW, hU, hwit NO PAYER
WAS SOUGHT.

KIN. In the seal and laws.12's closed list nobody calls head_calls_tie; no file names both
lookHeardAt and k4LookOf (sought by name, with a control by the same pass). NEAR: head_keys_tie and
HeadG1At (HeadCallsTie.lean): the field zk alone, carried from 342 to 346, for another kind's
statement.

NO NEGATIVE TEST. lettersHead is without code
(Johnson/Desc/ProofFile/Honest/Thread/ReachFacts.lean's own Limits).

Limits. AT lettersHead ALONE, at the class Claim: no letter L. ONE SEGMENT OF 25. IT PAYS ONE CLAUSE
OF HeadPlanS: the clauses on the book, the part, the layout and the makers' returns stay; and
HeadPlanS is one premise among those beneath the tie. sg is meant as 24. It stands over
MemberFrom.lean, another house's file that is on no row, and over files of ours that are in no seal.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.HeadSentence
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadCallsTie
import Johnson.Desc.K6.Honest.Law.KeepsMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.K8.ReadsQuiet (head)
open VerifiableInference.Desc.Kinds.Head.Law (p8K6)
open VerifiableInference.Desc.Kinds.Head.Honest (k6_keeps_of_member_step)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace.U3 (covOf u3Seats placeIn)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K3 (lookHeardAt)
open ProofFile.Honest.K3.Law.AtThr (head_calls_tie headLookOfK3 headCallsShape)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K6 (headHeardWholeAt headParAt headInFront)
open ProofFile.Honest.FirstThread (Script lettersHead WtF)

/-! ## 1 The two texts -/

/-- **THE TWO HOUSES' TEXTS FOR WHAT A LOOKUP HAS SAMPLED LAY FIVE FIELDS BY THE SAME TERMS**:
lookHeardAt (Johnson/Desc/ProofFile/Honest/K3/HeardWhole.lean) and k4LookOf
(Johnson/Desc/ProofFile/Honest/K4/Look.lean). By unfolding. -/
theorem lookHeardAt_k4 (hs : Forest.Shape) (base : ℕ) (hd : List Fmt.Drawn) :
    (lookHeardAt hs base hd).zx = (k4LookOf hs base hd).zx ∧
      (lookHeardAt hs base hd).zk = (k4LookOf hs base hd).zk ∧
      (lookHeardAt hs base hd).zb0 = (k4LookOf hs base hd).zb0 ∧
      (lookHeardAt hs base hd).zb1 = (k4LookOf hs base hd).zb1 ∧
      (lookHeardAt hs base hd).shape = (k4LookOf hs base hd).shape :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2 The lookup's part at the stand -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT THE STAND IN FRONT OF MEMBER 342 THE STATE's COPY OF WHAT THE LOOKUP ON THE HEAD's CALLS
LEFT AGREES WITH k4LookOf OF WHAT WAS HEARD, IN FIVE FIELDS**: head_sentence's premise hLook. -/
theorem head_look (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hb : 342 ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 342 k s m E)
    {fs : Forest.Shape} (hfs : headCallsShape Zp = fs) {N base₃ : ℕ}
    (hb3 : base₃ = roundsTo cF.blocksInOrder 340) (hN : roundsTo cF.blocksInOrder 341 ≤ N) :
    ∀ o g₁, s.here = .head o → o.lookHeard = some g₁ →
      g₁.zx = (k4LookOf fs base₃ (m.st.heard.take N)).zx ∧
        g₁.zk = (k4LookOf fs base₃ (m.st.heard.take N)).zk ∧
        g₁.zb0 = (k4LookOf fs base₃ (m.st.heard.take N)).zb0 ∧
        g₁.zb1 = (k4LookOf fs base₃ (m.st.heard.take N)).zb1 ∧
        g₁.shape = (k4LookOf fs base₃ (m.st.heard.take N)).shape := by
  intro o g₁ hso hol
  obtain ⟨b₆, hb₆, M⟩ := P4.k6_member_at_mg h.toAtMg
  have hM : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Made 342 k s m E := by
    have hT' := hT
    unfold Thr at hT'
    exact hT'.2.2.2.2.1
  have hseen : m.seen.map (·.drawn) = m.st.heard := by
    have hM' := hM
    unfold Thread.Made at hM'
    exact hM'.1
  obtain ⟨s₀, sj, sj', cols, rs₀, rs, c, n, rs', c', -, hfr, -, hst, -, hfold⟩ :=
    made_member_from (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (b := 342) (j := 341) (by omega) hb₆ hM
  have hnil : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.take 342).drop
      (341 + 1) = [] := List.drop_eq_nil_of_le (by rw [List.length_take]; omega)
  rw [hnil] at hfold
  obtain rfl : s = sj' := congrArg Prod.fst (foldBlocks_nil _ _ _ _ _ hfold)
  -- K6's member's yes keeps the field
  have K := k6_keeps_of_member_step M hst
  obtain ⟨o₀, o', ho₀, ho', e⟩ := K.own
  obtain ⟨-, -, o1, -, h1, -, hop, -⟩ := K
  rw [hso] at ho'
  cases ho'
  rw [ho₀] at h1
  cases h1
  have el : o.lookHeard = o₀.lookHeard := by rw [e]
  have hH : sj.lookHeard? = some g₁ := by
    unfold S.lookHeard?
    rw [ho₀]
    show (if o₀.opened then o₀.lookHeard else none) = some g₁
    rw [if_pos hop, ← el]
    exact hol
  -- the lookups' tie behind member 340
  have T := head_calls_tie h s₀ _ cols sj rs₀ c g₁
    ((m.st.heard.take N).drop (roundsTo cF.blocksInOrder 341)) hfr hH
  have hlist : ((m.seen.drop
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front).take
      ((cF.blocksInOrder.take 341).flatMap (·.rounds)).length).map (·.drawn) ++
        (m.st.heard.take N).drop (roundsTo cF.blocksInOrder 341) = m.st.heard.take N := by
    show ((m.seen.drop 0).take (roundsTo cF.blocksInOrder 341)).map (·.drawn) ++ _ = _
    rw [List.drop_zero, List.map_take, hseen,
      show m.st.heard.take (roundsTo cF.blocksInOrder 341) =
        (m.st.heard.take N).take (roundsTo cF.blocksInOrder 341) by
          rw [List.take_take, Nat.min_eq_left hN]]
    exact List.take_append_drop _ _
  rw [hlist] at T
  subst hfs
  subst hb3
  exact ⟨T.zx, T.zk, T.zb0, T.zb1, T.shape⟩

/-! ## 3 The clause, with no premise on the run -/

/-- **THE LAST CLAUSE OF HeadPlanS (K1/Law/TieReadsHeadAtS.lean), IN ITS OWN SPELLING, AT
lettersHead AND b = 342, WITH NO PREMISE ON THE RUN BUT THE THREAD's OWN.** head_clause, its hLook
paid by head_look. hwit: a rider, in marks: "on the letter wit: the
public instance alone; by unfolding at K1's reader as the fillings lay it". -/
theorem head_clause_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
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
    (hfs : headCallsShape Zp = G.W.HLy.fs)
    (hk3 : ∀ (sps : List Spot) (k3 : Spot × ℕ), spotsOf Zq.cuts = some sps →
      placeIn Zq sps sg .K3 = .ok k3 → k3.2 = roundsTo cF.blocksInOrder 340) :
    ∀ (sps : List Spot) (k6 k3 : Spot × ℕ) (x : OnBytes.Model.Head.Heard)
      (t : OnBytes.Model.Head.Tables), spotsOf Zq.cuts = some sps →
      placeIn Zq sps sg .K6 = .ok k6 → placeIn Zq sps sg .K3 = .ok k3 →
      headHeardWholeAt (headParAt G) (Kinds.Head.requestOf Zq.s₀) 0
        (k4LookOf G.W.HLy.fs k3.2
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A))) k6.2
        (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zq G) A)) = .ok x →
      ReadsQuiet.tables G.W.hS G.W.HLy G.W.H
        ((covOf Zq G (wit m.st.input).x).toOption.getD default) x = .ok t → tl.funs = t.funs := by
  intro sps k6 k3 xm t h1 h2 h3
  have hN : roundsTo cF.blocksInOrder 341 ≤ OnBytes.HonestTrace.heardOf (u3Seats Zq G) A := by
    have a1 := hbase sps k6 h1 h2
    have a2 := hcut sps k6 h1 h2
    have a0 : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front = 0 := rfl
    omega
  exact head_clause h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hGW hquiet hTT hVV hU hb hT hS htl
    wit hwit hbase hlen hcut
    (fun sps' k3' b1 b3 => head_look h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT hfs
      (hk3 sps' k3' b1 b3) hN) sps k6 k3 xm t h1 h2 h3

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lookHeardAt_k4
#print axioms ProofFile.Honest.K1.head_look
#print axioms ProofFile.Honest.K1.head_clause_paid
