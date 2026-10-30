-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlaysScript.lean: the kind "the code switch" (K2): (1) WHAT THE
KIND ASKS OF THE THREAD's TABLES AT THE SWITCH's MEMBER's OWN TREES, IN ONE STRUCTURE: `K2Script`: a
named premise on the frame's Script, in the form that the frame asks of each kind; (2) THE DEBT "IT
PLAYS", ASKED FROM THE PAIR (`PlaysS`, Honest/Thread/PaysS.lean), AT THE SWITCH's OWN MEMBER OF A
THREAD, OF THE KIND's ONE LOT's HALF: `switch_plays` (Honest/K2/Law/PlaysSeated.lean) WITHOUT
`K2Seated`: from the seven facts on the member and its half that the proof spends, `K2Script`, and
eight premises more. One definition, a premise's form; two statements with their proofs.

  `K2Script`            two clauses: table · fixed
  `k2Script_of_seated`  the tie: `K2Seated` gives it
  `switch_playsS`       THE DEBT, general in the thread

`K2Script` IS A SECOND TEXT OF TWO FIELDS OF `K2Seated` (Honest/K2/Seated.lean: table, fixed): to
the letter; `k2Script_of_seated` ties it. IT IS BANKED BESIDE THE FIRST TEXT, NOT SEATED: no choice
of a prover's fields and no sealed library names it; this file imports the first text. It names
`switchTableAt` (Honest/K2/Seated.lean); nothing that a prover sends, keeps or draws is written
anew. IT HOLDS THE TABLES; of the witness's messages this debt asks nothing: the structure may grow
at another debt.

THE CLAUSES SPEAK OF THE MEMBER's OWN TREES ALONE (the numbers from the member's first tree on, as
many as it has roots). table: each is, as the thread's function, the table that the half's first
move says · fixed: it turns no more from the member's front border on. At the frame's thread of the
first chain both are equations on the Script's letters `table` and `fixed` at these numbers. The
frame's own premise on `fixed` there (`fits_head`, Honest/Thread/FitsHead.lean) asks "at most the
rounds in front" of each tree below a border; the member's own trees lie below the border behind it
and not below the one in front: so the two hold together: by reading.

THE WIDTHS STAND APART, AS A PREMISE OF `switch_playsS`, NOT IN THE STRUCTURE: at a stand of the
pair in front of the member each tree that the second round opens has, as the thread's table, the
width that the numbers' list `read` states for it: THESE ARE TREES OF EARLIER MEMBERS, OTHER KINDS'
AMONG THEM: another payer's.

THE PREMISES OF `switch_playsS`, ALL SIXTEEN. ON THE MEMBER AND ITS HALF: here · place · half ·
rounds · oracles · roots · opens (`K2Seated`'s fields of these names, to the letter) · `K2Script` ·
the widths · PUBLIC, ON THE PLACE: `Sizes.serves` · `Sizes.roomy` · `placeFits` · `closingOk` ·
PUBLIC, THE NUMBERS AGAINST THE HONEST SENDING: the shapes · the answers' number · ON THE LETTER
`valid`: a valid input's public instance passes `publicOk`.

By: the proof of `switch_plays`, line for line, with the fields' names turned; its tools out of
Honest/K2/Law/PlaysSeated.lean, called.

Limits. NO MEMBER: the premises are shown met together nowhere; `K2Script` IS A DEFINITION: A
PREMISE's FORM: NOTHING IS CLAIMED OF IT, AND NOTHING SHOWS THAT IT CAN BE MET: no Script is laid
anywhere. ONE DEBT OF FIVE. IT IS ON RETURNING AND ON WHICH TABLES ARE AT HAND: nothing on what a
table holds, nor on whether the verifier's step says yes. All other Limits of
Honest/K2/Law/PlaysSeated.lean stand. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysSeated
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Oracle itemOf Place)
open VerifiableInference.Desc.K2.Honest (Sizes)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds)

variable {X W₀ Rc Xi Tr : Type}

/-- **What the kind asks of the thread's tables at the switch's member.** It is a definition: a
premise's form. Nothing is claimed of it, and nothing shows that it can be met. -/
structure K2Script {Bk : ProverCoinCounts} {Pb : Type}
    (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (q : P2) : Prop where
  /-- the member's own trees are the tables that the half's first move says -/
  table : ∀ j, j < q.roots → ∀ k w h, T.table (.own (treesTo T.bs b + j)) k w h =
    (p.place, switchTableAt Bk T.chain Sd D readers closing p k w h j)
  /-- they turn no more from the member's front border on -/
  fixed : ∀ j, j < q.roots → T.fixed (.own (treesTo T.bs b + j)) = T.front + roundsTo T.bs b

/-- **The tie**: the elder record gives the structure. -/
theorem k2Script_of_seated {Bk : ProverCoinCounts} {Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat) (blk : Block S Cl)
    (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (q : P2)
    (before : S → Except String S) (after : S → S → Except String S) (clause : S → S → Prop)
    (seg : Nat) (iCarry iPin iCarried iSample iPosition : T.ι) (toP : T.P → Pp)
    (toW : T.Wt → VerifiableInference.Desc.Wit (VerifiableInference.Desc.Sound.CellsQ rows cols)
      Tok VerifiableInference.Desc.Sound.MsgT)
    (Dof : Local W₀ Rc Xi Tr → VerifiableInference.Desc.Sound.MgData Xi' Pp Tok rows cols nR Xp)
    (Mg₀ : VerifiableInference.Desc.First.Meaning Pp (VerifiableInference.Desc.Wit
      (VerifiableInference.Desc.Sound.CellsQ rows cols) Tok VerifiableInference.Desc.Sound.MsgT))
    (Q : K2Seated T b blk Sd D readers closing p q before after clause seg iCarry iPin iCarried
      iSample iPosition toP toW Dof Mg₀) :
    K2Script T b Sd D readers closing p q :=
  ⟨Q.table, Q.fixed⟩

/-- **THE DEBT "IT PLAYS", ASKED FROM THE PAIR**, general in the thread. -/
theorem switch_playsS {Bk : ProverCoinCounts} {Pb : Type}
    (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat) (blk : Block S Cl)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace) (q : P2)
    (hhere : T.bs[b]? = some blk) (hplace : blk.place = p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) =
      some (switchHalf (coreSender freshTable) D readers (lotClosingAt lay segs) p))
    (hrounds : blk.rounds = rounds q) (horacles : blk.oracles = [q.sent, []])
    (hroots : q.sent.length = q.roots) (hopens : ∀ r ∈ q.read, r.1 < treesTo T.bs b)
    (Sc : K2Script T b (coreSender freshTable) D readers (lotClosingAt lay segs) p q)
    (hW : ∀ r ∈ q.read, ∀ k s m E, ThrS T Said b k s m E →
      (T.tableAt (.own r.1) k m).2.words = r.2.2)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (hS : q.sent.map (fun o => (o.logLength, o.words)) =
      treeShapes p.sizes.codes (switchSent p.sizes p.others))
    (hA : (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers = q.answers)
    (hc : closingOk freshTable (segs.take p.link) p = true)
    (hv : ∀ w, T.valid w → publicOk D lay p (segs.take p.link) w.x = true) :
    PlaysS T Said b := by
  intro blk' hblk' k s m E ds l hTS hd _ hl
  have hT := hTS.1
  rw [hhere] at hblk'
  cases hblk'
  obtain ⟨hHand, hFit, -, -, hMade, -, hval⟩ := hT
  obtain ⟨-, -, hsent, hTight, -⟩ := hMade
  obtain ⟨c, hlend, el⟩ := steps_one_half hhalf hl
  obtain ⟨d₁, d₂, hq⟩ : ∃ d₁ d₂, rounds q = [d₁, d₂] := ⟨_, _, rfl⟩
  rw [hrounds, hq] at hd
  obtain ⟨x₁, x₂, rfl, -⟩ := draws_two d₁ d₂ ds hd
  obtain ⟨Tb, g, m', hy, hi, sh, hsay⟩ := half_played D readers (lotClosingAt lay segs) p blk d₁ d₂
    q.sent [] (by rw [hrounds, horacles, hq]; rfl) (T.φ.sees m.st.input) c x₁ x₂ m hs hr hf
    (rounds_items q d₁ d₂ hq).1 hS (by rw [hA]; exact (rounds_items q d₁ d₂ hq).2) rfl
    ((returnsLaw D readers lay segs p hc m.st.input m.st.heard c.1.2.2).trans (hv _ hval))
  rw [← el] at hy
  have hlen : Tb.length = q.roots := by
    have := congrArg List.length (sh.trans hS.symm)
    rw [List.length_map, List.length_map] at this
    exact this.trans hroots
  obtain ⟨cols', hcols⟩ := old_cols q T.chain T.ft
    (E.add [⟨blk.name, blk.place, 0, true, [], Tb.map some, x₁⟩,
      ⟨blk.name, blk.place, 0, true, g, [], x₂⟩]).stored
    (E.add [⟨blk.name, blk.place, 0, true, [], Tb.map some, x₁⟩,
      ⟨blk.name, blk.place, 0, true, g, [], x₂⟩]).tree x₁ x₂ (fun r hr' => by
      have hin : Fmt.TreeSource.own r.1 ∈ T.hand b :=
        List.mem_append_right _ (List.mem_map.2 ⟨r.1, List.mem_range.2 (hopens r hr'), rfl⟩)
      have ha := hHand.2 _ hin
      unfold Thread.handAt at ha
      cases hu : E.tree (.own r.1) with
      | none =>
        rw [hu] at ha
        cases ha
      | some u =>
        rw [hu] at ha
        refine ⟨u, Env.add_keeps hTight _ hu, ?_⟩
        simp only [Option.any_some, Table.same, Bool.and_eq_true, beq_iff_eq] at ha
        exact ha.2.1.2.trans (hW r hr' k s m E hTS))
  refine ⟨_, cols', ⟨⟨l, hl, hy⟩, by rw [hrounds]; exact hcols⟩, ?_⟩
  intro σ hσ
  obtain ⟨j, hj, rfl⟩ := mem_fresh T hhere σ hσ
  have hj' : j < q.roots := by
    rw [horacles] at hj
    simpa [hroots] using hj
  have hjT : j < Tb.length := hlen ▸ hj'
  have hheard : m'.st.heard = m.st.heard ++ [x₁, x₂] := play_heard _ _ _ _ _ hy
  have htab : T.tableAt (.own (treesTo T.bs b + j)) k m' = (p.place, Tb[j]) := by
    unfold Thread.tableAt
    rw [Sc.table j hj', Sc.fixed j hj', hi, hheard, ← T.heard_length hFit, List.take_left,
      tableAt_is Bk T.chain (coreSender freshTable) D readers (lotClosingAt lay segs) p k
        m.st.input m.st.heard c.1 Tb (hplace ▸ lent_part Bk _ _ blk.place _ D readers _ p c hlend)
        (hsay ⟨[], none⟩) j, List.getElem?_eq_getElem hjT]
    rfl
  unfold Thread.handAt
  rw [htab]
  have htree : (E.add [⟨blk.name, blk.place, 0, true, [], Tb.map some, x₁⟩,
      ⟨blk.name, blk.place, 0, true, g, [], x₂⟩]).tree (.own (treesTo T.bs b + j)) =
      some (blk.place, Tb[j]) := by
    show (if treesTo T.bs b + j < E.sent then _ else
      ((tablesOf _)[treesTo T.bs b + j - E.sent]?).bind id) = _
    rw [hsent, if_neg (by omega), Nat.add_sub_cancel_left]
    simp [tablesOf, hjT]
  show (Option.any _ ((E.add _).tree _)) = true
  rw [htree]
  simp [hplace, same_self]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.k2Script_of_seated
#print axioms ProofFile.Honest.K2.Law.switch_playsS
