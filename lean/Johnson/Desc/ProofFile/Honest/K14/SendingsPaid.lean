-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsPaid.lean: "it plays" (Plays,
Honest/Thread/Pays.lean) is proved at a member of a chain's thread WHERE AtSend HOLDS: the member
declares a sending's rounds, the sending's half stands beside it, and the thread's own fields fixed
and table at the new trees are as TreesLaid asks (table IS sendTable). Here the member brings new
trees: so the sentence also asks that each new tree is at hand behind the member, from the sender's
place, and shows what the thread's own function for that tree shows.

  sendTable       THE FUNCTION TO LAY AS A THREAD's table AT A SENDING's TREE number i: of a run's
                  coins, the input and challenges: the sender's place, and table number i of
                  sendTablesAt (Honest/K14/SendingsPlay.lean) at the first coins at the part's
                  address
  SendJob.readsBelow, readsBelow_mono, sendTablesAt_take   a job's data reads none but the first n
                  challenges; then so do its tables
  heardFrom_take, jobU_readsBelow, jobOmega_readsBelow   the two sendings' data read none but the
                  first A.atPoint + 1 challenges: up to "LIN point"'s where atPoint, which is any
                  number here, is that round's number
  TreesLaid       the thread's two fields fixed and table at a sending's new trees
  AtSend          the member number b is a sending, beside the sending's half, and TreesLaid
  send_Plays      **AtSend gives Plays**: at all coins; of the thread's sentence in front it uses
                  the count of the challenges heard and the count of the trees sent

What is assumed, in AtSend. member: what send_moved asks of the sub-protocol (SendDeclared). half:
the half at the member's place is the lifted part. trees (TreesLaid): fixed: each new tree is fixed
by challenges that have been heard in front of the member, and the job's data reads none but these;
table: THE THREAD's FUNCTION table AT EACH NEW TREE IS sendTable: an equation between functions of
the coins, which fixes no coin. Where nothing stands at the number b, AtSend and Plays are met
vacuously. Threads at which AtSend holds: atSend_full (Honest/K14/Thread2Full.lean): at the members
2 and 5 of the thread letters2 whose free fields are laid by fullOver, table among them, under
Plan2; atSendU_of and atSendOmega_of (Honest/K14/PaidAll.lean): from AtEight and the sendings'
halves among the thread's, with TreesLaid still a premise.
What is not claimed. That AtSend holds at the shared chain's thread of the IOP as written in Lean.
Nothing on the frame's other sentences at a member (Behind, Exchange, RidesPast, Accepted). Nothing
on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E)
open OnBytes.Slice (toE)
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {Bk : ProverCoinCounts} {S Cl W X Pb : Type}

/-- **The function to lay as a thread's table at a sending's tree number i.** pl: the sender's
place; ch: the chain's number. Where the coins are not at hand, or the sending has no such tree: a
table of one empty symbol. -/
def sendTable (J : SendJob) (wit : W → Ask) (pl : Place) (ch i : Nat) (k : Coins Bk) (w : W)
    (h : List Fmt.Drawn) : Place × Table :=
  (pl, match (k.look ch { place := pl, part := 0 }).2.cut { f := 0, e := 0 }
      (sendingPart J).takes with
    | some own => (sendTablesAt J own (wit w) h).getD i
        { logLength := 0, words := 0, sym := fun _ j => j.elim0 }
    | none => { logLength := 0, words := 0, sym := fun _ j => j.elim0 })

/-- The job's data reads none but the first n challenges. -/
def SendJob.readsBelow (J : SendJob) (n : Nat) : Prop :=
  ∀ a h, J.data { input := a, heard := h.take n, own := () } =
    J.data { input := a, heard := h, own := () }

/-- What reads none but the first n challenges reads none but the first n', for n ≤ n'. -/
theorem readsBelow_mono {J : SendJob} {n n' : Nat} (h : J.readsBelow n) (hn : n ≤ n') :
    J.readsBelow n' := by
  intro a l
  rw [← h a (l.take n'), List.take_take, Nat.min_eq_left hn, h a l]

/-- Then the tables read none but the first n challenges. -/
theorem sendTablesAt_take {J : SendJob} {n : Nat} (hJ : J.readsBelow n)
    (own : Cs (sendingPart J).takes) (a : Ask) (h : List Fmt.Drawn) :
    sendTablesAt J own a (h.take n) = sendTablesAt J own a h := by
  unfold sendTablesAt SendJob.rows
  rw [hJ a h]

/-- The one challenge number p is read off the first p + 1. -/
theorem heardFrom_take (a : Ask) (h : List Fmt.Drawn) (p : Nat) :
    heardFrom ({ input := a, heard := h.take (p + 1), own := () } : State Ask Unit) p 1 =
      heardFrom ({ input := a, heard := h, own := () } : State Ask Unit) p 1 := by
  unfold heardFrom
  show ((h.take (p + 1)).drop p).take 1 = (h.drop p).take 1
  rw [List.drop_take, Nat.add_sub_cancel_left, List.take_take, Nat.min_self]

/-- "send o_u" reads none but the first A.atPoint + 1 challenges: those up to "LIN point"'s, where
A.atPoint is that round's number; here it is any number. -/
theorem jobU_readsBelow (A : SendPub) : (jobU A).readsBelow (A.atPoint + 1) := by
  intro a h
  show (fun _ => Desc.K14.Honest.uAtE A.P.S (elems (heardFrom _ A.atPoint 1)) a.rows) =
    fun _ => Desc.K14.Honest.uAtE A.P.S (elems (heardFrom _ A.atPoint 1)) a.rows
  rw [heardFrom_take]

/-- "send o_omega" reads none but the first A.atPoint + 1 challenges: the like. -/
theorem jobOmega_readsBelow (A : SendPub) : (jobOmega A).readsBelow (A.atPoint + 1) := by
  intro a h
  show (fun _ => Desc.K14.Honest.omegaAtE A.P.S (elems (heardFrom _ A.atPoint 1)) a.rows) =
    fun _ => Desc.K14.Honest.omegaAtE A.P.S (elems (heardFrom _ A.atPoint 1)) a.rows
  rw [heardFrom_take]

variable (T : Thread Bk S Cl Empty W X Pb)

/-- **The thread's two fields on a sending's new trees.** i: the number of a new tree among the
member's. -/
structure TreesLaid (b : Nat) (J : SendJob) (wit : W → Ask) : Prop where
  fixed : ∀ blk, T.bs[b]? = some blk → ∀ i, i < (blk.oracles.flatMap id).length →
    T.fixed (.own (treesTo T.bs b + i)) ≤ T.front + roundsTo T.bs b ∧
      J.readsBelow (T.fixed (.own (treesTo T.bs b + i)))
  table : ∀ blk, T.bs[b]? = some blk → ∀ i, i < (blk.oracles.flatMap id).length →
    T.table (.own (treesTo T.bs b + i)) = sendTable J wit blk.place T.chain i

/-- **The member number b is a sending**, beside the sending's half. -/
structure AtSend (b : Nat) (J : SendJob) (wit : W → Ask) : Prop where
  member : ∀ blk, T.bs[b]? = some blk → SendDeclared blk J
  half : ∀ blk, T.bs[b]? = some blk → (T.hs.find? fun h => h.place == blk.place) =
    some { place := blk.place, parts := [liftSend wit (sendingPart J)] }
  trees : TreesLaid T b J wit

variable {T} {b : Nat} {J : SendJob} {wit : W → Ask}

/-- **A sending: it plays, where AtSend holds at b**: at all coins. -/
theorem send_Plays (h : AtSend T b J wit) : Plays T b := by
  intro blk hb k s m E ds l hT hd _ hl
  obtain ⟨d₀, d₁, os, hr, ho, hf₀, hf₁, ho₀, hs₀, ho₁, hs₁⟩ := (h.member blk hb).rounds
  obtain ⟨x₀, x₁, c, rfl, hc, hp, hcols⟩ :=
    send_moved J wit blk d₀ d₁ os hr ho hf₀ hf₁ ho₀ hs₀ ho₁ hs₁ (h.half blk hb) hl m ds hd
  refine ⟨_, [], ⟨⟨l, hl, hp⟩, hcols _ _ _ _⟩, ?_⟩
  intro σ hσ
  obtain ⟨i, hi, rfl⟩ := fresh_mem_own T hb hσ
  obtain ⟨hfx, hrd⟩ := h.trees.fixed blk hb i hi
  have hos : (blk.oracles.flatMap id).length = os.length := by
    rw [ho]
    simp
  -- as many tables as oracle messages
  have hlen : (sendTablesAt J c.1.1 (wit m.st.input) m.st.heard).length = os.length := by
    have hf := hf₀ (J.rows ⟨wit m.st.input, m.st.heard, ()⟩ (coinsE c.1.1).toArray)
    unfold Sending.fits at hf
    rw [Bool.and_eq_true] at hf
    have e := congrArg List.length (beq_iff_eq.1 hf.2)
    rw [List.length_map, List.length_map] at e
    exact e
  have hi' : i < (sendTablesAt J c.1.1 (wit m.st.input) m.st.heard).length := by
    rw [hlen, ← hos]
    exact hi
  -- the tree behind the source, behind the two rounds
  have hsent : E.sent = treesTo T.bs b := hT.2.2.2.2.1.2.2.1
  have htree : (E.add
      [playedBy blk [] ((sendTablesAt J c.1.1 (wit m.st.input) m.st.heard).map some) x₀,
        playedBy blk (sendShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])) [] x₁]).tree
        (.own (treesTo T.bs b + i)) =
      some (blk.place, (sendTablesAt J c.1.1 (wit m.st.input) m.st.heard)[i]) := by
    rw [← hsent, add_own]
    simp [tablesOf, playedBy, hi']
  -- the thread's own function at the source
  have hheard : m.st.heard.length = T.front + roundsTo T.bs b := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    exact e
  have hown : (k.look T.chain ⟨blk.place, 0⟩).2.cut ⟨0, 0⟩ (sendingPart J).takes =
      some c.1.1 := lendRow_own (p := (liftSend wit (sendingPart J) : Part Empty W X)) hc
  have htab : T.tableAt (.own (treesTo T.bs b + i)) k
      (pastOf (pastOf m [] x₀) (sendShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])) x₁) =
      (blk.place, (sendTablesAt J c.1.1 (wit m.st.input) m.st.heard)[i]) := by
    unfold Thread.tableAt
    rw [h.trees.table blk hb i hi]
    show sendTable J wit blk.place T.chain i k m.st.input
      (((m.st.heard ++ [x₀]) ++ [x₁]).take _) = _
    rw [List.append_assoc, List.take_append_of_le_length (by rw [hheard]; exact hfx)]
    unfold sendTable
    rw [hown]
    show (blk.place, (sendTablesAt J c.1.1 (wit m.st.input) (m.st.heard.take _)).getD i _) = _
    rw [sendTablesAt_take hrd, List.getD_eq_getElem _ _ hi']
  unfold Thread.handAt
  rw [htree, htab]
  simp [Table.same]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.readsBelow_mono
#print axioms ProofFile.Honest.K14.sendTablesAt_take
#print axioms ProofFile.Honest.K14.heardFrom_take
#print axioms ProofFile.Honest.K14.jobU_readsBelow
#print axioms ProofFile.Honest.K14.jobOmega_readsBelow
#print axioms ProofFile.Honest.K14.send_Plays
