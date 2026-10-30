-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Behind.lean: CONDITIONAL: at the member of the first chain that
stands at an attention segment's own rounds (kind K5): what holds behind its step's yes, joined out
of laws that are stated over the library alone (Johnson/Desc/K5/Honest/Law/DoorAtHead.lean,
BehindAtHead.lean) and what the chain's invariant hands over in front (Honest/K5/Law/Front.lean).
Two premises of those laws, "the list of the proof's places in the trees can be laid" and "the
lookup on the calls has a place in the plan", are paid here from the hypothesis.

  `open8_at`       the eight public items that those laws ask are open at the kind's border
  `runs_at_thr`    CONDITIONAL: behind the member's step the segment's four runs of claims return
                   (`RunsReturn`, Johnson/Desc/First/Att/K05MadeAt.lean)
  `formP_of_onAt`  CONDITIONAL: the table's promise at the next place, at the open sets stepped by
                   the kind's two rows, is the invariant's clause `formP` at the next border
  `honestLike_at`, `atBorder_at`   the two named premises of the law on the promise behind
                   (`behind_at_head`, Johnson/Desc/K5/Honest/Law/BehindAtHead.lean), at the honest
                   letters and at the table's own open sets at the border
  `formP_behind`   CONDITIONAL: the invariant's clause `formP` holds behind the member's step
  `k5_behind`      CONDITIONAL: **the debt `Behind` (Honest/Thread/Pays.lean) at the kind's member
                   of group g**
  `own_at_thr`     CONDITIONAL: **the item "the forms of the segment's own runs are worth 0" holds
                   behind the member's step, at every continuation of the challenges**, from what
                   the claims say (`SayAt`) in the item's own world: one of the six items that the
                   kind's row owes

Who is meant to pay the premises. The hypothesis `P5J.AtMgA`: not shown here. `K5Seated`: whoever
lays the list of halves and makes the place's public data. `Thr` in front: whoever shows it along
the chain. Kp, Rd (on the letters `keeps` and `rides`): whoever lays these two letters. `SayAt`: the
laws on the values that the honest side sends; none is shown here.

OF THE FOUR CLAUSES OF `Behind`, TWO ARE CARRIED BY PREMISES. No mark of failure behind, and the
table's promise behind (`formP`): shown. `keeps`: `K5Keeps` is shown, and the letter follows through
Kp. `rides`: from `rides` in front, through Rd.

The strings. The law on the promise behind speaks at the oracles' strings of a frame. At the honest
letters the promise reads no string: so a made-up frame without a tree, and one made-up value of its
strings on both sides, serve. No lemma is called for that here: Lean sees it by unfolding.

Limits. Every theorem is conditional. IN VALUE `own_at_thr`'s PREMISE hSay HOLDS ITS CONCLUSION: by
the library's own law what the claims say is "every form of the runs is worth 0", which is the
item's clause on values. What `own_at_thr` adds is the item's four other clauses (the open segment's
part is there; the readers return; the late slots pass; each form passes the public test) and the
frame around them. Whether `SayAt` can be met is not said here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Keeps
import Johnson.Desc.ProofFile.Honest.K5.Law.Front
import Johnson.Desc.K5.Honest.Law.BehindAtHead
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place OpenedColumn Strs Chain Claim First.S First.Pub First.rowOf
  noDigest)
open VerifiableInference.Desc.First.Att (P.inOf)
open VerifiableInference.Desc.First (Item onAt openSets pubSets start leavesName stepOpen pubStep
  pubRowM openSets_succ pubSets_succ)
open VerifiableInference.Desc.Sound (mgBase mgAll seatTab Frame strsOf doorsFitB_parts)
open VerifiableInference.Desc.First.Att.P
open H2K5.Door (moreOver9)
open H2K5.Honest (Open8 runs_at_head own_at_head worldBehind HonestLike AtBorder behind_at_head
  K5Keeps)
open ProofFile.Honest.FirstThread (Script WtF honest noStrs)
open P5J (AtMgA mgAtAll TS CellsM)

/-- The eight public items are open at the kind's border. CONDITIONAL: g is below 12. -/
theorem open8_at {g : Nat} (hg : g < 12) : Open8 (2 * g + 1)
    ((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?.getD []) :=
  ⟨open8_k5 hg _ (by simp), open8_k5 hg _ (by simp), open8_k5 hg _ (by simp),
    open8_k5 hg _ (by simp), open8_k5 hg _ (by simp), open8_k5 hg _ (by simp),
    open8_k5 hg _ (by simp), open8_k5 hg _ (by simp)⟩

/-- The named premise on the two lists, at the table's own open sets at the kind's border. By the
library's decisions on the written lists. CONDITIONAL: g is below 12. -/
theorem atBorder_at {g : Nat} (hg : g < 12) : AtBorder g
    (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
    ((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?.getD []) :=
  { open8 := open8_at hg
    caller := open_k5 hg _ (by simp)
    twenty := fun q hq =>
      H2K5.Door.twenty_full hg q ((doorsFitB_parts (H2K5.Door.doors_full hg)).1 q hq).1
    narrow := fun q hq => ((doorsFitB_parts (H2K5.Door.doors_full hg)).1 q hq).2
    ties := H2K5.Door.ties_full hg }

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- The named premise on the meaning, at the honest letters: by unfolding. CONDITIONAL: under the
hypothesis h, of which the meaning is made. -/
theorem honestLike_at : HonestLike h (honest (mgAtAll h) ans test) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ => trivial⟩

/-- **Behind the member's step the segment's four runs of claims return.** CONDITIONAL: under the
hypothesis h, `K5Seated`, `Thr` in front and the step's yes. -/
theorem runs_at_thr {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E
      ds y cols s') :
    ∃ att hd5 G, s.here = .att att ∧
      hear a.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, [], 0) ∧
      s' = behind s att hd5 G ∧ RunsReturn a s att hd5 G := by
  obtain ⟨Pl, Dc⟩ := seated_decides h hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hT
  have hr := reach_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Hs.member).1) hT
  exact ⟨att, hd5, G, e, hh, rfl, runs_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl
    _ _ (open8_at hg) hr hu hon e hh⟩

/-- **The table's promise at the next place is the invariant's clause at the next border.**
CONDITIONAL: g is below 12; the promise at the open sets stepped by the kind's two rows. -/
theorem formP_of_onAt {g : Nat} (hg : g < 12) {π : ProofFile.InstPub} {s' : TS}
    (hon : onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (some ⟨1, some (2 * g + 1), 4, .K1⟩)
      (stepOpen (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
        (First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩))
      (pubStep
        (((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
        (pubRowM ((moreOver9 {}).strike leavesName) P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩))
      (π, s') noStrs) :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).formP (borderOf g + 1)
      (π, s') := by
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have hnx : P5J.At.ps[borderOf g + 1]? = some ⟨1, some (2 * g + 1), 4, .K1⟩ :=
    H2K5.Door.next_full hg
  have hm : (honest (mgAtAll h) ans test).more = (moreOver9 {}).strike leavesName :=
    H2K5.Door.hm_all h
  show onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
    (P5J.At.ps[borderOf g + 1]?)
    (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g + 1]?).getD [])
    (((pubSets (honest (mgAtAll h) ans test).more P5J.At.links P5J.At.ps)[borderOf g + 1]?).getD
      [])
    (π, s') noStrs
  rw [hnx, hm, openSets_succ _ _ _ _ _ hpl, pubSets_succ _ _ _ _ _ hpl]
  exact hon

/-- **The invariant's clause `formP` holds behind the member's step.** CONDITIONAL: under the
hypothesis h, `K5Seated`, `Thr` in front and the step's yes. -/
theorem formP_behind {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E
      ds y cols s') :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).formP (borderOf g + 1)
      (m.st.input.x.pub, s') := by
  obtain ⟨-, Dc⟩ := seated_decides h hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨hu, hon⟩ := onAt_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hT
  have hr := reach_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Hs.member).1) hT
  have hm : (honest (mgAtAll h) ans test).more = (moreOver9 {}).strike leavesName :=
    H2K5.Door.hm_all h
  have hb := behind_at_head h hL hg ha (honest (mgAtAll h) ans test)
    (honestLike_at h ans test) _ _ (atBorder_at hg)
    (Fr := ⟨0, [], fun _ => 0, 0⟩) (bs := 0) (y := (fun _ => (0, []), fun _ => []))
    (y' := (fun _ => (0, []), fun _ => [])) ⟨rfl, fun _ _ _ => rfl⟩ hr hu hon e hh
  rw [hm] at hb
  exact formP_of_onAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hb

/-- **THE DEBT `Behind` AT THE KIND's MEMBER OF GROUP g**: behind its step's yes the form and the
riders hold, and the step has left what `keeps` names. CONDITIONAL: under the hypothesis h and
`K5Seated`; Kp: keeps at the border holds wherever `K5Keeps` does; Rd: what rides says in front of
the border it says behind, of every state that `K5Keeps` ties to the one in front. -/
theorem k5_behind {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s') :
    Behind (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  obtain ⟨-, Dc⟩ := seated_decides h hg ha Hs.member
  have hK := k5_keeps_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hT hd
    hS
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨⟨?_, ?_⟩, ?_, Kp _ _ hK⟩
  · show s'.failed.isNone = true
    rw [form_behind _ Hs Dc hd hS]
    rfl
  · show (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).formP (borderOf g + 1)
      (y.2.st.input.x.pub, s')
    rw [ei]
    exact formP_behind h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hT hd hS
  · show rides (borderOf g + 1) y.2.st.input s'
    rw [ei]
    exact Rd _ _ _ hT.2.2.2.2.2.1 hK

/-- **THE ITEM ON THE FORMS OF THE SEGMENT's OWN RUNS HOLDS BEHIND THE MEMBER's STEP**, at every
continuation of the challenges heard. CONDITIONAL: under the hypothesis h, `K5Seated`, `Thr` in
front and the step's yes; hSay: at every continuation, what the claims say holds in the item's own
world, at whatever the claims' reading at the state behind returns. -/
theorem own_at_thr {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E
      ds y cols s')
    (hSay : ∀ ds' att hd5 G gL, s.here = .att att → att.g = some gL → s' = behind s att hd5 G →
      ∀ i K, P.inOf (seatCO (parCOf a)) (parCOf a) (behind s att hd5 G) = some (i, K) →
        K5Law.SayAt Reading.gl
          (worldBehind h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd5 G
            (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
              ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).wit k y.2.st.input
                (y.2.st.heard ++ ds')))) a.S gL i K) :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Items
      [Item.formsT (2 * g + 1) 3 "own"] k s' y.2 (E.add y.1) := by
  intro ds' i hi
  obtain rfl : i = Item.formsT (2 * g + 1) 3 "own" := List.mem_singleton.1 hi
  obtain ⟨Pl, Dc⟩ := seated_decides h hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨att', gL, e', hgL, -⟩ :=
    (readyO_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg Pl hT).open_
  rw [e] at e'
  cases e'
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hT
  have hr := reach_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Hs.member).1) hT
  exact ⟨own_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr hu hon
    e hh h.𝔇.St _ hgL (hSay ds' att hd5 G gL e hgL rfl), fun hw => nomatch hw⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.open8_at
#print axioms ProofFile.Honest.K5.atBorder_at
#print axioms ProofFile.Honest.K5.honestLike_at
#print axioms ProofFile.Honest.K5.runs_at_thr
#print axioms ProofFile.Honest.K5.formP_of_onAt
#print axioms ProofFile.Honest.K5.formP_behind
#print axioms ProofFile.Honest.K5.k5_behind
#print axioms ProofFile.Honest.K5.own_at_thr
