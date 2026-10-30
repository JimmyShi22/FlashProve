-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Exchange.lean: CONDITIONAL: the frame of the debt `Exchange`
(Honest/Thread/Pays.lean) at the member of the first chain that stands at an attention segment's own
rounds (kind K5): the six items that the kind's row owes hold behind the member's step, at every
continuation of the challenges. And the member's debts in one statement.

The six. Three say that the forms of named runs are worth 0: "own", "planes", "join". Three are read
and owed again: the pin of the segment's first sending, the pin of the stored table, "every cell of
the segment is small" (`k5_ctx_owed`, Honest/K5/Law/Keeps.lean).

"planes" IS HAD WHOLE, from the item "the planes' worth" that the kind's row asks in front and that
the invariant in front holds (`planes_item_at_head`, Johnson/Desc/K5/Honest/Law/PlanesAtHead.lean).

IN VALUE TWO NAMED PREMISES HOLD THE CLAUSES ON VALUES OF "own" AND "join". Each of these items has
five clauses: the open segment's part is there; the run's reader returns; its late slots pass a
test; each form passes a public test; each form is worth 0. This file and those beneath it pay the
first four and the frame around them. The fifth is handed on under a named premise:
  `SayOwed`      for "own": what the claims say holds in the item's own world (`K5Law.SayAt`)
  `JoinOwed`     for "join": whatever form the lookup's text returns on the segment's key forms is
                 worth 0 in that world
So for these two `k5_exchange` is a frame, not a result on values. Each of the two speaks of the
steps of the member at the border alone: over every sub-protocol of the type it could not be met,
since a made-up one steps to any state.

  `owes_k5`, `asks_k5`   the six items that the kind's row, read forward, owes; the seven that it
                 asks
  `join_at_thr`, `planes_at_thr`   CONDITIONAL: the two items behind the member's step
  `k5_exchange`  CONDITIONAL: **`Exchange` at the kind's member of group g**
  `k5_owes`      CONDITIONAL: **`Plays`, `Behind`, `Exchange`, and `Accepted` for every fall, at
                 that member**: three of the four conjuncts of `Owes` and the one of `Yes`
                 (Honest/Thread/File.lean). The fourth conjunct, `RidesPast`, is not shown here

Who is meant to pay the premises. The hypothesis `P5J.AtMgA`: not shown here. `K5Seated`: whoever
lays the list of halves and makes the place's public data. The test `Thread.fits`: an evaluation on
the letters. `AnsReadsRest`, Kp, Rd: whoever lays the letters `ans`, `keeps`, `rides`. `SayOwed`:
the laws on the values that the honest side sends. `JoinOwed`: these, for the key forms, with the
law of the lookup on the calls on its own half of the join.

General in the letter `valid`: so every theorem holds at a `valid` that pins the input.

Limits. Every theorem is conditional. Neither named premise is shown to be met anywhere.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Behind
import Johnson.Desc.K5.Honest.Law.JoinAtHead
import Johnson.Desc.K5.Honest.Law.PlanesAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place OpenedColumn Strs Chain Claim First.S First.Pub First.rowOf
  noDigest)
open VerifiableInference.Desc.First.Att (P.inOf)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (seatTab)
open VerifiableInference.Desc.First.Att.P
open H2K5.Honest (worldBehind join_at_head planes_item_at_head K5Keeps)
open ProofFile.Honest.FirstThread (Script WtF honest noStrs)
open P5J (AtMgA mgAtAll TS CellsM)

/-! ## At the library's own letters -/

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

/-- **The six items that the kind's row, read forward, owes.** CONDITIONAL: g is below 12. -/
theorem owes_k5 {g : Nat} (hg : g < 12) :
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).row
      (borderOf g)).owes =
      [Item.formsT (2 * g + 1) 3 "own", .formsT (2 * g + 1) 2 "planes",
        .formsT (2 * g + 1) 2 "join", .pin (2 * g + 1) 0, .pinW, .constr (2 * g + 1) .small] := by
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have e : FirstRows.rowAt P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩ = FwdRow.of
      (First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).ins
      (First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).outs
      (First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).ctx := rfl
  show (FirstRows.rows P5J.At.links P5J.At.ps (borderOf g)).owes = _
  unfold FirstRows.rows
  rw [hpl, Option.map_some, Option.getD_some, e, k5_row (place_k5 hg)]
  rfl

/-- **A premise's form, for "own"**: along every step OF THE MEMBER AT THE BORDER (blk is bound to
it, as the debt's own text binds it) from `Thr` in front, at every continuation: what the claims say
holds in the item's own world, at whatever the claims' reading at the state behind returns. It is a
definition. Nothing is claimed of it. -/
def SayOwed (g : Nat) (a : Attention.Plan) : Prop :=
  ∀ (blk : Block TS ProofFile.Cl) (k : Coins Bk) (s s' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (E : Env) (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (cols : List OpenedColumn),
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).bs[borderOf g]? = some blk →
    Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) k s m E →
    drawsFit blk.rounds ds = true →
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E ds y
      cols s' →
    ∀ ds' att hd5 G gL, s.here = .att att → att.g = some gL → s' = behind s att hd5 G →
      ∀ i K, P.inOf (seatCO (parCOf a)) (parCOf a) (behind s att hd5 G) = some (i, K) →
        K5Law.SayAt Reading.gl
          (worldBehind h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd5 G
            (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
            ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).wit k y.2.st.input
              (y.2.st.heard ++ ds')))) a.S gL i K

/-- **A premise's form, for "join"**: along every such step, at every continuation: whatever form
the lookup's text returns on the segment's key forms at the state behind is worth 0 in the item's
own world. It is a definition. Nothing is claimed of it. -/
def JoinOwed (g : Nat) (a : Attention.Plan) : Prop :=
  ∀ (blk : Block TS ProofFile.Cl) (k : Coins Bk) (s s' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (E : Env) (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (cols : List OpenedColumn),
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).bs[borderOf g]? = some blk →
    Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) k s m E →
    drawsFit blk.rounds ds = true →
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E ds y
      cols s' →
    ∀ ds' att hd5 G, s.here = .att att → s' = behind s att hd5 G →
      ∀ (gL : Forest.Heard) (kf : Array Aff) (z : Aff × Fork × OnBytes.K.Kc.Tape),
        att.lookHeard = some gL →
        keysOfK (seatCO (parCOf a)) (parCOf a) (behind s att hd5 G) = some kf →
        VerifiableInference.Desc.First.Look.joinF gL kf G [] = some z →
        z.1.value Reading.gl
          (worldBehind h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) s att hd5 G
            (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
            ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).wit k y.2.st.input
              (y.2.st.heard ++ ds')))) = 0

/-- **The item on the form that the run "join" gathers holds behind the member's step**, at every
continuation. CONDITIONAL: under the hypothesis h, `K5Seated`, `Thr` in front, the step's yes, and
`JoinOwed`, which holds the item's clause on values. -/
theorem join_at_thr {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (hJ : JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E
      ds y cols s') :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Items
      [Item.formsT (2 * g + 1) 2 "join"] k s' y.2 (E.add y.1) := by
  intro ds' i hi
  obtain rfl : i = Item.formsT (2 * g + 1) 2 "join" := List.mem_singleton.1 hi
  have hJ' := hJ blk k s s' m E ds y cols Hs.member hT hd hS ds'
  obtain ⟨Pl, Dc⟩ := seated_decides h hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hT
  have hr := reach_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Hs.member).1) hT
  exact ⟨join_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr hu
    hon e hh h.𝔇.St _ (hJ' att hd5 G e rfl), fun hw => nomatch hw⟩

/-- **The seven items that the kind's row, read forward, asks.** CONDITIONAL: g is below 12. -/
theorem asks_k5 {g : Nat} (hg : g < 12) :
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).row
      (borderOf g)).asks =
      [Item.constr (2 * g + 1) .idn, .worth (2 * g + 1) 2 "planes", .worth (2 * g + 1) 2 "keys",
        .worth (2 * g + 1) 2 "rider", .pin (2 * g + 1) 0, .pinW, .constr (2 * g + 1) .small] := by
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have e : FirstRows.rowAt P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩ = FwdRow.of
      (First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).ins
      (First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).outs
      (First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).ctx := rfl
  show (FirstRows.rows P5J.At.links P5J.At.ps (borderOf g)).asks = _
  unfold FirstRows.rows
  rw [hpl, Option.map_some, Option.getD_some, e, k5_row (place_k5 hg)]
  rfl

/-- **The item on the forms of the lookup's run "planes" holds behind the member's step**, at every
continuation: FROM THE ITEM THAT THE KIND's ROW ASKS IN FRONT, "the planes' worth", which `Thr` in
front holds at every continuation. No premise on values. CONDITIONAL: under the hypothesis h, the
test on the letters, `K5Seated`, `Thr` in front and the step's yes. By `planes_item_at_head`
(Johnson/Desc/K5/Honest/Law/PlanesAtHead.lean). -/
theorem planes_at_thr {n : Nat} {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E
      ds y cols s') :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Items
      [Item.formsT (2 * g + 1) 2 "planes"] k s' y.2 (E.add y.1) := by
  intro ds' i hi
  obtain rfl : i = Item.formsT (2 * g + 1) 2 "planes" := List.mem_singleton.1 hi
  obtain ⟨Pl, Dc⟩ := seated_decides h hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hT
  have hr := reach_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Hs.member).1) hT
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hfit' := hfit
  unfold Thread.fits at hfit'
  simp only [Bool.and_eq_true] at hfit'
  have hop : Item.worth (2 * g + 1) 2 "planes" ∈
      (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).opened
        (borderOf g) := by
    refine mem_of_fwdFit hfit'.1.1.1.1 hb ?_
    rw [asks_k5 h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have h0 := hT.2.2.2.1 (ds ++ ds') _ hop
  have h1 := planes_item_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
    (open8_at hg) (open_k5 hg _ (by simp)) hr hu hon e hh
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).strs E)
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).strs (E.add y.1)) h0
  show (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).means y.2.st.input _
    (y.2.st.input.x.pub, behind s att hd5 G)
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).strs (E.add y.1))
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).wit k y.2.st.input
      (y.2.st.heard ++ ds'))
  rw [ei, eh, List.append_assoc]
  exact h1

/-- **THE DEBT `Exchange` AT THE KIND's MEMBER OF GROUP g**: the six items that its row owes hold
behind its step, at every continuation. CONDITIONAL: under the hypothesis h, the test on the
letters, `K5Seated`, the letter ans at the first sending's tenants, and the two named premises
`SayOwed`, `JoinOwed`, WHICH HOLD THE CLAUSES ON VALUES of two of the six. -/
theorem k5_exchange {n : Nat} {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a)
    (hJ : JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a) :
    Exchange (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' i hi
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  rw [owes_k5 h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg] at hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact own_at_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hT hd hS
      (hSay blk k s s' m E ds y cols Hs.member hT hd hS) ds' _ (List.mem_singleton.2 rfl)
  rcases List.mem_cons.1 hi with rfl | hi
  · exact planes_at_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hfit hb
      hT hd hS ds' _ (List.mem_singleton.2 rfl)
  rcases List.mem_cons.1 hi with rfl | hi
  · exact join_at_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hJ hT hd
      hS ds' _ (List.mem_singleton.2 rfl)
  exact k5_ctx_owed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hfit hb ha Hs hans
    hT hd hS ds' i hi

/-- **THE MEMBER's DEBTS IN ONE STATEMENT**: it plays; behind its yes; the exchange; it is accepted,
for every fall. CONDITIONAL: under all premises of `k5_behind` and `k5_exchange`. The riders' debt
is not among them. -/
theorem k5_owes {n : Nat} {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a)
    (hJ : JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a) :
    Plays (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Behind (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Exchange (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      ∀ fall, Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
        (borderOf g) :=
  ⟨k5_plays _ Hs,
    k5_behind h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs Kp Rd,
    k5_exchange h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hfit hb hans
      hSay hJ,
    k5_accepted h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.owes_k5
#print axioms ProofFile.Honest.K5.asks_k5
#print axioms ProofFile.Honest.K5.join_at_thr
#print axioms ProofFile.Honest.K5.planes_at_thr
#print axioms ProofFile.Honest.K5.k5_exchange
#print axioms ProofFile.Honest.K5.k5_owes
