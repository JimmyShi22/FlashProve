-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KeepsMT.lean: CONDITIONAL: the clause `K5KeepsM`
(Johnson/Desc/K5/Honest/Law/KeepsM.lean: what an accepting step of the kind "an attention segment's
own rounds" (K5) leaves, with "no mark behind" inside) AS THE MEMBER's CLAUSE OF T.keeps: its payer
from the whole member's accepting step, and the debts that spend T.keeps, stated anew over it, WITH
THE `Thread` T A VARIABLE.

WHY THE DEBTS ARE STATED ANEW. The laws so far tie T.keeps at the border to the older clause
`K5Keeps`, in two directions: `Behind` takes "`K5Keeps` gives T.keeps" (Kp), the riders take
"T.keeps gives `K5Keeps`" (`K5RidersT`, its field keeps). AT A T.keeps THAT IS `K5KeepsM` NO LEMMA
THAT LIES PAYS EITHER: `K5Keeps` says of the mark only that it is as it was; and `K5KeepsM` is shown
to give `K5Keeps` only where the ledger in front has its arrays' lengths. Both close where they are
spent: behind the member's own step `K5KeepsM` holds outright (`keepsM_T`); and a rider's filler has
`Thr` T in front, which gives these lengths (`keeps_of_M_T`).

  1  `k5KeepsM_of_step`       CONDITIONAL: **THE PAYER**: the whole member's accepting step
                              (`StepYes`, Johnson/Top/H0/Walk/Reach.lean) gives the clause; nothing
                              is asked of the state in front
     `k5KeepsM_payer_T`       the same at T's member, T a variable
     `k5KeepsM_payer_head`, `k5KeepsAt_payer_head`   the same at the hypothesis's own flat list; by
                              the member's place
  2  `keepsM_T`               behind the member's step in a `Thread`
     `keeps_of_M_T`           **`Thr` T in front and `K5KeepsM` give `K5Keeps`**
  3  `k5_behind_M_T`          **`Behind` T b** under KpM, RdM: the two premises on T.keeps and
                              T.rides over `K5KeepsM`
  4  `K5RidersM`              `K5RidersT` with its field keeps over `K5KeepsM`
     `k5RidersM_thrAt`        the first `Thread` at the library's own letters meets it
     `k5_ridesPastAt_M_T`, `k5_ridesPast_M_T`   **the riders' debt**, by the share and whole
  5  `k5_exchange_shares_T`   `Exchange` T b out of its six shares (Honest/K5/Law/SharesT.lean)
     `k5_owes_all_M_T`        **ALL OF THE MEMBER's DEBTS IN ONE STATEMENT** over `K5KeepsM`

Limits. Every theorem is conditional. The hypothesis `P5J.AtMgA` is not shown here. `K5Script` is
shown by nobody, `IdnOwed` of no `valid`. At the library's full size and the format's second hash function
alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.KeepsM
import Johnson.Desc.ProofFile.Honest.K5.Law.SharesT
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place OpenedColumn Strs Chain Claim First.S)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (mgBase mgAll seatTab)
open VerifiableInference.Desc.First.Att.P
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)
open H2K5.Honest (K5Keeps K5KeepsM K5KeepsAt k5KeepsAt_iff k5KeepsM_of_decide k5Keeps_of_M)
open ProofFile.Honest.FirstThread (Script WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

/-! ## 1 The payer -/

/-- **THE WHOLE MEMBER's ACCEPTING STEP GIVES THE CLAUSE.** CONDITIONAL: blk decides as the kind's
own decision with two tests more (`DecidesAs`, Honest/K5/Law/Member.lean); the step's yes. Nothing
is asked of the state in front. -/
theorem k5KeepsM_of_step {p : Par} {blk : Block First.S Claim} (Dc : DecidesAs p blk) {ft : Nat}
    {s s' : First.S} (hy : StepYes ft blk s s') : K5KeepsM p.own s s' := by
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  obtain ⟨h1, h2, -⟩ := (Dc.decides s s' rs gs).1 hd
  exact k5KeepsM_of_decide p h1 h2

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **The payer at the hypothesis's own flat list.** CONDITIONAL: under the hypothesis h; g is below
12; the group's plan. -/
theorem k5KeepsM_payer_head {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) (blk : Block TS ProofFile.Cl)
    (hb : cF.blocksInOrder[borderOf g]? = some blk) (t t' : TS) (hy : StepYes 0 blk t t') :
    K5KeepsM a.own t t' :=
  k5KeepsM_of_step (seated_decides h hg ha hb).2 hy

/-- **The payer by the member's place.** CONDITIONAL: under the hypothesis h; g is below 12. -/
theorem k5KeepsAt_payer_head {g : Nat} (hg : g < 12) (blk : Block TS ProofFile.Cl)
    (hb : cF.blocksInOrder[borderOf g]? = some blk) (t t' : TS) (hy : StepYes 0 blk t t') :
    K5KeepsAt (P5J.At.X Zp) blk.place t t' := by
  obtain ⟨blk', a, hb', Pl, Dc⟩ := k5_member h hg
  obtain rfl : blk' = blk := Option.some.inj (hb'.symm.trans hb)
  rw [Dc.place]
  exact (k5KeepsAt_iff Pl.plan t t').2 (k5KeepsM_of_step Dc hy)

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (A : K5AtT h T g it pb wt ans test carryX cq)
include A

/-- **THE PAYER AT T's MEMBER.** T IS A VARIABLE. CONDITIONAL: under the hypothesis h and `K5AtT`
(of it: T.bs); g is below 12; the group's plan. -/
theorem k5KeepsM_payer_T (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a)
    (blk : Block TS ProofFile.Cl) (hb : T.bs[borderOf g]? = some blk) (s s' : TS)
    (hy : StepYes T.ft blk s s') : K5KeepsM a.own s s' :=
  k5KeepsM_of_step (decides_T h A hg ha hb).2 hy

/-! ## 2 In a `Thread` -/

/-- **Behind the member's step in a `Thread` the clause holds.** T IS A VARIABLE. CONDITIONAL: under
the hypothesis h, `K5AtT`, `K5Seated`; challenges that fit; the step. `Thr` T is not spent. -/
theorem keepsM_T (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hd : drawsFit blk.rounds ds = true) (hS : T.Stepped blk k s m E ds y cols s') :
    K5KeepsM a.own s s' := by
  obtain ⟨-, Dc⟩ := decides_T h A hg ha Hs.member
  have hf := form_behind _ Hs Dc hd hS
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  exact ⟨hf, att, hd5, G, _, e, hh, rfl⟩

/-- **`Thr` T IN FRONT AND THE CLAUSE GIVE THE OLDER CLAUSE.** T IS A VARIABLE. CONDITIONAL: under
the hypothesis h and `K5AtT`; g is below 12. The promise in front, which `Thr` T holds, says that
the open ledger has its arrays' lengths. -/
theorem keeps_of_M_T (hg : g < 12) {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr T (borderOf g) k s m E)
    {o : Params.AttentionRounds} (K : K5KeepsM o s s') : K5Keeps s s' := by
  obtain ⟨-, a, -, Pl, -⟩ := k5_member h hg
  obtain ⟨att, gL, e, -, -, hz, -⟩ := (readyO_T h A hg Pl hT).open_
  refine k5Keeps_of_M K fun a' e' => ?_
  rw [e] at e'
  cases e'
  exact hz

/-! ## 3 `Behind` -/

/-- **THE DEBT `Behind` OVER THE CLAUSE.** T IS A VARIABLE. CONDITIONAL: under the hypothesis h,
`K5AtT`, `K5Seated`, and two premises on letters: KpM: the clause gives T.keeps at the border; RdM:
T.rides goes from the border to the next along the clause. -/
theorem k5_behind_M_T (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (KpM : ∀ s s', K5KeepsM a.own s s' → T.keeps (borderOf g) s s')
    (RdM : ∀ w s s', T.rides (borderOf g) w s → K5KeepsM a.own s s' →
      T.rides (borderOf g + 1) w s') : Behind T (borderOf g) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  obtain ⟨-, Dc⟩ := decides_T h A hg ha Hs.member
  have hK := keepsM_T h A hg ha Hs hd hS
  have hf := form_behind _ Hs Dc hd hS
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  obtain ⟨hu, hon⟩ := onAt_T h A hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← A.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h A (Nat.le_of_lt hlt) hT
  refine ⟨⟨?_, ?_⟩, ?_, KpM _ _ hK⟩
  · rw [A.form _ (Or.inr rfl)]
    show (behind s att hd5 G).failed.isNone = true
    rw [hf]
    rfl
  · refine (A.formP _ (Or.inr rfl) _).2 ?_
    have hp : pb (T.seat k y.2 (behind s att hd5 G)).1 = m.st.input.x.pub := by
      rw [← ei]
      exact A.handed _ _ _
    rw [hp]
    exact next_of_front h ans test hg ha hr hu hon e hh
  · rw [ei]
    exact RdM _ _ _ hT.2.2.2.2.2.1 hK

end

/-! ## 4 The riders -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}

/-- **THE STRUCTURE FOR THE RIDERS, OVER THE CLAUSE**: `K5RidersT` (Honest/K5/Law/RidersT.lean) with
its field keeps turned: T.keeps at the border gives `K5KeepsM` at the numbers o. It is a definition:
a list of premises on T's letters. -/
structure K5RidersM
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (g : Nat) (it : Item → T.ι) (pb : T.P → ProofFile.InstPub) (wt : T.Wt → WtF)
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull)
    (o : Params.AttentionRounds) : Prop where
  /-- T.opened and T.row at the border: which items ride -/
  riders : ∀ j ∈ T.opened (borderOf g), j ∉ (T.row (borderOf g)).shuts →
    j ∉ (T.row (borderOf g)).owes →
    ∃ i, j = it i ∧ (i = .unmarked ∨ riderB (2 * g + 1) i = true) ∧
      ∀ n, i ≠ .constr n .lookDigits
  /-- T.means at the riding sorts: the table's own sentence, at the honest letters over the
  library's filling with the two fields laid -/
  means : ∀ i, (i = .unmarked ∨ riderB (2 * g + 1) i = true) → ∀ w a y v,
    T.means w (it i) a y v ↔
      Item.holds (P5J.At.N Zp cF)
        (honest (mgAll { h.𝔇 with decT := fun _ _ => some (cq w), cr1 := carryX } mgBase) ans test)
        i (pb a.1, a.2) y (wt v)
  /-- T.keeps at the border -/
  keeps : ∀ s s', T.keeps (borderOf g) s s' → K5KeepsM o s s'
  /-- T.strs: what rounds that were played leave of the strings -/
  strs : ∀ E ps, StrsKept E.sent (T.strs E) (T.strs (E.add ps))

end

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

/-- **The first `Thread` at the library's own letters meets the structure.** CONDITIONAL: g is below
12; Kq: its letter keeps at the border gives the clause. -/
theorem k5RidersM_thrAt {g : Nat} (hg : g < 12) {o : Params.AttentionRounds}
    (Kq : ∀ s s', keeps (borderOf g) s s' → K5KeepsM o s s') :
    K5RidersM h (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) g
      (fun i => i) (fun p => p) (fun v => v) ans test carryX Q.cells o :=
  { riders := fun j ho h1 h2 =>
      ⟨j, rfl,
        riders_thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg j ho h1 h2,
        no_digits_thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg j ho⟩
    means := fun _ _ _ _ _ _ => Iff.rfl
    keeps := Kq
    strs := fun E ps => strsKept_add item n₁ n₂ E ps }

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (A : K5AtT h T g it pb wt ans test carryX cq)
include A

/-- **A SHARE OF THE RIDERS' DEBT OVER THE CLAUSE: AT EVERY ITEM OF THE RIDING SORTS**, the digits'
part aside. T IS A VARIABLE. CONDITIONAL: under the hypothesis h, `K5AtT`, `K5RidersM`, and `AnsOn`
at the index masks' tenant, which the index masks' pin alone spends. -/
theorem k5_ridesPastAt_M_T {o : Params.AttentionRounds}
    (R : K5RidersM h T g it pb wt ans test carryX cq o) (hg : g < 12)
    (hidx : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g))) (i : Item)
    (hi : i = .unmarked ∨ riderB (2 * g + 1) i = true) (hd : ∀ n, i ≠ .constr n .lookDigits) :
    RidesPastAt T (borderOf g) (it i) := by
  intro k s m E s' ps v hT hk hm
  obtain ⟨blk, -, hb, -, -⟩ := k5_member h hg
  have hr := reach_T h A (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  obtain ⟨hu, hon⟩ := onAt_T h A hg hT
  have h0 := (R.means i hi _ _ _ _).1 hm
  refine (R.means i hi _ _ _ _).2 ?_
  have hp : pb (T.seat k m s).1 = m.st.input.x.pub := A.handed _ _ _
  have hp' : pb (T.seat k m s').1 = m.st.input.x.pub := A.handed _ _ _
  have hs : E.sent = treesTo cF.blocksInOrder (borderOf g) := by
    rw [← A.bs]
    exact hT.2.2.2.2.1.2.2.1
  have hY := R.strs E ps
  rw [hs] at hY
  rw [hp] at h0
  rw [hp']
  exact riders_go_at_head h hg (cq m.st.input) hidx i hi hd _ s s' _ _ _ hr hu hon
    (keeps_of_M_T h A hg hT (R.keeps s s' hk)) hY h0

/-- **THE RIDERS' DEBT OVER THE CLAUSE.** T IS A VARIABLE. CONDITIONAL: as `k5_ridesPastAt_M_T`. -/
theorem k5_ridesPast_M_T {o : Params.AttentionRounds}
    (R : K5RidersM h T g it pb wt ans test carryX cq o) (hg : g < 12)
    (hidx : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g))) :
    RidesPast T (borderOf g) :=
  ridesPast_of T fun j hj hs ho => by
    obtain ⟨i, rfl, hi, hd⟩ := R.riders j hj hs ho
    exact k5_ridesPastAt_M_T h A R hg hidx i hi hd

/-! ## 5 All debts -/

/-- **`Exchange` T b OUT OF ITS SIX SHARES.** T IS A VARIABLE. CONDITIONAL: the union of the six
shares' premises. -/
theorem k5_exchange_shares_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hV : IdnOwed T.valid cells Z5) : Exchange T (borderOf g) := by
  refine (exchange_iff T).2 fun j hj => ?_
  rw [A.owes] at hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
  unfold owed6 at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact k5_share_own_T h A hg ha Hs Sc hP hV
  · exact k5_share_planes_T h A hg ha Hs hfit hb
  · exact k5_share_join_T h A hg ha Hs hfit hb Sc hP
  · exact k5_share_pin_T h A hg ha Hs hfit hb hans
  · exact k5_share_pinW_T h A hg ha Hs hfit hb
  · exact k5_share_small_T h A hg ha Hs hfit hb

/-- **ALL OF THE MEMBER's DEBTS IN ONE STATEMENT, OVER THE CLAUSE WITH THE MARK INSIDE, WITH T A
VARIABLE**: it plays; behind its yes; the exchange; the riders; it is accepted, for every fall.
CONDITIONAL: as `k5_owes_all_T` (Honest/K5/Law/RidesT.lean), with KpM, RdM and `K5RidersM` in the
stead of Kp, Rd and `K5RidersT`. It bears on values through Sc and hV; neither is shown; hans
and hidx are sentences on the letter ans, which has no text here. -/
theorem k5_owes_all_M_T {a : Attention.Plan}
    (R : K5RidersM h T g it pb wt ans test carryX cq a.own) {n : Nat} (hg : g < 12)
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (KpM : ∀ s s', K5KeepsM a.own s s' → T.keeps (borderOf g) s s')
    (RdM : ∀ w s s', T.rides (borderOf g) w s → K5KeepsM a.own s s' →
      T.rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hidx : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g)))
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hV : IdnOwed T.valid cells Z5) :
    (Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      RidesPast T (borderOf g)) ∧ ∀ fall, Accepted T fall (borderOf g) :=
  ⟨⟨k5_plays T Hs, k5_behind_M_T h A hg ha Hs KpM RdM,
      k5_exchange_shares_T h A hg ha Hs hfit hb hans Sc hP hV, k5_ridesPast_M_T h A R hg hidx⟩,
    fun fall => k5_accepted_T h A hg ha Hs fall⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5KeepsM_of_step
#print axioms ProofFile.Honest.K5.k5KeepsM_payer_head
#print axioms ProofFile.Honest.K5.k5KeepsAt_payer_head
#print axioms ProofFile.Honest.K5.k5KeepsM_payer_T
#print axioms ProofFile.Honest.K5.keepsM_T
#print axioms ProofFile.Honest.K5.keeps_of_M_T
#print axioms ProofFile.Honest.K5.k5_behind_M_T
#print axioms ProofFile.Honest.K5.k5RidersM_thrAt
#print axioms ProofFile.Honest.K5.k5_ridesPastAt_M_T
#print axioms ProofFile.Honest.K5.k5_ridesPast_M_T
#print axioms ProofFile.Honest.K5.k5_exchange_shares_T
#print axioms ProofFile.Honest.K5.k5_owes_all_M_T
