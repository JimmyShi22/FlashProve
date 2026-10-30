-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SharesT.lean: CONDITIONAL: the debts `Exchange` and `RidesPast`
of the member at an attention segment's own rounds (kind K5) SHARE BY SHARE: at one item each
(`ExchangeAt`, `RidesPastAt`, Honest/Thread/Shares.lean), WITH THE `Thread` T A VARIABLE, each share
of `Exchange` under its own premises and no others; the shares of `RidesPast` under one list of
premises for all riding sorts.

THE SIX SHARES OF `Exchange` (l := 2 g + 1), each beside the hypothesis h, the structure `K5AtT`
(Honest/K5/Law/AtT.lean) and `K5Seated` (Honest/K5/Law/Seated.lean):
  `k5_share_own_T`      `formsT l 3 "own"`: under `K5Script`, `IdnOwed` T.valid: BOTH BEAR ON VALUES
  `k5_share_planes_T`   `formsT l 2 "planes"`: under the test T.fits alone: from the item "the
                        planes' worth", which the row asks in front
  `k5_share_join_T`     `formsT l 2 "join"`: under T.fits and `K5Script`: IT BEARS ON VALUES
  `k5_share_pin_T`      `pin l 0`: under T.fits and `AnsReadsRest`
  `k5_share_pinW_T`     `pinW`: under T.fits alone
  `k5_share_small_T`    `constr l small`: under T.fits alone
The last three are read in front and owed again (`again_T`).

THE SHARES OF `RidesPast`:
  `k5_ridesPastAt_T`    at every item of the riding sorts (the digits' part aside): under the two
                        structures and `AnsOn` (`riders_go_at_head`, Honest/K5/Law/RidesPast.lean)
`RidesPastAt` asks more than the debt: it has no premise "the item is open at the border". So it is
not drawn from `RidesPast` T b here, but from the law on the riders itself.

Limits. Every theorem is conditional. The hypothesis `P5J.AtMgA` is not shown here; `K5Script` is
shown by nobody; `IdnOwed` of no `valid`; `AnsReadsRest` and `AnsOn` of no ans here. At the
library's full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.ProofFile.Honest.K5.Law.WholeT
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesPast

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place OpenedColumn Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (mgBase mgAll seatTab)
open VerifiableInference.Desc.First.Att.P
open H2K5.Honest (own_at_head join_at_head planes_item_at_head K5Keeps)
open ProofFile.Honest.FirstThread (WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (R : K5AtT h T g it pb wt ans test carryX cq)
include R

/-- What the kind's row asks is open at T's border. CONDITIONAL: the structure (T.row); the test
T.fits up to a number beyond the border. -/
theorem asked_open_T {n : Nat} (hfit : T.fits n = true) (hb : borderOf g < n) (q : Item)
    (hq : q ∈ asked7 (2 * g + 1)) : it q ∈ T.opened (borderOf g) := by
  unfold Thread.fits at hfit
  simp only [Bool.and_eq_true] at hfit
  exact mem_of_fwdFit hfit.1.1.1.1 hb (by rw [R.asks]; exact List.mem_map.2 ⟨q, hq, rfl⟩)

/-- **THE SHARE "own".** T IS A VARIABLE. CONDITIONAL: under the hypothesis h, `K5AtT`, `K5Seated`,
and the two premises that bear on values: Sc (`K5Script`), hV (`IdnOwed` T.valid); hP: the public
data hold the plan's shape and numbers. -/
theorem k5_share_own_T (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hV : IdnOwed T.valid cells Z5) :
    ExchangeAt T (borderOf g) (it (.formsT (2 * g + 1) 3 "own")) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  have hSay := sayOwedT_of h R hg ha Hs Sc hP hV blk k s s' m E ds y cols Hs.member hT hd hS ds'
  refine (R.means _ (Or.inr List.mem_cons_self) _ _ _ _).2 ?_
  obtain ⟨Pl, Dc⟩ := decides_T h R hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← R.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h R (Nat.le_of_lt hlt) hT
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have hp : pb (T.seat k y.2 (behind s att hd5 G)).1 = m.st.input.x.pub := by
    rw [← ei]
    exact R.handed _ _ _
  rw [hp]
  obtain ⟨att', gL, e', hgL, -⟩ := (readyO_T h R hg Pl hT).open_
  rw [e] at e'
  cases e'
  exact ⟨own_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr hu
    hon e hh h.𝔇.St _ hgL (hSay att hd5 G gL e hgL rfl), fun hw => nomatch hw⟩

/-- **THE SHARE "planes".** T IS A VARIABLE. CONDITIONAL: under the hypothesis h, `K5AtT`,
`K5Seated` and the test T.fits. No premise bears on values: it is had from the item "the planes'
worth", which the row asks in front and `Thr` T holds there. -/
theorem k5_share_planes_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n) :
    ExchangeAt T (borderOf g) (it (.formsT (2 * g + 1) 2 "planes")) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  have hq : Item.worth (2 * g + 1) 2 "planes" ∈ asked7 (2 * g + 1) :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have h0 := (R.means _ (Or.inl hq) _ _ _ _).1
    (hT.2.2.2.1 (ds ++ ds') _ (asked_open_T h R hfit hb _ hq))
  have hp0 : pb (T.seat k m s).1 = m.st.input.x.pub := R.handed _ _ _
  rw [hp0] at h0
  refine (R.means _ (Or.inr (List.mem_cons_of_mem _ List.mem_cons_self)) _ _ _ _).2 ?_
  obtain ⟨Pl, Dc⟩ := decides_T h R hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← R.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h R (Nat.le_of_lt hlt) hT
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have hp : pb (T.seat k y.2 (behind s att hd5 G)).1 = m.st.input.x.pub := by
    rw [← ei]
    exact R.handed _ _ _
  rw [hp]
  have eh := play_heard _ _ _ _ _ hy
  have h1 := planes_item_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
    (open8_at hg) (open_k5 hg _ (by simp)) hr hu hon e hh (T.strs E) (T.strs (E.add y.1)) h0
  rw [ei, eh, List.append_assoc]
  exact h1

/-- **THE SHARE "join".** T IS A VARIABLE. CONDITIONAL: under the hypothesis h, `K5AtT`, `K5Seated`,
the test T.fits, and Sc (`K5Script`), which bears on values; hP. -/
theorem k5_share_join_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) :
    ExchangeAt T (borderOf g) (it (.formsT (2 * g + 1) 2 "join")) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  have hJ := joinOwedT_script h R hg ha Hs hfit hb Sc hP blk k s s' m E ds y cols Hs.member hT hd
    hS ds'
  refine (R.means _ (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    _ _ _ _).2 ?_
  obtain ⟨Pl, Dc⟩ := decides_T h R hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← R.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h R (Nat.le_of_lt hlt) hT
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have hp : pb (T.seat k y.2 (behind s att hd5 G)).1 = m.st.input.x.pub := by
    rw [← ei]
    exact R.handed _ _ _
  rw [hp]
  exact ⟨join_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr hu
    hon e hh h.𝔇.St _ (hJ att hd5 G e rfl), fun hw => nomatch hw⟩

/-- **An item that the kind's row reads and owes again**: its share. T IS A VARIABLE. CONDITIONAL:
under the hypothesis h, `K5AtT`, `K5Seated`, the test T.fits; hgo: what the item's own sentence says
of a state it says of every state that `K5Keeps` ties to it, at the same strings and witness. -/
theorem again_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n) (j : Item)
    (hj : j ∈ [Item.pin (2 * g + 1) 0, Item.pinW, Item.constr (2 * g + 1) .small])
    (hgo : ∀ (c : CellsM OnBytes.Flat.numsFull) (π : ProofFile.InstPub) (s s' : TS) (y : Strs) (v : WtF),
      K5Keeps s s' →
      Item.holds (P5J.At.N Zp cF)
        (honest (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase) ans test)
        j (π, s) y v →
      Item.holds (P5J.At.N Zp cF)
        (honest (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase) ans test)
        j (π, s') y v) :
    ExchangeAt T (borderOf g) (it j) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  have hK := keeps_T h R hg ha Hs hT hd hS
  have hq : j ∈ asked7 (2 * g + 1) :=
    List.mem_append_right [Item.constr (2 * g + 1) .idn, .worth (2 * g + 1) 2 "planes",
      .worth (2 * g + 1) 2 "keys", .worth (2 * g + 1) 2 "rider"] hj
  have hw : j ∈ owed6 (2 * g + 1) :=
    List.mem_append_right [Item.formsT (2 * g + 1) 3 "own", .formsT (2 * g + 1) 2 "planes",
      .formsT (2 * g + 1) 2 "join"] hj
  have h0 := (R.means _ (Or.inl hq) _ _ _ _).1
    (hT.2.2.2.1 (ds ++ ds') _ (asked_open_T h R hfit hb _ hq))
  have hp0 : pb (T.seat k m s).1 = m.st.input.x.pub := R.handed _ _ _
  rw [hp0] at h0
  refine (R.means _ (Or.inr hw) _ _ _ _).2 ?_
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hp : pb (T.seat k y.2 s').1 = m.st.input.x.pub := by
    rw [← ei]
    exact R.handed _ _ _
  have hE := (k5_env _ Hs hd hT.2.2.2.2.1.2.2.2.1 hS.1).1
  have h1 := hgo (cq m.st.input) _ _ _ _ _ hK h0
  rw [hp, hE, ei, eh, List.append_assoc]
  exact h1

/-- **THE SHARE OF THE FIRST SENDING's PIN.** T IS A VARIABLE. CONDITIONAL: under the hypothesis h,
`K5AtT`, `K5Seated`, the test T.fits, and `AnsReadsRest` at that sending's tenants. -/
theorem k5_share_pin_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0)) :
    ExchangeAt T (borderOf g) (it (.pin (2 * g + 1) 0)) :=
  again_T h R hg ha Hs hfit hb _ List.mem_cons_self fun c π _ _ y v hK hm =>
    ctx_rides_head h ans test carryX c hg hK hans π y v _ List.mem_cons_self hm

/-- **THE SHARE OF THE STORED TABLE's PIN.** T IS A VARIABLE. CONDITIONAL: under the hypothesis h,
`K5AtT`, `K5Seated` and the test T.fits. At the honest letters its sentence reads nothing of the
verifier's state. -/
theorem k5_share_pinW_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n) : ExchangeAt T (borderOf g) (it .pinW) :=
  again_T h R hg ha Hs hfit hb _ (List.mem_cons_of_mem _ List.mem_cons_self)
    fun _ _ _ _ _ _ _ hm => hm

/-- **THE SHARE "every cell of the segment is small".** T IS A VARIABLE. CONDITIONAL: under the
hypothesis h, `K5AtT`, `K5Seated` and the test T.fits. -/
theorem k5_share_small_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n) :
    ExchangeAt T (borderOf g) (it (.constr (2 * g + 1) .small)) :=
  again_T h R hg ha Hs hfit hb _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    fun c π _ _ y v hK hm =>
      ctx_rides_head h (fun _ _ _ _ _ => True) test carryX c hg hK
        (fun _ _ _ _ _ _ _ _ _ => trivial) π y v _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hm

/-- **A SHARE OF THE RIDERS' DEBT: AT EVERY ITEM OF THE RIDING SORTS**, the digits' part aside. T IS
A VARIABLE. CONDITIONAL: under the hypothesis h, the two structures `K5AtT` and `K5RidersT`, and
`AnsOn` at the index masks' tenant, which the index masks' pin alone spends. -/
theorem k5_ridesPastAt_T (Rr : K5RidersT h T g it pb wt ans test carryX cq) (hg : g < 12)
    (hidx : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g))) (i : Item)
    (hi : i = .unmarked ∨ riderB (2 * g + 1) i = true) (hd : ∀ n, i ≠ .constr n .lookDigits) :
    RidesPastAt T (borderOf g) (it i) := by
  intro k s m E s' ps v hT hk hm
  obtain ⟨blk, -, hb, -, -⟩ := k5_member h hg
  have hr := reach_T h R (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have h0 := (Rr.means i hi _ _ _ _).1 hm
  refine (Rr.means i hi _ _ _ _).2 ?_
  have hp : pb (T.seat k m s).1 = m.st.input.x.pub := R.handed _ _ _
  have hp' : pb (T.seat k m s').1 = m.st.input.x.pub := R.handed _ _ _
  have hs : E.sent = treesTo cF.blocksInOrder (borderOf g) := by
    rw [← R.bs]
    exact hT.2.2.2.2.1.2.2.1
  have hY := Rr.strs E ps
  rw [hs] at hY
  rw [hp] at h0
  rw [hp']
  exact riders_go_at_head h hg (cq m.st.input) hidx i hi hd _ s s' _ _ _ hr hu hon
    (Rr.keeps s s' hk) hY h0

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.asked_open_T
#print axioms ProofFile.Honest.K5.k5_share_own_T
#print axioms ProofFile.Honest.K5.k5_share_planes_T
#print axioms ProofFile.Honest.K5.k5_share_join_T
#print axioms ProofFile.Honest.K5.again_T
#print axioms ProofFile.Honest.K5.k5_share_pin_T
#print axioms ProofFile.Honest.K5.k5_share_pinW_T
#print axioms ProofFile.Honest.K5.k5_share_small_T
#print axioms ProofFile.Honest.K5.k5_ridesPastAt_T
