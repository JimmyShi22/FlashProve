-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/AllT2.lean: CONDITIONAL: the twins, WITHOUT THE PREMISE
`IdnOwed` (the input's cells meet the library's three families of identities), of the share "own" of
`Exchange`, of `Exchange` whole, and of all the debts of the member at an attention segment's own
rounds (kind K5) in one statement, WITH THE `Thread` T A VARIABLE.

In that premise's stead stands hH: `HoldsOwed` T.valid cq (Honest/K5/Law/Idn12/AskedT.lean). Every
twin takes it by that name.

  `k5_share_own_T₂`        CONDITIONAL: the share at `formsT l 3 "own"` (l := 2 g + 1). AGAINST
                           `k5_share_own_T` (Honest/K5/Law/SharesT.lean): `IdnOwed` IS GONE; THE
                           TEST T.fits AND `HoldsOwed` HAVE COME
  `k5_exchange_shares_T₂`  CONDITIONAL: `Exchange` T b out of that share and the five others
  `k5_owes_all_T₂`         CONDITIONAL: **all debts**, T.keeps tied to `K5Keeps` (Kp, Rd,
                           `K5RidersT`)

Limits. Every theorem is conditional. TWO PREMISES BEAR ON VALUES: Sc (`K5Script`): NOT SHOWN;
hH (`HoldsOwed`): SHOWN OF NO `valid`. THE WEIGHT OF `IdnOwed` HAS MOVED, NOT GONE: that the
identities hold now comes from three items that `Thr` T holds in front of the member, of T's own
witness: whoever shows that a run meets `Thr` T there owes them. hans and hidx are sentences on the
letter ans, which has no text here. The hypothesis `P5J.AtMgA` is not shown here. At a T.valid that
no input meets every premise can hold, and the statements then say nothing. One member of the chain.
At the library's full size and the format's second hash function alone. The older laws stand beside these.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Idn12.SayOwedT2
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesT

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place OpenedColumn Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (mgBase mgAll seatTab)
open VerifiableInference.Desc.First.Att.P
open H2K5.Honest (own_at_head K5Keeps)
open ProofFile.Honest.FirstThread (WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (A : K5AtT h T g it pb wt ans test carryX cq)
include A

/-- **THE SHARE "own", WITHOUT `IdnOwed`.** T IS A VARIABLE. CONDITIONAL: under the hypothesis h,
`K5AtT`, `K5Seated`, the test T.fits, hP, and two premises that bear on values and that are not
shown: Sc (`K5Script`), hH (`HoldsOwed`). -/
theorem k5_share_own_T₂ {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hH : HoldsOwed T.valid cq) :
    ExchangeAt T (borderOf g) (it (.formsT (2 * g + 1) 3 "own")) := by
  intro blk' hblk' k s m E ds y cols s' hT hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  have hSay := sayOwedT_of₂ h A hg ha Hs hfit hb Sc hP hH blk k s s' m E ds y cols Hs.member hT hd
    hS ds'
  refine (A.means _ (Or.inr List.mem_cons_self) _ _ _ _).2 ?_
  obtain ⟨Pl, Dc⟩ := decides_T h A hg ha Hs.member
  obtain ⟨att, hd5, G, e, hh, rfl⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h A hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← A.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h A (Nat.le_of_lt hlt) hT
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have hp : pb (T.seat k y.2 (behind s att hd5 G)).1 = m.st.input.x.pub := by
    rw [← ei]
    exact A.handed _ _ _
  rw [hp]
  obtain ⟨att', gL, e', hgL, -⟩ := (readyO_T h A hg Pl hT).open_
  rw [e] at e'
  cases e'
  exact ⟨own_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr hu
    hon e hh h.𝔇.St _ hgL (hSay att hd5 G gL e hgL rfl), fun hw => nomatch hw⟩

/-- **`Exchange` T b OUT OF ITS SIX SHARES, WITHOUT `IdnOwed`.** T IS A VARIABLE. CONDITIONAL: the
union of the six shares' premises. -/
theorem k5_exchange_shares_T₂ {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hH : HoldsOwed T.valid cq) :
    Exchange T (borderOf g) := by
  refine (exchange_iff T).2 fun j hj => ?_
  rw [A.owes] at hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
  unfold owed6 at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact k5_share_own_T₂ h A hg ha Hs hfit hb Sc hP hH
  · exact k5_share_planes_T h A hg ha Hs hfit hb
  · exact k5_share_join_T h A hg ha Hs hfit hb Sc hP
  · exact k5_share_pin_T h A hg ha Hs hfit hb hans
  · exact k5_share_pinW_T h A hg ha Hs hfit hb
  · exact k5_share_small_T h A hg ha Hs hfit hb

/-- **ALL OF THE MEMBER's DEBTS IN ONE STATEMENT, WITHOUT `IdnOwed`**, T.keeps tied to `K5Keeps`. T
IS A VARIABLE. CONDITIONAL: as `k5_owes_all_T` (Honest/K5/Law/RidesT.lean), with hH in hV's stead.
It bears on values through Sc and hH, and through what `Thr` T holds of the asked items in front;
none of these is shown. -/
theorem k5_owes_all_T₂ (R : K5RidersT h T g it pb wt ans test carryX cq) {n : Nat}
    (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → T.keeps (borderOf g) s s')
    (Rd : ∀ w s s', T.rides (borderOf g) w s → K5Keeps s s' → T.rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hidx : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g)))
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hH : HoldsOwed T.valid cq) :
    (Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      RidesPast T (borderOf g)) ∧ ∀ fall, Accepted T fall (borderOf g) :=
  ⟨⟨k5_plays T Hs, k5_behind_T h A hg ha Hs Kp Rd,
      k5_exchange_shares_T₂ h A hg ha Hs hfit hb hans Sc hP hH, k5_ridesPast_T h hg A R hidx⟩,
    fun fall => k5_accepted_T h A hg ha Hs fall⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_share_own_T₂
#print axioms ProofFile.Honest.K5.k5_exchange_shares_T₂
#print axioms ProofFile.Honest.K5.k5_owes_all_T₂
