-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/RiderT.lean: CONDITIONAL: the batch of the library's
third family of identities on an attention segment, at the point that the lookup on the calls heard,
IS 0 AT THE CELLS OF THE RUN's OWN INPUT: drawn from an item that the row of the segment's own
rounds (kind K5) asks in front, WITH THE `Thread` T A VARIABLE.

Why. The laws on the values of the kind spend the third family at one place alone, and there through
that batch (`Rider`, Johnson/Desc/K5/Honest/Law/Idn.lean). The row asks the item "the rider's worth"
in front; `Thr` T holds it there of T's own witness; the tie of the witness's cells to the trace's
(`K5Script`, its field `cellsTie`) carries it to the input's cells, and the tie on the key points
(its field `keyTie`) says that the point is the one that the state holds.

  `rider_T`   CONDITIONAL: **`Rider` at the input's cells**, from `Thr` T in front
              (`rider_item_at_head`, Johnson/Desc/K5/Honest/Law/RiderOfAsked.lean)

THE PREMISES: the hypothesis h · `K5AtT` · g below 12, the group's plan · `K5Seated` · the test
T.fits (what the row asks is open) · Sc: `K5Script`: NOT SHOWN · hP · `Thr` T at the
border · an attention segment stands open, and holds what the lookup heard.

Limits. Conditional. It says nothing of the third family on the cube: the batch at one point alone.
At the library's full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Idn12.AskedT
import Johnson.Desc.K5.Honest.Law.RiderOfAsked

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (seatTab)
open VerifiableInference.Desc.First.Att.P (segAt_front)
open H2K5.Honest (tOf Rider rider_item_at_head)
open ProofFile.Honest.FirstThread (WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (A : K5AtT h T g it pb wt ans test carryX cq)
include A

/-- **THE BATCH OF THE THIRD FAMILY AT THE LOOKUP's POINT IS 0 AT THE CELLS OF THE RUN's OWN INPUT,
FROM `Thr` T IN FRONT.** T IS A VARIABLE. CONDITIONAL: the premises stand in the file's head. Sc is
shown by nobody. -/
theorem rider_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr T (borderOf g) k s m E)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att)
    {gL : OnBytes.Model.Forest.Heard} (hgL : att.g = some gL) :
    Rider Z5.P.D (OnBytes.Road.L5.callsOf a.fs) (OnBytes.Slice.readV (gL.zx ++ gL.zy))
      (tOf Reading.gl (inOf Z5.P.S Z5.link (cells m.st.input.trace))) := by
  cases Z5 with
  | mk link P base keyAt =>
  have hP' : P = ⟨a.S, a.own⟩ := hP
  subst hP'
  obtain ⟨Pl, -⟩ := decides_T h A hg ha Hs.member
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h A hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← A.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h A (Nat.le_of_lt hlt) hT
  have hq : Item.worth (2 * g + 1) 2 "rider" ∈ asked7 (2 * g + 1) := by
    unfold asked7
    simp
  have h0 := (A.means _ (Or.inl hq) _ _ _ _).1
    (hT.2.2.2.1 [] _ (asked_open_T h A hfit hb _ hq))
  have hp0 : pb (T.seat k m s).1 = m.st.input.x.pub := A.handed _ _ _
  rw [hp0] at h0
  obtain ⟨g1, hg1, K3, -⟩ := Sc.keyTie k s m E hT att e
  obtain rfl : g1 = gL := Option.some.inj (hg1.symm.trans hgL)
  exact rider_item_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr
    hu hon e (segAt_front e) (T.strs E) _ h0 hgL K3
    (fun q hq' => cells_named Sc (addrIn_at_head h hg ha) hT (segAt_front e) [] q hq')

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.rider_T
