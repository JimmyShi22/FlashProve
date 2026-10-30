-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/AskedT.lean: CONDITIONAL: two of the library's three
families of identities on an attention segment, AT THE CELLS OF THE RUN's OWN INPUT, drawn from two
items that the row of the segment's own rounds (kind K5) asks in front, WITH THE `Thread` T A
VARIABLE.

Why. The laws on the values of the kind take "the input's cells meet the three families" as a
premise on the letter T.valid (`IdnOwed`, Honest/K5/Law/IdnAt.lean). The row asks the items "idn"
and "small" of the segment's relation in front, `Thr` T holds them there of T's own witness, and the
tie of the witness's cells to the trace's (`K5Script`, its field `cellsTie`) carries them to the
input's cells. So for the first two families that premise can give way.

  `HoldsOwed`   a premise's form on the letters T.valid and cq: at every valid input w the cells
                cq w hold an index. cq w: the cells that the honest side's letters lay for the input
                w: on the honest side the meaning's decoder is the constant cq w, and decodes no
                table. The item "idn" says what it says "for every index that these cells hold":
                where they hold none the item is idle
  `holdsOwed_all`   it follows from the same sentence at every input, valid or not
  `idn12_T`     CONDITIONAL: **the families at1 and at2 at the input's cells**, from `Thr` T in
                front (`idn12_of_asked`, Johnson/Desc/K5/Honest/Law/IdnOfAsked.lean)

THE PREMISES OF `idn12_T`: the hypothesis h · `K5AtT` (what the row asks; what T.means says of the
two items; the form in front) · g below 12, the group's plan · `K5Seated` · the test T.fits (what
the row asks is open) · Sc: `K5Script`: NOT SHOWN · hP · hH: `HoldsOwed`: SHOWN OF NO
`valid` · `Thr` T at the border.

Limits. Conditional. THE THIRD FAMILY (at3) IS NOT HERE. `HoldsOwed` is a definition: nothing is
claimed of it. At the library's full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SharesT
import Johnson.Desc.ProofFile.Honest.K5.Law.AddrInAt
import Johnson.Desc.K5.Honest.Law.IdnOfAsked

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (seatTab)
open VerifiableInference.Desc.First.Att.P (segAt_front)
open Inst.Model.AttSeg (Idn idnVal)
open H2K5.Honest (tOf idn12_of_asked)
open ProofFile.Honest.FirstThread (WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

/-- **At every valid input w the cells cq w hold an index.** cq w: the cells that the honest side's
letters lay for the input w. It is a definition: a premise's form on the letters `valid` and cq.
Nothing is claimed of it. THE INDEX STANDS UNDER "THERE IS", TIED TO NOTHING OF w.w₀: enough for the
identities; never read as "the cells are those of the committed weights". -/
def HoldsOwed {W : Type} (valid : W → Prop) (cq : W → CellsM OnBytes.Flat.numsFull) : Prop :=
  ∀ w, valid w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (cq w) i

/-- It follows from the same sentence at every input. CONDITIONAL: that sentence. -/
theorem holdsOwed_all {W : Type} (valid : W → Prop) {cq : W → CellsM OnBytes.Flat.numsFull}
    (hA : ∀ w, ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (cq w) i) : HoldsOwed valid cq :=
  fun w _ => hA w

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (R : K5AtT h T g it pb wt ans test carryX cq)
include R

/-- **THE FAMILIES at1 AND at2 AT THE CELLS OF THE RUN's OWN INPUT, FROM `Thr` T IN FRONT.** T IS A
VARIABLE. CONDITIONAL: the premises stand in the file's head. Sc is shown by nobody; hH of no
`valid`. -/
theorem idn12_T {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hH : HoldsOwed T.valid cq) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr T (borderOf g) k s m E) :
    (∀ k' b' g' i, (Idn.at1 k' b' g' i).Valid Z5.P.D →
        idnVal Z5.P.D (tOf Reading.gl (inOf Z5.P.S Z5.link (cells m.st.input.trace)))
          (.at1 k' b' g' i) = 0) ∧
      ∀ b' g' i, (Idn.at2 b' g' i).Valid Z5.P.D →
        idnVal Z5.P.D (tOf Reading.gl (inOf Z5.P.S Z5.link (cells m.st.input.trace)))
          (.at2 b' g' i) = 0 := by
  cases Z5 with
  | mk link P base keyAt =>
  have hP' : P = ⟨a.S, a.own⟩ := hP
  subst hP'
  obtain ⟨Pl, -⟩ := decides_T h R hg ha Hs.member
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← R.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h R (Nat.le_of_lt hlt) hT
  obtain ⟨att, gL, e, -, -⟩ := (readyO_T h R hg Pl hT).open_
  have hqI : Item.constr (2 * g + 1) .idn ∈ asked7 (2 * g + 1) := List.mem_cons_self
  have hqS : Item.constr (2 * g + 1) .small ∈ asked7 (2 * g + 1) := by
    unfold asked7
    simp
  have hI := (R.means _ (Or.inl hqI) _ _ _ _).1
    (hT.2.2.2.1 [] _ (asked_open_T h R hfit hb _ hqI))
  have hS := (R.means _ (Or.inl hqS) _ _ _ _).1
    (hT.2.2.2.1 [] _ (asked_open_T h R hfit hb _ hqS))
  exact idn12_of_asked h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr hu
    hon (segAt_front e) (cq m.st.input) carryX _ (hH _ hT.2.2.2.2.2.2) hI hS
    (fun q hq => cells_named Sc (addrIn_at_head h hg ha) hT (segAt_front e) [] q hq)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.holdsOwed_all
#print axioms ProofFile.Honest.K5.idn12_T
