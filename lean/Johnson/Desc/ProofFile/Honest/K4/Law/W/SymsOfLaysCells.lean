-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/SymsOfLaysCells.lean: CONDITIONAL: IT MOVES A DEBT,
IT PAYS NONE. AT EACH OF THE TWELVE GROUPS.

What is here. THE THIRD STONE OF A BRIDGE TO THE HYPOTHESIS `CellIsList` (Law/W/CellsTieOf.lean) OF
THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), AT EVERY GROUP OF LAYERS: the equation in the
script's own letters (`K4SymsRaw`, Law/W/CellsOfSyms.lean) follows from the premise's
form «the script lays the filling off the planes» (`LaysCells`, Honest/K5/Law/LaysCells.lean) at
K4's own segment 2 g and, from the second group on, at the segment 2 (g - 1) of the group before, a
sentence on the readers, and public premises. It is the like of `eSyms_of_laysCells`,
at a layers' link. From the second group on one matrix of K4's list is borrowed: the stream that
comes in is the stream that goes out of the group before; its symbols lie in a message of that
segment, which K4's link keeps. In the first group L' asks nothing. Five statements with their
proofs. `k4Sym_at` joins `k4_seat_number` (Law/W/SeatNumberK4.lean: which array, place and number a
symbol's seat has) with `sym_of_laysCells` (Law/W/SymOfLaysCells.lean: what the form gives there)
and turns the packing of the trace's cells into the packing of the honest side's cells.

  `iB_head`   under h: the planes' matrix has the number 5 in K4's list.
  `ff_name_at`   on the typed sizes alone: at a number below 9 that is not 5: the name, its owner,
      that the owner is the matrix of `ownerW g i`, holds no planes and has an array of its own
      segment, and that owner and borrower have one shape.
  `pack_k4_of_trace`   a helper on the two packings.
  `k4Sym_at`   the equation at one matrix, from the form at the segment of the matrix's owner.
  `k4SymsRaw_all`   **`K4SymsRaw` at each group.**

Not shown here. L, L': THAT A SCRIPT MEETS THE FORM: shown of no script here. ON L AND L': they
are premises on what the script holds of the private input: NOT IN FRONT OF A LAW OVER COINS.
Laws that end in this form at the Script joined of K1's and K2's
lots are no part of this library.


That the joined script is the honest prover's is said nowhere. hrd: that the frame's reader of the
cells is the lot's (a premise here). hSz: on the filling's sizes
(Honest/K5/Law/SizesOffPlanes.lean says where it is met). hShape: the plan's entry has the rows and
columns of the full-size example's typed sizes, at every matrix but the planes': the form of
`shape_at_plan` (Honest/K5/Law/PackedAtSeg.lean) with the layers' segment for attention's: a
premise here; Law/W/ShapeK4.lean, not imported here, has it under h. hOwn: the key under which K4's
honest side reads matrix i (`k4Owner`, Honest/K4/Part.lean) is the owner's segment's number, the
owner's label and column 0: a premise here; Law/W/OwnerKeyK4.lean, not imported here, has it under
h. hQ: Qp is what `k4PubOf` returns at the member's parameters. h: the library's hypothesis
`P5J.AtMgA` on the public files; Lh and hx follow from it, as Law/W/MatsAreHead.lean's head says.
NOT TRIED FOR EMPTINESS: no instance of the premises together is exhibited. `iB_head` RESTS ON TWO
LAWS OF FILES UNDER Johnson/Goal/, CALLED BY NAME (`Meaning.ix_of_core`, `Hd.core_of_scope`), as the
library's Johnson/Road/K4/NineInScope.lean and its callers do. All limits of the heads of the files
that it imports hold here; among them: closed facts by evaluation in Lean's kernel lie beneath; no
independent checker that its writers know of has replayed them; through its imports it stands over
files under Johnson/Goal/. THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a part of the proof file's description
may import this one. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsOfSyms
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SeatNumberK4
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SymOfLaysCells
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinReader

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2 Reading)
open OnBytes.Model.Layer (matIx)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.HonestTrace (Sz Seg MatName nameNo_isSome nameNo_eq_some_iff matAt_eq_some_iff
  arrayNo_isSome_iff shape_owner ref_ok)
open OnBytes.Road.K4 (ownerW)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (layAt Seat sigListCalls seatCalls szOf)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.K5 (LaysCells planesAtRef msgNo5)
open ProofFile.Honest.FirstThread (Script)
open P5J (AtMgA TS CellsM)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- On the full-size example's typed sizes alone. At a number below 9 that is not 5, at a group
below 12: μ': the name with that number in the layers' segment's list; (σ, μ): who committed it. -/
theorem ff_name_at {g i : ℕ} (hg : g < 12) (hi9 : i < 9) (hi5 : i ≠ 5) :
    ∃ (μ' : MatName) (σ : Seg) (μ : MatName), Sz.ref.nameNo (.ff g) i = some μ' ∧ μ' ≠ .b ∧
      Sz.ref.owner (.ff g) μ' = (σ, μ) ∧
      Sz.ref.matAt (ownerW g i).1 (ownerW g i).2 = some (σ, μ) ∧
      (μ ≠ .b ∧ μ ≠ .bA ∧ μ ≠ .bH) ∧ (Sz.ref.arrayNo σ μ).isSome = true ∧
      Sz.ref.shape σ μ = Sz.ref.shape (.ff g) μ' := by
  by_cases c : i = 8 ∧ g ≠ 0
  · obtain ⟨rfl, h0⟩ := c
    have ow : ownerW g 8 = (2 * (g - 1), 7) := by
      unfold ownerW
      rw [if_pos ⟨rfl, h0⟩]
    have hg' : g - 1 < 12 := by omega
    have own : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg h0
    have hmu : Sz.ref.mu (.ff (g - 1)) .xbO = some 7 := by
      unfold Sz.mu
      rw [if_pos (show Seg.Below Sz.ref.nGr (.ff (g - 1)) from hg')]
      rfl
    have hmu8 : Sz.ref.mu (.ff g) .xbI = some 8 := by
      unfold Sz.mu
      rw [if_pos (show Seg.Below Sz.ref.nGr (.ff g) from hg)]
      rfl
    have hsh := shape_owner Sz.ref ref_ok.1 (.ff g) .xbI (by rw [hmu8]; rfl)
    rw [own] at hsh
    refine ⟨.xbI, .ff (g - 1), .xbO, rfl, by simp, own, ?_, ⟨by simp, by simp, by simp⟩,
      (arrayNo_isSome_iff Sz.ref _ _).2 ⟨by rw [hmu]; rfl, rfl⟩, hsh⟩
    rw [ow]
    exact (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨hg', rfl, hmu⟩
  · have ow : ownerW g i = (2 * g, i) := by
      unfold ownerW
      rw [if_neg c]
    obtain ⟨μ, hμ⟩ := nameNo_isSome Sz.ref (σ := .ff g) (mu := i) hi9
    have hno := (nameNo_eq_some_iff Sz.ref _ _ _).1 hμ
    have hmu : Sz.ref.mu (.ff g) μ = some i := by
      unfold Sz.mu
      rw [if_pos (show Seg.Below Sz.ref.nGr (.ff g) from hg)]
      exact hno
    have hb : μ ≠ .b := by
      rintro rfl
      have e5 : 5 = i := Option.some.inj hno
      exact hi5 e5.symm
    have hbA : μ ≠ .bA := by
      rintro rfl
      have e : (none : Option ℕ) = some i := hno
      cases e
    have hbH : μ ≠ .bH := by
      rintro rfl
      have e : (none : Option ℕ) = some i := hno
      cases e
    have own : Sz.ref.owner (.ff g) μ = (.ff g, μ) := by
      by_cases hx : μ = .xbI
      · subst hx
        have e8 : 8 = i := Option.some.inj hno
        exact if_pos (by
          by_contra h0
          exact c ⟨e8.symm, h0⟩)
      · clear hμ hno hmu hb hbA hbH
        cases μ with
        | xbI => exact absurd rfl hx
        | _ => rfl
    refine ⟨μ, .ff g, μ, hμ, hb, own, ?_, ⟨hb, hbA, hbH⟩,
      (arrayNo_isSome_iff Sz.ref _ _).2 ⟨by rw [hmu]; rfl, own⟩, rfl⟩
    rw [ow]
    exact (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨hg, rfl, hmu⟩

/-- CONDITIONAL: on hm and hO. The packing of the trace's cells under the key (l, lab), down a
column, is the packing of the honest side's cells of matrix i, where that key is the one under which
the honest side reads matrix i. -/
theorem pack_k4_of_trace {W₀ Rc Tr : Type} {Qp : K4Pub} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (v : Local W₀ Rc ProofFile.Inst Tr) {i l : ℕ} {lab : String} {n₁ n₂ : ℕ} (hm : n₂ = n₁)
    (hO : k4Owner Qp i = (l, lab, 0)) (c i' : ℕ) :
    Alg.pack (2 ^ 20) (fun a : Fin n₁ =>
        algebraMap Cb.Gl.F Cb.Gl.E ((cells v.trace).cell l lab a.val c)) i' =
      Alg.pack (2 ^ 20) (fun a : Fin n₂ => Reading.gl.val
        (OnBytes.ofF ((k4Wit Qp cells weights tokens (look Qp) v).cell i a.val c))) i' := by
  subst hm
  congr 1
  funext a
  show _ = Reading.gl.val (OnBytes.ofF (OnBytes.Slice.ofF
    ((cells v.trace).cell (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c))))
  rw [gl_slice]
  simp only [hO, Nat.zero_add]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, Lh and hQ. **The planes' matrix has the number 5 in K4's list.** -/
theorem iB_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) : (matIx Qp.P.y).iB = 5 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
    O.W ▸ O.public
  have i6 := (_root_.Meaning.ix_of_core hpub
    (OnBytes.Road.Hd.core_of_scope h.scope h.reads hpub)).1
  have ey : x.2.P.y = Zp.p.X.y := (nine_head h Lh).Sx.y
  unfold k4PubOf at hQ
  obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 hQ
  show (matIx x.2.P.y).iB = 5
  rw [ey]
  have eB : (matIx Zp.p.X.y).iB = Zp.p.X.y.parts.getD 0 0 + Zp.p.X.y.parts.getD 1 0 + 1 := rfl
  have eQ : (matIx Zp.p.X.y).iQA = Zp.p.X.y.parts.getD 0 0 + Zp.p.X.y.parts.getD 1 0 + 2 := rfl
  omega

variable {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh} {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}

/-- CONDITIONAL: on every hypothesis named. **The equation at one symbol of one matrix**, from the
form at the segment of the matrix's owner. (σ, μ): the owner. -/
theorem k4Sym_at {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {Qp : K4Pub} {S : Sz} (hSz : planesAtRef S = Sz.ref)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : MsgAddr → Option (ℕ × ℕ)} {heard : MsgAddr → ℕ} {i : ℕ}
    (L : LaysCells h Q S Vd N rd seat heard (ownerW g i).1) {cells : Tr → Cells}
    (hrd : ∀ v, (rd v).cells = cells v.trace) (weights : W₀ → Weights)
    (tokens : ProofFile.Inst → Array Nat) (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    {σ : Seg} {μ : MatName}
    (hM : Sz.ref.matAt (ownerW g i).1 (ownerW g i).2 = some (σ, μ))
    (hne : μ ≠ .b ∧ μ ≠ .bA ∧ μ ≠ .bH) (ho : (Sz.ref.arrayNo σ μ).isSome = true)
    (hm : (x.2.hp.tl.mats.getD i {}).m = (Sz.ref.shape σ μ).1)
    (hkk : (x.2.hp.tl.mats.getD i {}).k = (Sz.ref.shape σ μ).2)
    (hO : k4Owner Qp i = ((ownerW g i).1, μ.label, 0))
    (kk : Coins Bk) {v : Local W₀ Rc ProofFile.Inst Tr} (hv : Vd v) {hd : List Fmt.Drawn}
    (hN : N ≤ hd.length) {i' c : ℕ} (hiN : i < x.2.hp.tl.NM)
    (hi' : i' < Alg.symRows (x.2.hp.tl.mats.getD i {}).m) (hc : c < (x.2.hp.tl.mats.getD i {}).k)
    {s : Seat} (hk : s.msg < (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link).length)
    (hs : seatCalls h.𝔇.sent xl.link (.cell (x.2.hp.tl.gtTree.getD i 0) i' c) = some s) :
    Q.msg (msgNo5 h xl s.msg hk) kk v (hd.take (Q.fixedMsg (msgNo5 h xl s.msg hk))) false s.row
        s.place =
      Alg.pack (((szOf x.2.hp.tl).rad : Nat) : ℤ)
        (fun a : Fin (x.2.hp.tl.mats.getD i {}).m =>
          Reading.gl.val
            (OnBytes.ofF ((k4Wit Qp cells weights tokens (look Qp) v).cell i a.val c))) i' := by
  obtain ⟨hi9, A, hA, hlaid, hnum⟩ := k4_seat_number h Lh hx hiN hi' hc hk hs
  have h26 : (ownerW g i).2 < 26 := by
    unfold ownerW
    split_ifs
    · exact (by decide : 7 < 26)
    · exact Nat.lt_trans hi9 (by decide)
  have q := sym_of_laysCells hSz L hrd h26 hA hM hne ho hlaid
    (by rw [← hm]; exact hi') (by rw [← hkk]; exact hc) kk hv hN
  have eR : (((szOf x.2.hp.tl).rad : ℕ) : ℤ) = 2 ^ 20 := by
    show ((2 ^ 20 : ℕ) : ℤ) = 2 ^ 20
    norm_num
  rw [hnum, eR]
  exact q.trans (pack_k4_of_trace v hm hO c i')

/-- CONDITIONAL: on every hypothesis named; the head says of each what it is. **THE EQUATION IN THE
SCRIPT's OWN LETTERS, AT EACH GROUP.** It moves the debt. -/
theorem k4SymsRaw_all {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) {S : Sz} (hSz : planesAtRef S = Sz.ref)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat seat' : MsgAddr → Option (ℕ × ℕ)} {heard heard' : MsgAddr → ℕ}
    (L : LaysCells h Q S Vd N rd seat heard (2 * g))
    (L' : g ≠ 0 → LaysCells h Q S Vd N rd seat' heard' (2 * (g - 1))) {cells : Tr → Cells}
    (hrd : ∀ v, (rd v).cells = cells v.trace) (weights : W₀ → Weights)
    (tokens : ProofFile.Inst → Array Nat) (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (hShape : ∀ i μ, Sz.ref.nameNo (.ff g) i = some μ → μ ≠ .b →
      (x.2.hp.tl.mats.getD i {}).m = (Sz.ref.shape (.ff g) μ).1 ∧
        (x.2.hp.tl.mats.getD i {}).k = (Sz.ref.shape (.ff g) μ).2)
    (hOwn : ∀ i μ, Sz.ref.nameNo (.ff g) i = some μ →
      k4Owner Qp i = ((ownerW g i).1, (Sz.ref.owner (.ff g) μ).2.label, 0)) :
    K4SymsRaw h Q Vd N xl x.2.hp.tl Qp cells weights tokens look := by
  intro kk v hd hv hN i i' c hiN hi hi' hc s hk hs
  have hi9 := (k4_seat_number h Lh hx hiN hi' hc hk hs).1
  rw [iB_head h Lh hQ] at hi
  obtain ⟨μ', σ, μ, hμ', hb', own, hM, hne, ho, hsh⟩ := ff_name_at Lh.lt hi9 hi
  obtain ⟨hm, hkk⟩ := hShape i μ' hμ' hb'
  rw [← hsh] at hm hkk
  have hO := hOwn i μ' hμ'
  rw [own] at hO
  by_cases cb : i = 8 ∧ g ≠ 0
  · have ow : (ownerW g i).1 = 2 * (g - 1) := by
      unfold ownerW
      rw [if_pos cb]
    exact k4Sym_at Lh hx hSz (ow ▸ L' cb.2) hrd weights tokens look hM hne ho hm hkk hO kk hv hN
      hiN hi' hc hk hs
  · have ow : (ownerW g i).1 = 2 * g := by
      unfold ownerW
      rw [if_neg cb]
    exact k4Sym_at Lh hx hSz (ow ▸ L) hrd weights tokens look hM hne ho hm hkk hO kk hv hN
      hiN hi' hc hk hs

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.ff_name_at
#print axioms ProofFile.Honest.K4.W.pack_k4_of_trace
#print axioms ProofFile.Honest.K4.W.iB_head
#print axioms ProofFile.Honest.K4.W.k4Sym_at
#print axioms ProofFile.Honest.K4.W.k4SymsRaw_all
