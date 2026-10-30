-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SmallAtDraw.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A
PAYMENT BENEATH THE KIND'S FROZEN CONDITION: THE FIELD `small` OF `K8LeftT`, TO THE LETTER, FROM THE
CONDITION'S OWN FIELD `fold`, TWO CLOSED FACTS ON THE PLAN, AND FOUR PLAIN FACTS A MATRIX ON THE
STATE. NO SOUNDNESS.

`small_at_const` (SmallJoin.lean) has the field from `ShowsAt`; ShowsJoin.lean has the two
readers of a committed symbol at one entry of one table. Here `ShowsAt` is had at every reached
state in front of the draw:
  `planAt_tlAt`: the link's own planned value IS the library's `Meaning.tlAt`.
  the part has the plan's number and list of matrices and numbers of their arrays: `k8LaidOwn`;
  a link and a fork are open: `K8FoldAt`; the promise (`fork_of_onQ`);
  the layout has the label's array, every element inside the sizes is laid, and the seat is what the
    layout's reader gives: `seat_of_laidThere` at the head's own test `PlanOk.laid`;
  the open link's list and layout are the built link's and the plan's: `K8FoldAt`'s fifth and sixth.
  `MatAt`: THE FOUR PLAIN FACTS ON THE STATE, at one array A born at a link: the frame knows where
    A's message is (o); the programs' own test `laidMatrixOk` at the statement's bits of o; the book
    seats o at a tenant of the segment's group; that tenant has the plan's number of the message.
  `SmallOwes`: WHAT IS LEFT OF THE FIELD: `names` (closed: the built link's list names the array of
    each matrix's label at the plan's number of that matrix's array); `layout` (closed: the ground's
    layout is the constant's); `mats`: `MatAt` along the condition beside the promise.
  `small_of_owes`: **`fold` and `SmallOwes` give `K8LeftT`'s field `small`, to the letter.**
Limits. `SmallOwes` is shown nowhere here. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.ShowsJoin
import Johnson.P1K8R.TightAt
import Johnson.Goal.Meaning.ReadingsOne

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc (Block Chain Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (seven lay7 lay7_of_test)
open VerifiableInference.Desc.K9 (seatAt seatAt_mem)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- **The link's own planned value is the library's.** -/
theorem planAt_tlAt {W : Verify.Public} {l : ℕ} {tlP : HTailF2} (h : P1K8S.PlanAt W l tlP) :
    tlP = Meaning.tlAt W l := by
  unfold Meaning.tlAt
  rcases h with ⟨rfl, rfl⟩ | ⟨g, hp, hg, rfl, e, rfl⟩ | ⟨g, a, hg, rfl, e, rfl⟩
  · rfl
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show 2 * g / 2 = g by omega, e]
    rfl
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (2 * g + 1) / 2 = g by omega, e]
    rfl

/-- **THE FOUR PLAIN FACTS ON THE STATE**, at one array A born at link born. -/
def MatAt (Zp : ProofFile.Pub) (cF : Chain S Cl) (l : ℕ) (s : S) (L : LinkCtx) (born : ℕ)
    (A : ReqArray) : Prop :=
  ∃ (o : ℕ) (q : ℕ × ℕ), L.check.frame.whereIs born A.message = some o ∧
    laidMatrixOk A (s.st.rowBits o .main) (s.st.placeBits o .main) = true ∧
    seatAt ((P5J.At.N Zp cF).group l) s.book o = some q ∧
    P5J.At.arr Zp q.1 q.2 = P5J.At.num Zp born A.message

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT OF THE FIELD `small` AT LINK l.** -/
structure SmallOwes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame} (G : ProofFile.Ground)
    (l : ℕ) (Xl : LinkH) (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop) : Prop where
  names : ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM →
    Xl.arrayOf[(Meaning.tlAt (P5J.At.X Zp) l).gtTree.getD μ 0]? =
      some (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ)))
  layout : G.first.layout = P5J.At.layout Zp
  mats : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (L : LinkCtx),
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) → a.1.failed = none → a.1.link? = some L →
    ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM → ∀ A,
      VerifiableInference.Desc.arrayOf (P5J.At.layout Zp)
        (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ))
        (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ))) = some A →
      MatAt Zp cF l a.1 L (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ)) A

/-- **THE FIELD `small` OF `K8LeftT`, TO THE LETTER.** -/
theorem small_of_owes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {n₀ : ℕ} {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    (fold : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) → a.1.failed = none → K8FoldAt Zp G l Xl n₀ a.1)
    (H : SmallOwes h G l Xl Rch) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) w,
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      TieAt (cellsAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
        (z, a.1)) a.1 w →
      (mgAtAll h).constr l .small (z, a.1) (strsOf Fr a.2) w := by
  intro z a w ha hr hm hT
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hm' : a.1.failed = none := not_not.1 hm
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
    rw [← drawAt_place]
    exact hRch _ _ hr
  obtain ⟨L, -, -, hL, -, -, -, e1, e2, -, -, -⟩ := fold z a ha hr hm'
  obtain ⟨F, hF⟩ := fork_of_onQ (P5J.At.N Zp cF) (mgAtAll h) (fun s => (z, s)) l hl a ha hm'
  obtain ⟨tlP, hv, h7, -⟩ := P1K8S.k8LaidOwn h.scope h.reads O hx ((z, a.1), a.2) hr'
  have eP : tlP = Meaning.tlAt (P5J.At.X Zp) l := by
    rw [planAt_tlAt hv, O.W]
    rfl
  refine small_at_const h hl z a.1 (strsOf Fr a.2) w (fun tl ht => ?_) hT
  have e7 : seven tl = seven (Meaning.tlAt (P5J.At.X Zp) l) := by
    have e := lay7_of_test h7
    unfold lay7 at e
    rw [show (((z, a.1), a.2) : (ProofFile.InstPub × S) × Fr.E.Str).1.2.tl? = some tl from ht] at e
    rw [← eP]
    exact Option.some.inj e
  have eG : tl.gtTree = (Meaning.tlAt (P5J.At.X Zp) l).gtTree := congrArg (·.1) e7
  refine ⟨congrArg (·.2.2.2.2.1) e7, congrArg (·.2.2.2.2.2.2) e7, fun μ r c hr1 hc1 => ?_⟩
  obtain ⟨A, rp, hA, -, -, hrp, eS⟩ :=
    Meaning.seat_of_laidThere h.plan.laid (P5J.At.num Zp) (by omega : l < 25) μ hr1 hc1
  obtain ⟨o, q, hwi, hok, hq, hn⟩ := H.mats z a L ha hr hm' hL μ.val μ.isLt A hA
  have hxx : L.arrayOf[tl.gtTree.getD μ 0]? =
      some (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ.val),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ.val))) := by
    rw [e1, eG]
    exact H.names μ.val μ.isLt
  have haa : OnBytes.reqArray L.check.rows.layout
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ.val))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ.val))) = some A := by
    rw [e2, H.layout, Meaning.reqArray_eq_arrayOf]
    exact hA
  have hN1 := h.plan.hN l μ r c hr1 hc1
  rw [eS] at hN1
  rw [show seatC Zp l μ r c = _ from eS,
    read_is_entry (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l w hN1
      (seatAt_mem _ _ _ _ hq) hn]
  exact (cell_is_entry (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l z a.1
    hL hF ht hxx haa hwi hok hq w hrp).symm

end

end P1K8T

#print axioms P1K8T.planAt_tlAt
#print axioms P1K8T.small_of_owes
