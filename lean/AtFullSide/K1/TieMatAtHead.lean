-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/TieMatAtHead.lean: hF1 OF exchangeAtS_tie_base (AtFullSide/K1/TieAtBase.lean): THE FIRST FAMILY OF THE ITEM "tie l"
(TieMatS) AT THE BASE PROVER, AT EACH SEGMENT l BELOW 25, by tieMatS_of_front.

  SeatsSaid        public: the plan's half at segment l: the premises hNM, hB, hPub of matSeatF_head at the plan's own record
  OwnerRows        public: each matrix's owner off Sz.ref.owner: its array, number and label
  tieMatS_at_head  the statement, at the two forms
  tieMatS_written  the same at the written plan: the two forms paid by TieMatSeats.lean; what is left: hLf, hN, and the binders hI, hV, hSaid

OF COMPLETENESS's KIND: hSame is paid off the trace, under hI and hV; NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).
The two public forms and the form LaysFilling stand as premises; the Script Q is a letter.
NO PROPERTY IS CLAIMED.
-/
import AtFullSide.K1.TieAtBase
import AtFullSide.K1.TieTailAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatPaid
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatSeats
import Johnson.Desc.ProofFile.Honest.K1.Law.TieOwnerLays
import Johnson.Desc.ProofFile.Honest.K1.Law.TieOwnerJob
import Johnson.Desc.ProofFile.Honest.K1.Law.TieSameOwner
import Johnson.Desc.ProofFile.Honest.Law.LaidOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.HonestTrace (Sz Seg MatName PartsFit ServesAt theTrace packedCells cellOf)
open ProofFile.Honest.FirstThread (Letters lettersHead WtF Script)
open P5J (AtMgA TS)

variable {W₀ : Type}

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Public: the plan's half at segment l.** NM: the number of matrices of the plan's record; own:
number, segment, matrix and array of each matrix's owner. hNM, hB, hPub of matSeatF_head at tlW := the
plan's own record, at the term's cs, arr, ms and Sz.ref. A definition: a premise's form. -/
def SeatsSaid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (NM : ℕ)
    (own : ℕ → ℕ × ℕ × ℕ × ReqArray) (l : ℕ) : Prop :=
  (_root_.Meaning.tlAt Zp.p.X l).NM = NM ∧
  K1.symsSeatedB (h.𝔇.pubD.d3.arrayOf.getD l #[]) h.𝔇.layout h.𝔇.shape l
    (_root_.Meaning.tlAt Zp.p.X l) = true ∧
  ∀ ν, ν < NM → ∀ (c₁ : ℕ × String) (a₁ : ReqArray) (o : ℕ) (q : ℕ × ℕ) (sh : OracleShape),
    (h.𝔇.pubD.d3.arrayOf.getD l #[])[(_root_.Meaning.tlAt Zp.p.X l).gtTree.getD ν 0]? = some c₁ →
    reqArray h.𝔇.layout c₁.1 c₁.2 = some a₁ →
    First.FillSent.whereIsP h.𝔇.pubD.dS l c₁.1 a₁.message = some o →
    K13.Law.d12Full.L.places[o]? = some q →
    K13.Law.d12Full.M[o]? = some sh → (h.𝔇.N.sent l 0).contains q = true →
    ∃ (yM : Mem) (l₀ ν₀ : ℕ), ((P5J.At.ms Zp Z.lay).find? fun z => decide (VerifiableInference.Desc.Sound.seatOf z = q)) = some yM ∧
      (yM.1.l.get yM.2).1 = sh ∧
      laidMatrixOk a₁ (ceilLog2 (sh.rows Part.main))
        (if sh.rows Part.main == 0 then 0 else ((P5J.At.cs Zp).base.getD sh.code default).logEll) = true ∧
      own ν = (P5J.At.arr Zp q.1 q.2, l₀, ν₀, a₁) ∧ Sz.ref.packedShape l ν = Sz.ref.packedShape l₀ ν₀ ∧
      ∀ i c rp, i < (Sz.ref.packedShape l ν).1 → c < (Sz.ref.packedShape l ν).2 →
        laidAt a₁ i c = some rp → rp.1 < sh.mainRows ∧ padB (P5J.At.cs Zp) sh false rp.1 rp.2 = false

/-- **Public: each matrix's owner is Sz.ref's.** At matrix ν of segment l, named μ in the list of σ:
the entry own ν is the owner's number at the plan, the owner's place in Sz.ref's numbering, and its
array in the layout, whose size holds the packed shape. R, P: any bits at which the array passes
laidMatrixOk: they serve the covering of its size alone. A definition: a premise's form. -/
def OwnerRows (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (NM : ℕ)
    (own : ℕ → ℕ × ℕ × ℕ × ReqArray) (l : ℕ) : Prop :=
  ∀ ν, ν < NM → ∀ n l₀ ν₀ a, own ν = (n, l₀, ν₀, a) → ∃ (σ : Seg) (μ : MatName) (R P : ℕ),
    σ.Below 12 ∧ σ.no 12 = l ∧ (MatName.all 3 1 1 4 σ)[ν]? = some μ ∧
    Sz.ref.matAt l₀ ν₀ = some (Sz.ref.owner σ μ) ∧ n = P5J.At.num Zp l₀ a.message ∧
    VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l₀ a.name = some a ∧
    ProofFile.Honest.K1.labelNo a.name = some ν₀ ∧ laidMatrixOk a R P = true ∧
    (Sz.ref.packedShape l ν).1 ≤ a.sizeI ∧ (Sz.ref.packedShape l ν).2 ≤ a.sizeC

end

section
variable {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **hF1 at the base prover, at segment l.** hI: on the letter I (as in exchangeAtS_tie_base). hV: on
Vd; idle at Vd := fun _ => False. hSaid: the thread's Said is within SaidOk. NM, own: the plan's. hLf:
the Script lays the filling at each owner's segment, at one N, no later than the reads of segment l. -/
theorem tieMatS_at_head
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop) (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hI : ∀ u ξ C, I.trace A.Z u ξ = some C → ∃ i x,
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x) ∧
        ServesAt (P5J.At.X A.Z) i x) (hV : Vd w → ReadyInput A.F A.H w)
    {l NM N : ℕ} {own : ℕ → ℕ × ℕ × ℕ × ReqArray} (hl : l < 25)
    (hSeats : SeatsSaid h NM own l) (hRows : OwnerRows h NM own l)
    (hN : N ≤ (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
      roundsTo (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs (K1.noL l false))
    (hLf : ∀ ν, ν < NM → ∀ n l₀ ν₀ a, own ν = (n, l₀, ν₀, a) → ∃ seat heard,
      K5.LaysFilling h Q Vd N (fun v => (witBT I A.Z v).R) seat heard l₀) :
    TieMatS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (P5J.At.cs A.Z)
      (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) Sz.ref (witBT I A.Z) (K1.noL l false) l := by
  obtain ⟨hNM, hB, hPub⟩ := hSeats
  have PF : PartsFit (P5J.At.X A.Z) :=
    OnBytes.HonestTrace.partsFit_in_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  refine tieMatS_of_front (g := h.𝔇.N.sent l 0) (NM := NM) (N := N) (own := own)
    (matSeatF_head h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hl
      (_root_.Meaning.tlAt A.Z.p.X l)
      (codes_at_reads h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hl)
      (fun blk hb k s μ E ds y cols s' hT hd hS tl htl => by
        obtain ⟨e1, e2⟩ := tail_at_reads h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hl
          blk hb k s μ E ds y cols s' hT hd hS tl htl
        exact ⟨e1.trans hNM, e2⟩)
      hNM hB hPub)
    (fun z hz => List.mem_append_left _ (List.mem_append_left _ hz)) hN ?_ ?_ ?_
  · intro ν hν n l₀ ν₀ a ho
    obtain ⟨σ, μ, R, P, -, -, -, hat₀, hn, harr, hlab, -, -, -⟩ := hRows ν hν n l₀ ν₀ a ho
    obtain ⟨seat, heard, Lf⟩ := hLf ν hν n l₀ ν₀ a ho
    have hat₀' : Sz.ref.matAt l₀ ν₀ = some ((Sz.ref.owner σ μ).1, (Sz.ref.owner σ μ).2) := hat₀
    obtain ⟨-, -, hmu⟩ := (OnBytes.HonestTrace.matAt_eq_some_iff Sz.ref _ _ _ _).1 hat₀'
    have hno : (Sz.ref.arrayNo (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).isSome = true :=
      (OnBytes.HonestTrace.arrayNo_isSome_iff Sz.ref _ _).2
        ⟨by rw [hmu]; rfl, OnBytes.HonestTrace.owner_owner Sz.ref σ μ⟩
    have hz := K5.cellsVals_size Sz.ref hlab hat₀' hno
    subst hn
    exact ownerHolds_of_lays (H := A.H) (test := test) (carryX := carryX) (item := item) (n₁ := n₁)
      (n₂ := n₂) (b₀ := b₀) (Vd := Vd) (Rd := Rd) (Kp := Kp) (w := w) Lf (wit := witBT I A.Z)
      (fun _ => rfl) (fun v hv => hv.2) harr rfl hlab hz
  · intro ν hν n l₀ ν₀ a ho i c hi hc
    obtain ⟨σ, μ, R, P, -, -, -, -, -, -, -, hok, hsI, hsC⟩ := hRows ν hν n l₀ ν₀ a ho
    exact Option.isSome_iff_exists.1
      (Meaning.laidAt_of_matrixOk hok (Nat.lt_of_lt_of_le hi hsI) (Nat.lt_of_lt_of_le hc hsC))
  · intro v hv ν hν n l₀ ν₀ a ho i c hi hc
    obtain ⟨σ, μ, R, P, hσ, hl', hμ, hat₀, -, -, -, -, -, -⟩ := hRows ν hν n l₀ ν₀ a ho
    obtain ⟨i', ξ, hcell, hS⟩ := hTr_at_base hA hI hV v hv
    have hmu : Sz.ref.mu σ μ = some ν := by
      unfold Sz.mu
      rw [if_pos (show σ.Below Sz.ref.nGr from hσ)]
      exact OnBytes.HonestTrace.all_no_ref σ hμ
    have hat : Sz.ref.matAt (σ.no 12) ν = some (σ, μ) :=
      (OnBytes.HonestTrace.matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨hσ, rfl, hmu⟩
    have hat₀' : Sz.ref.matAt l₀ ν₀ = some ((Sz.ref.owner σ μ).1, (Sz.ref.owner σ μ).2) := hat₀
    obtain ⟨-, hl₀, -⟩ := (OnBytes.HonestTrace.matAt_eq_some_iff Sz.ref _ _ _ _).1 hat₀'
    have B := OnBytes.HonestTrace.borrowedSame_of_meetsAll
      (OnBytes.HonestTrace.meetsAll_theTrace h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne hS)
    have hSh : Sz.ref.shape σ μ = Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 :=
      (OnBytes.HonestTrace.shape_owner Sz.ref OnBytes.HonestTrace.ref_ok.1 σ μ (by rw [hmu]; rfl)).symm
    rw [hcell, ← hl']
    exact packed_of_owner PF B hσ hμ hat hat₀ hl₀.symm hSh i c

/-- **hF1 at the base prover, at the written plan.** The two public forms are paid (nmW, ownAt:
TieMatSeats.lean). Left: hI, hV, hSaid as in tieMatS_at_head; hN; hLf, the Script lays the filling at every
segment at one N. -/
theorem tieMatS_written
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop) (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hI : ∀ u ξ C, I.trace A.Z u ξ = some C → ∃ i x,
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x) ∧
        ServesAt (P5J.At.X A.Z) i x) (hV : Vd w → ReadyInput A.F A.H w)
    {l N : ℕ} (hl : l < 25)
    (hN : N ≤ (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
      roundsTo (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs (K1.noL l false))
    (hLf : ∀ l₀, l₀ < 25 → ∃ seat heard,
      K5.LaysFilling h Q Vd N (fun v => (witBT I A.Z v).R) seat heard l₀) :
    TieMatS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (P5J.At.cs A.Z)
      (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) Sz.ref (witBT I A.Z) (K1.noL l false) l := by
  have hO := ownerRows_head h hl
  obtain ⟨e1, e2, e3⟩ := tieSeats_head h hl
  refine tieMatS_at_head hA h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hI hV
    (NM := nmW l) (own := ownAt A.Z l) hl
    ⟨e1, e2, fun ν hν c₁ a₁ o q sh f1 f2 f3 f4 f5 _ => e3 ν hν c₁ a₁ o q sh f1 f2 f3 f4 f5⟩
    ?_ hN ?_
  · intro ν hν n l₀ ν₀ a ho
    obtain ⟨σ, μ, R, P, g1, g2, g3, g4, -, g5⟩ := hO ν hν n l₀ ν₀ a ho
    exact ⟨σ, μ, R, P, g1, g2, g3, g4, g5⟩
  · intro ν hν n l₀ ν₀ a ho
    obtain ⟨σ, μ, R, P, -, -, -, -, g, -⟩ := hO ν hν n l₀ ν₀ a ho
    exact hLf l₀ g

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieMatS_at_head
#print axioms ProofFile.Honest.K1.tieMatS_written
