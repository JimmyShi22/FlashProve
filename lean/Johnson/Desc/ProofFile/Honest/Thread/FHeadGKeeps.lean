-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadGKeeps.lean: the column `hK` of the gathering
(`owesS_head_form`, GatherHeadForm.lean) at `f := fHeadG` (FHeadG.lean), and the gathering at it.
What is said before the chain is `SaidOk` (SaidOk.lean). `fHeadG` is `fHeadF` with the clause
`relsHead` beside it. `relsHead` speaks at K1's commitment to the digits and at the lookup on the
digits (K3). `k1_rels_at` and `k3_readers_at` (PayersAt.lean) prove its two clauses from an
accepting step at the numbers `noL l true` and `k3K l true`. `rels_k1_number` and `rels_k3_number`
(FHeadG.lean) say that the places at which `relsHead` speaks stand at these numbers. No definition.

  1  `border_at`   the number of a place of the written list
  2  `head_rels`   after an accepting step the clause `relsHead` holds, at every number
  3  `fHeadG_hK`   the column `hK` at `fHeadG`, from the column `hF`
  4  `owesS_fHeadG`   `OwesS` at `csHead` and `fHeadG`

What `owesS_fHeadG` leaves as hypotheses: those of `owesS_fHeadF_paid` (GatherFHeadW.lean), at the
invariant with `fHeadG`: the columns `hP`, `hF`, `h₀`, `hl`, `hX`; `hok`; `hB`; `hσ`.

Limits.
  * `OwesS` is the form of a hypothesis of the rule. Nothing here shows that a run accepts.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG
import Johnson.Desc.ProofFile.Honest.Thread.PayersAt
import Johnson.Desc.ProofFile.Honest.Thread.GatherFHeadW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (borderOf)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- The number of a place of the written list. -/
theorem border_at {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) :
    borderOf P5J.At.ps (some p) = b := by
  have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
  have hb : b < 358 := by
    have hlt := (List.getElem?_eq_some_iff.1 hp).1
    rw [← e', IM.places_len] at hlt
    exact hlt
  have e := IM.border_W b (by omega)
  rw [e', hp] at e
  exact e

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **After an accepting step the clause `relsHead` holds**, at every number. -/
theorem head_rels :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      relsHead h.𝔇.pubD blk.place.kind blk.place s s' := by
  intro b hb blk hblk k s m E ds y cols s' hA _ hS
  have hb' : b < cF.blocksInOrder.length := hb
  rw [head_len h] at hb'
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk
  have hbo := border_at hp
  by_cases h1 : blk.place.kind = KindName.K1
  · rw [h1]
    show ∀ l, blk.place.link = some l → blk.place.piece = 6 ∨ blk.place.piece = 7 →
      k1RelsAt h.𝔇.pubD l blk.place s s'
    intro l hl hc
    obtain ⟨hl25, rfl⟩ := rels_k1_number hb' hp h1 hl hc
    unfold k1RelsAt
    rw [hbo]
    exact k1_rels_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl25 hblk hA hS
  · by_cases h3 : blk.place.kind = KindName.K3
    · rw [h3]
      show blk.place.piece = 7 ∨ blk.place.piece = 8 → readersStayAt h.𝔇.pubD blk.place s s'
      intro hc
      obtain ⟨hl25, hbk⟩ := rels_k3_number hb' hp h3 hc
      unfold readersStayAt
      rw [hbo]
      subst hbk
      exact k3_readers_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl25 hblk hA hS
    · exact relsHead_other _ h1 h3 _ _ _

/-- **The column `hK` at `fHeadG`**, from the column `hF`. -/
theorem fHeadG_hK {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hF :
      ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
        ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
        ∀ k s m E ds y cols s',
        ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m E →
        drawsFit blk.rounds ds = true →
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
          cols s' →
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (b + 1) k s' y.2) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      fHeadG Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD blk.place.kind blk.place s s' :=
  fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
    ⟨head_hK_forms h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w SaidOk _ hF
        (fHead_hK_whole h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w SaidOk hB) b hb blk hblk k s m
        E ds y cols s' hA hd hS,
      head_rels h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b hb blk hblk k s m E ds y cols s' hA
        hd hS⟩

end ProofFile.Honest.FirstThread

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`OwesS` at the first chain's invariant at the full size**, at `csHead` and `fHeadG`. -/
theorem owesS_fHeadG (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadG Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread SaidOk b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS L.thread SaidOk b c)
    (hX : ∀ b, b < L.thread.bs.length → ∀ i ∈ (L.thread.row b).owes,
      ExchangeAtS L.thread SaidOk b i)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → i ∈ L.thread.opened b →
      i ∉ (L.thread.row b).shuts → i ∉ (L.thread.row b).owes → rideOkF p i = true →
      RidesPastAtS L.thread SaidOk b i) : OwesS L.thread SaidOk := by
  subst hL
  exact owesS_head_form h H Q test carryX item n₁ n₂ b₀ Vd (csHead ν st R)
    (fHeadG Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) w SaidOk rfl hP hF
    (fHeadG_hK h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hB hF)
    h₀
    (fun b _ c hc h1 h2 => head_staysBy_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk))
      (fHead_hst_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ _ _ _ _ w hσ b c hc h1 h2))
    hl hX
    (head_hR_of_cellsF h H Q test carryX item n₁ n₂ b₀ Vd _ _ w SaidOk hok)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.border_at
#print axioms ProofFile.Honest.FirstThread.head_rels
#print axioms ProofFile.Honest.FirstThread.fHeadG_hK
#print axioms ProofFile.Honest.FirstThread.owesS_fHeadG
