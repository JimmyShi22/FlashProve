-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/BehindAt.lean: the code switch as a piece (PieceAt.lean): WHAT THE LAW READS
OF THE TYPED STATEMENT BEHIND, and the law of the piece's own reduction under a premise that a
reading can meet.

A STATEMENT TURNS; OLD BESIDE NEW.
  OLD (`BehindIs`, PieceAt.lean; `k2_leads`): one function fb gives back, from the piece's statement
    behind (the record behind and the oracles behind), THE VERY typed statement behind that `lawOut`
    puts out: fb a' = b₂.
  NEW (`BehindAlike`; `k2_leads_alike`): fb a' and b₂ are `Alike`: the same matrix of each sample's
    seed, the same answers, the same words, the same part of the carried joint.
  WHY: the elder could hardly be met. The record keeps a new message's sample ROWS, not its seed
    (K2Hears/SeedBehind.lean), and nothing known here keeps the drawn
    positions as such; the typed statement behind holds both. The conclusion of the law does not
    turn; the premise gets weaker (`behindAlike_of_is`), so the theorem stronger. PieceAt.lean does
    not turn.

Main names:
  `val_of_mat`, `decMin_congr`, `dec_congr`: the library's decoder with a sample (`OMsg.dec`,
    Cb/Ld/LdSig.lean) reads a seed through its matrix `Z.mat` alone.
  `Alike`: the four agreements.
  `rb_alike`: THE LEMMA WITH CONTENT: `lawRb` (what stands behind; LawAt.lean) reads of the typed
    statement behind THESE FOUR ALONE: it does not tell two statements that are alike apart. The
    laid rows are read off the record; the claim, the drawn positions with the open word's symbols
    there, and the rider's word are not read at all.
  `BehindAlike`, `behindAlike_of_is`, `k2_leads_alike`.
What stays a premise of `k2_leads_alike`, one by one: r.ok; r.writtenOK; `K2Wr`; hon; hpr;
`LawAfter` at the piece's own shown columns; `BehindAlike` (paid in BehindPaid.lean from two named
premises). Letters: as in PieceAt.lean.
Limits: those of PieceAt.lean. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.PieceAt
import Johnson.Top.H0.K2Caller.AfterAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim noDigest chainAt viewWordsBelowPrime)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

/-! ### The decoder reads a seed through its matrix alone -/

theorem val_of_mat {E J : Type} [Field E] [Fintype J] (Z : Ood.Sample E J) {ρ ρ' : Z.D}
    (h : Z.mat ρ = Z.mat ρ') : Z.val ρ = Z.val ρ' := by
  funext u s
  show ∑ j, Z.mat ρ s j * u j = ∑ j, Z.mat ρ' s j * u j
  rw [h]

theorem decMin_congr {T U D Y : Type} (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ)
    {ρ ρ' : D} (y : Y) (h : ev ρ = ev ρ') :
    Ood.decMin dist rank view ev e ρ y = Ood.decMin dist rank view ev e ρ' y := by
  have hF : Ood.First dist rank view ev ρ y = Ood.First dist rank view ev ρ' y := by
    funext t
    unfold Ood.First
    rw [h]
  unfold Ood.decMin
  rw [hF]

/-- **Two samples with one matrix and the same answers decode alike.** -/
theorem dec_congr {E : Type} [Field E] (o : OMsg E) (f : o.Str) {σ σ' : o.Smp}
    (hm : o.Z.mat σ.1 = o.Z.mat σ'.1) (ha : σ.2 = σ'.2) : o.dec f σ = o.dec f σ' := by
  unfold OMsg.dec
  rw [ha]
  exact decMin_congr _ _ _ _ _ _ (val_of_mat o.Z hm)

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)

/-- The typed statements behind. -/
abbrev TB := (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.X ×
  ((Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.Ex.prod (portCode r.cs r.rider).nat).Str

/-- **Alike in what the law reads**: the samples' matrices, the answers, the words, the carried
joint's part. -/
structure Alike (b b' : TB X iJ iQ) : Prop where
  mat : ∀ i, ((selLoc X iJ iQ).S.om i).Z.mat (b.1.2 i).1 = ((selLoc X iJ iQ).S.om i).Z.mat (b'.1.2
      i).1
  ans : ∀ i, (b.1.2 i).2 = (b'.1.2 i).2
  words : b.2.1.2 = b'.2.1.2
  carried : (b.1.1.2, b.2.1.1) = (b'.1.1.2, b'.2.1.1)

/-- **What stands behind does not tell two such statements apart.** -/
theorem rb_alike (p : K2.P2) (Yt : Type) (a : Rec × Yt) (s' : Rec) {b b' : TB X iJ iQ}
    (h : Alike X iJ iQ b b') (wt) (hw : lawRb X iJ iQ p Yt a (s', b) wt) :
    lawRb X iJ iQ p Yt a (s', b') wt := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨fun i => ?_, h2, ?_⟩
  · have e := h1 i
    have e' : ((selLoc X iJ iQ).S.om i).dec (b.2.1.2 i) (b.1.2 i) = some (wt.1 i).1 := e
    show ((selLoc X iJ iQ).S.om i).dec (b'.2.1.2 i) (b'.1.2 i) = some (wt.1 i).1
    rw [← h.words, ← dec_congr _ _ (h.mat i) (h.ans i)]
    exact e'
  · have e : (selLoc X iJ iQ).A₁.relR (b.1.1.2, b.2.1.1) ((selLoc X iJ iQ).S.msgs wt.1, wt.2) := h3
    exact (congrArg (fun z => (selLoc X iJ iQ).A₁.relR z ((selLoc X iJ iQ).S.msgs wt.1, wt.2))
      h.carried).mp e

end

variable {F : Frame} {W : Type}

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (p : K2.P2) (base : ℕ)
  (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
  (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)

/-- **The named premise, in the shape that a reading can meet**: at every yes fb of the piece's
statement behind is ALIKE to the typed statement behind that `lawOut` puts out. -/
def BehindAlike (on : Rec × F.E.Str → Prop) (fb : Rec × F.E.Str → TB X iJ iQ) : Prop :=
  ∀ (a a' : Rec × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂])) b₂, on a →
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.out a τ = some a' →
    lawOut X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) a τ = some (a'.1, b₂) →
    Alike X iJ iQ (fb a') b₂

/-- The elder premise gives the new one. -/
theorem behindAlike_of_is {on : Rec × F.E.Str → Prop} {fb : Rec × F.E.Str → TB X iJ iQ}
    (h : BehindIs (W := W) X iJ iQ d₁ d₂ ρ p base ext strs inX on fb) :
    BehindAlike (W := W) X iJ iQ d₁ d₂ ρ p base ext strs inX on fb := fun a a' τ b₂ ha ho hl => by
  rw [h a a' τ b₂ ha ho hl]
  exact ⟨fun _ => rfl, fun _ => rfl, rfl, rfl⟩

end

set_option maxHeartbeats 2000000 in
/-- **The law of the code switch, of the piece's own reduction, with its level, under the weaker
premise.** -/
theorem k2_leads_alike {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) (p : K2.P2) (base : ℕ)
    (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X) (on : Rec × F.E.Str → Prop)
    (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (selZ X iJ iQ)).on (lawFa X iJ iQ strs inX a))
    (hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (lawFa X iJ iQ strs inX a))
    (hA : LawAfter X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on)
    (fb : Rec × F.E.Str → TB X iJ iQ)
    (hB : BehindAlike X iJ iQ d₁ d₂ ρ p base ext strs inX on fb) :
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.Leads on
      (fun a a' => ∀ wt, lawRb X iJ iQ p F.E.Str a (a'.1, fb a') wt →
        ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX a)
            (selBk X iJ iQ wt) ∧
        ∀ k : (selHd X iJ iQ).K,
          ((selHd X iJ iQ).o k).decW ((selHd X iJ iQ).sW k (lawFa X iJ iQ strs inX a).2.1.1)
              ((lawFa X iJ iQ strs inX a).1.1.1.2 k) =
            some ((selHd X iJ iQ).msg (cutSel r.cs r.l iJ iQ (selNew X iJ iQ wt)).1 k))
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ∧
    Err.Below (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) := by
  have L := law_at h hW X iJ iQ d₁ d₂ ρ w p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on hon hpr
    hA
  refine ⟨fun a ha => Doomed.mono _ _ ?_ (L.1 a ha), L.2⟩
  intro τ hτ a' ha' wt hw
  obtain ⟨b₂, hb⟩ := piece_is_lawOut X iJ iQ d₁ d₂ ρ p base ext strs inX w a a' τ ha'
  exact hτ (a'.1, b₂) hb wt (rb_alike X iJ iQ p F.E.Str a a'.1 (hB a a' τ b₂ ha ha' hb) wt hw)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.dec_congr
#print axioms VerifiableInference.Desc.First.K2Caller.rb_alike
#print axioms VerifiableInference.Desc.First.K2Caller.behindAlike_of_is
#print axioms VerifiableInference.Desc.First.K2Caller.k2_leads_alike
