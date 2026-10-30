-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/OpenedAtHead.lean: the member at a link's first place of the proof file's own
first chain: the lot's sub-protocol there (a commitment at link 0, a code switch at the links 1 to
23) WITH THE FRAME's "opened" JOINED BEHIND IT: what the seated member's decision is, half by half.
One definition, six theorems. A joining of laws; nothing is evaluated.

  `Keeps f`: a text that, where it returns, leaves the mark of failure and the heard reply.
    `keeps_lay`, `keeps_att`, `keeps_zero`: the three texts of "opened" do.
  **`joined_iff`**: for b "the lot's sub-protocol b' with the row f's opened joined" (IM.Joined), at
    a place that does not hear the reply, and f.opened in Keeps: b's decision accepts from s to t
    just if b' accepts from s to some m at its own rounds and columns, m bears no mark, m has s's
    reply, and f.opened m = .ok t. BOTH WAYS: the library's IM.Joined.yes is the way from an accept.
  `sub_kind` (under the head P5J.AtMgA, Johnson/P5J/MgAtAll.lean), `first_kind`: small facts on a
    link's sort and on the kind at its first place.

The member itself under the head, with its second half's step named and every parameter tied to a
value, is stated in SeatsNamed.lean (opened_att_named, opened_lay_named).

Limits. THE FIRST HALF (the commitment; the code switch) HAS NO STEP HERE: it is another kind's. At
the earlier hash OnBytes.secondHashFunction (sub_kind). Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Walk.Shape.FrameEnds
import Johnson.P1L20R.FrameSits
import Johnson.AtFull.Shape.PlansAtHead
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching hearsReply)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame framesOf_arms fvsOf)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)

/-! ## 1 The seated member's decision, half by half -/

/-- Where the text returns it leaves the mark of failure and the heard reply. -/
def Keeps (f : S → Except String S) : Prop :=
  ∀ m t, f m = .ok t → t.failed = m.failed ∧ t.out.reply = m.out.reply

theorem keeps_lay (P : LayPar) : Keeps (openLay P) := fun m t h => by
  obtain ⟨-, rfl⟩ := openLay_lays h
  exact ⟨rfl, rfl⟩

theorem keeps_att (P : AttPar) : Keeps (openAtt P) := fun m t h => by
  obtain ⟨-, rfl⟩ := openAtt_lays h
  exact ⟨rfl, rfl⟩

theorem keeps_zero (P : LayPar) (fvs : List Bool) (kCol : Nat) :
    Keeps (openLayZero P fvs kCol) := fun m t h => by
  obtain ⟨-, im, -, rfl⟩ := openZero_lays h
  exact ⟨rfl, rfl⟩

theorem joined_iff {b b' : Block S ProofFile.Cl} {a : Place} {f : LinkFrame}
    (e : b = IM.seatedWith ProofFile.sameReply b' (ProofFile.guardMark (IM.openedOf f).retype) b.name a)
    (hk : a.kind ≠ KindName.K7) (hO : Keeps f.opened) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      ∃ m, b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok m ∧
        m.failed = none ∧ ProofFile.sameReply s m = true ∧ f.opened m = .ok t := by
  have hp : hearsReply a = false := by
    show (a.kind == KindName.K7) = false
    simpa using hk
  have ed : b.decide s rs gs = (IM.seatedWith ProofFile.sameReply b'
      (ProofFile.guardMark (IM.openedOf f).retype) b.name a).decide s rs gs :=
    congrArg (fun y : Block S ProofFile.Cl => y.decide s rs gs) e
  rw [ed]
  unfold IM.seatedWith
  rw [VerifiableInference.Desc.guarded_yes ProofFile.sameReply hearsReply _ hp]
  show (((ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings)).bind
      (fun s' => ((ProofFile.guardMark (IM.openedOf f).retype).guarded ProofFile.sameReply
        fun _ => false).decide s' (rs.drop b'.rounds.length) (gs.drop b'.openings)) = .ok t ∧
      ProofFile.sameReply s t = true) ↔ _
  constructor
  · rintro ⟨hy, hst⟩
    cases hd : (ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings) with
    | error w => rw [hd] at hy; exact nomatch hy
    | ok m =>
      rw [hd] at hy
      obtain ⟨h1, h2⟩ := (IM.guardMark_yes b' s m _ _).1 hd
      obtain ⟨h3, -⟩ := (VerifiableInference.Desc.guarded_yes ProofFile.sameReply (fun _ => false)
        (ProofFile.guardMark (IM.openedOf f).retype) rfl m _ _ t).1 hy
      obtain ⟨h5, -⟩ := (IM.guardMark_yes _ m t _ _).1 h3
      have h5' : f.opened m = .ok t := h5
      refine ⟨m, h1, h2, ?_, h5'⟩
      unfold ProofFile.sameReply at hst ⊢
      rw [← (hO m t h5').2]
      exact hst
  · rintro ⟨m, h1, h2, h3, h4⟩
    obtain ⟨k1, k2⟩ := hO m t h4
    have hd : (ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings) =
        .ok m := (IM.guardMark_yes b' s m _ _).2 ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hd]
      refine (VerifiableInference.Desc.guarded_yes ProofFile.sameReply (fun _ => false)
        (ProofFile.guardMark (IM.openedOf f).retype) rfl m _ _ t).2
        ⟨(IM.guardMark_yes _ m t _ _).2 ⟨h4, k1.trans h2⟩, ?_⟩
      unfold ProofFile.sameReply
      rw [k2]
      exact beq_self_eq_true _
    · unfold ProofFile.sameReply at h3 ⊢
      rw [k2]
      exact h3

/-! ## 2 A link's sort, under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem sub_kind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {Y : Stages.LinkH} (hY : Zp.p.built.links[l]? = some Y) : ProofFile.subOf Y.kind = subAt l := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have h2 := IM.subs_scope h.scope h.reads O l hl
  unfold ProofFile.subsOf at h2
  rw [List.getElem?_map, Array.getElem?_toList, hY] at h2
  exact Option.some.inj h2

/-! ## 3 The kind at a link's first place -/

theorem first_kind (l : Nat) (hl : l < 24) :
    ∃ k, (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k ∧ k ≠ KindName.K7 := by
  have hs : subAt l ≠ .head := by
    unfold subAt
    rw [if_neg (by omega)]
    split <;> exact fun e => nomatch e
  cases hq : subAt l with
  | head => exact absurd hq hs
  | layers => cases (l == 0) <;> exact ⟨_, rfl, fun e => nomatch e⟩
  | attention => cases (l == 0) <;> exact ⟨_, rfl, fun e => nomatch e⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.joined_iff
#print axioms Johnson.AtFull.Shape.Keeps
#print axioms Johnson.AtFull.Shape.keeps_lay
#print axioms Johnson.AtFull.Shape.keeps_att
#print axioms Johnson.AtFull.Shape.keeps_zero
#print axioms Johnson.AtFull.Shape.sub_kind
#print axioms Johnson.AtFull.Shape.first_kind
