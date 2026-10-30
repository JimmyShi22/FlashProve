-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrontStays.lean: WHAT AlikeFront COMPARES, BUT FOR THE LEDGER,
IS LEFT AS IT WAS BY THE DECISIONS OF THE FIVE SUB-PROTOCOLS BETWEEN THE OUTPUT HEAD's OWN ROUNDS
AND ITS BATCHING (342 to 346). After the pattern of FunsStay.lean, lemma for lemma.
Why. K6HeardAt (Johnson/Desc/Kinds/Law/K6Claims.lean) is carried along AlikeFront
(k6HeardAt_front); Johnson/Desc/Kinds/Law/K6PromiseBorder.lean says: KeepsK6 is shown of none:
each kind's. This file holds the equalities' half; K6HeardAtBatch.lean the ledger's and the walk.
  frontSix s        at a state in the head's segment: x, squaresP, opened, lookHeard; else none;
                   beside: the reply and the request
  SameFront s s'   frontSix s' = frontSix s · sameFront_trans
  the writes       putTl_front · putFork_front · front_put (the commitment's three) · mark_front ·
                   putDigits_front (the digits' seat's put)
  the decisions    commitAtS_front · k8_front (K8.whole) · k1Quiet_front · k1Reads_front (on two
                   rounds) · quietAt_front · **k3Digits_front** (K3.theStated's value AT THE DIGITS'
                   ADDRESS, its test on the plan passed) · k11_front (headClaimMergeKind)
AT THE CALLS' ADDRESS IT IS NOT SO: there the seat's put calls S.hearLook, which lays lookHeard
and x.g1. So StretchKeeps' field k3 (StretchBack.lean: every address) is not met by SameFront.
Limits. ON THE DECISIONS ALONE: nothing on the runs of claims. That a seated sub-protocol is one of
these texts is the seats' files'. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.K5AtLater
import Johnson.Desc.First.K8.LawLeaves
import Johnson.Desc.First.Look.K3DigitsSeatedYes
import Johnson.Top.H.Keep.PadExact
import Johnson.Desc.First.Fork.MergeKind
import Johnson.Desc.Kinds.Law.K6Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K1 (commitAtS laterAt laid commitAtS_slots joined_yes k1Quiet_decides)
open VerifiableInference.Desc.K3 (seatDigits)
open VerifiableInference.OnPublicFiles (theStated_yes_digits decide_exact)
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.ForkMerge (headMergeDecide headClaimMergeKind)

/-- What AlikeFront (Johnson/Desc/Kinds/Law/RunsFixedFront.lean) compares, but for the ledger. -/
def frontSix (s : S) :=
  ((match s.here with
    | .head o => some (o.x, o.squaresP, o.opened, o.lookHeard)
    | _ => none), s.out.reply, s.req)

/-- It is left as it was. -/
def SameFront (s s' : S) : Prop := frontSix s' = frontSix s

theorem sameFront_trans (a b c : S) (h : SameFront a b) (k : SameFront b c) : SameFront a c :=
  Eq.trans k h

theorem putTl_front (s : S) (tl : HTailF2) : frontSix (s.putTl tl) = frontSix s := by
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [S.putTl, frontSix, hs, ho]
  | _ => simp [S.putTl, frontSix, hs]

theorem putFork_front (s : S) (F : Fork) : frontSix (s.putFork F) = frontSix s := by
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [S.putFork, frontSix, hs, ho]
  | _ => simp [S.putFork, frontSix, hs]

/-- The commitment's three writes. -/
theorem front_put (s : S) (w : _root_.Desc.Plain.DState Unit) (L' : LinkCtx) (F' : Fork) :
    frontSix (((laid s w).putLink L').putFork F') = frontSix s := by
  cases hs : s.here with
  | head a =>
    by_cases ho : a.opened = true <;> simp [S.putFork, S.putLink, frontSix, laid, hs, ho]
  | _ => simp [S.putFork, S.putLink, frontSix, laid, hs]

theorem commitAtS_front {Cl : Type} (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides SameFront (commitAtS P link moment arrays : Block S Cl) := by
  intro s rs gs s' h
  obtain ⟨_, F, _, y, _, hF, _, e, hs⟩ := commitAtS_slots h
  show frontSix s' = frontSix s
  rw [e]
  exact front_put s _ _ _

theorem k8_front (p : First.K8.ParW) : Decides SameFront (First.K8.whole p) :=
  fun s rs gs s' h => First.K8.hear_leaves (Cl := Claim) frontSix putTl_front p.toPar s rs gs s' h

theorem k1Quiet_front (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides SameFront (IM.k1Quiet G l X) := by
  refine k1Quiet_decides _ (fun P s rs gs s' h => ?_) (fun P s rs gs s' h => ?_)
    (fun A s s' h => ?_) G l X
  · obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
    simp [SameFront, frontSix, ha]
  · obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
    simp [SameFront, frontSix, ha]
  · obtain ⟨a, t, tl, ha, rfl⟩ := _root_.Meaning.K2.readsAtSO_eq h
    simp [SameFront, frontSix, ha]

theorem k11_front (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Decides SameFront (headClaimMergeKind P) := by
  intro s rs gs s' h
  have h' : headMergeDecide P s rs = .ok s' := h
  unfold headMergeDecide at h'
  split at h'
  · rename_i a ha
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨t, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨claim, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨x, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨⟨wo, F, t'⟩, _, h'⟩ := K9L.ok_bind h'
    dsimp only at h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain rfl := Except.ok.inj h'
    simp [SameFront, frontSix, ha]
  · exact nomatch h'

theorem mark_front (s : S) (w : String) : frontSix (s.mark w) = frontSix s := by
  unfold S.mark
  split <;> rfl

theorem putDigits_front {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    frontSix ((seatDigits claim).put s g G) = frontSix s := by
  show frontSix (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test") = frontSix s
  split
  · exact (putFork_front _ G).trans (putTl_front s _)
  · exact mark_front s _

/-- The steps without a round behind a lookup. -/
theorem quietAt_front {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : SameFront s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → SameFront s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, _, k⟩ := K9L.ok_bind k
    obtain ⟨G, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact putFork_front s _
  have hd : K3.quietHead X s = .ok t → SameFront s t := by
    intro k
    unfold K3.quietHead at k
    split at k
    · rename_i a ha
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain rfl := Except.ok.inj k
      simp [SameFront, frontSix, ha]
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → SameFront s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact rfl
  unfold K3.quietAt at hf
  dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact dig _ _ h)
    | (obtain rfl := Option.some.inj hf
       first
         | exact hd h
         | exact lk _ h)
    | cases hf

/-- **The seated lookup on the digits.** (At the calls' address it is not so: there the hearing is
laid.) -/
theorem k3Digits_front {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) : Decides SameFront B := by
  intro s rs gs c hd
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  obtain ⟨F₁, y, -, -, e, -⟩ :=
    decide_exact (K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  have h1 : SameFront s s' := by
    show frontSix s' = frontSix s
    rw [e]
    exact putDigits_front claim s y.1 y.2
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact h1
  · exact sameFront_trans _ _ _ h1 (quietAt_front hf hfs)

/-- **The reads' place's sub-protocol**, on two rounds. -/
theorem k1Reads_front (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (IM.k1Reads Z G l X pr reads).decide s [r₁, r₂] gs = .ok s') : SameFront s s' := by
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes _ _ _ _ _ _ s s' r₁ r₂ gs h
  exact sameFront_trans _ _ _ (commitAtS_front _ _ _ _ _ _ _ _ h1) (k1Quiet_front G l X _ _ _ _ h3)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.commitAtS_front
#print axioms VerifiableInference.Desc.LinkJoin.k8_front
#print axioms VerifiableInference.Desc.LinkJoin.k1Quiet_front
#print axioms VerifiableInference.Desc.LinkJoin.k1Reads_front
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_front
#print axioms VerifiableInference.Desc.LinkJoin.k3Digits_front
#print axioms VerifiableInference.Desc.LinkJoin.k11_front
