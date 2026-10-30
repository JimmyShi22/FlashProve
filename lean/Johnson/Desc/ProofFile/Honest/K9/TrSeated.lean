-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TrSeated.lean: K11's MERGE; K4's, K8's AND K1's SUB-PROTOCOLS AS THE DESCRIPTION SEATS THEM;
THE STEPS WITHOUT A ROUND BEHIND THE READS AND BEHIND A LOOKUP: an accepting decision is `KeepsTr`.

One of nine files (Honest/K9/TrAre.lean, TrFl, TrWalk, TrK4, TrK5, TrK6, TrSeated, TrVia, TrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves the ledger's arrays, but for the mark
"the commitment is received" (`tr`), and what the batching's draw will test of the segment's book-keeping (`lnk`). They are the
nine files Honest/K9/TrAre.lean to TrLot.lean, carried over by program from the reading `tr` to the reading `tr`, name by name;
these in turn carry the library's own walk for the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files
Slots*.lean beside it).

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.TrK4
import Johnson.Desc.ProofFile.Honest.K9.TrK5
import Johnson.Desc.ProofFile.Honest.K9.TrK6
import Johnson.Desc.First.Link.Law.LooksSeated
import Johnson.Desc.First.Link.Law.LooksFrame
import Johnson.Desc.First.Link.Law.LooksK3
import Johnson.Goal.Meaning.KeepsDriver
import Johnson.Goal.Meaning.RecReadsAtt
import Johnson.Desc.First.Look.K3Stated
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.K1.Places
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.BlockKeeps
import Johnson.Desc.Kinds.Law.Heard
import Johnson.Desc.First.Fork.MergeKind
import Johnson.Desc.ProofFile.Lots.Makers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Johnson.Desc.First.ForkMerge (mergeHear headMergeDecide headClaimMergeKind)

/-! ## K11 -/

/-- The merge's hearing leaves the reading. -/
theorem mergeHear_tr {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork}
    {t u : Tape} {wo : WsForkOut} (h : mergeHear lay cl sv F t = .ok (wo, G, u)) :
    FlT.SameTr F G := by
  unfold mergeHear at h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨⟨rho, F1, t1⟩, e1, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨v, F2, t2⟩, e2, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨p, F3, t3⟩, e3, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨⟨rm, p4⟩, F4, t4⟩, e4, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨⟨sFv, p5⟩, F5, t5⟩, e5, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨fvp, F6, t6⟩, e6, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain rfl : F6 = G := congrArg (·.2.1) (Except.ok.inj h)
  exact (((((FlT.StaysT.same (named_some e1)).trans (FlT.StaysT.same (named_some e2))).trans
    (FlT.StaysT.same (named_some e3))).trans (FlT.StaysT.same (named_some e4))).trans
    (FlT.StaysT.same (named_some e5))).trans (FlT.StaysT.same (named_some e6))

/-- **K11: the merge of the claims on the weights.** -/
theorem k11_stepsT (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    (headClaimMergeKind P).Steps (KeepsTr) := by
  intro s rs gs s' h
  have h' : headMergeDecide P s rs = .ok s' := h
  unfold headMergeDecide at h'
  split at h'
  · rename_i a ha
    obtain ⟨_, ho, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨t, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨claim, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨x, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨⟨wo, F, t'⟩, hm, h'⟩ := K9L.ok_bind h'
    dsimp only at h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    have hop : a.opened = true := by
      cases e : a.opened with
      | true => rfl
      | false =>
        rw [e] at ho
        exact nomatch ho
    obtain rfl := Except.ok.inj h'
    refine keeps_of_casesT fun G' L' hG hL' => ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, ha, hop]
    · simp [S.link?, ha, hop]
    · have e : some a.L = some L' := by simpa [S.link?, hop] using hL'
      exact congrArg lnk (Option.some.inj e)
    · have e : some ({ F with planClaimsF := P.nLin } : Fork) = some G' := by
        simpa [S.fork?, hop] using hG
      rw [← Option.some.inj e]
      exact (mergeHear_tr hm : tr F = tr a.F)
  · exact nomatch h'

/-! ## The kinds' makers as the lots seat them -/

theorem k4C_stepsT (p : OnBytes.Desc.First.K4.Par) :
    (OnBytes.Desc.First.K4.blockAtC p).Steps (KeepsTr) :=
  fun s rs gs s' h => k4_stepsT p s rs gs s' h

theorem k8W_stepsT (p : First.K8.ParW) : (First.K8.whole p).Steps (KeepsTr) :=
  fun s rs gs s' h => k8_stepsT (Cl := Claim) p.toPar s rs gs s' h

theorem k1Later_stepsT {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.laterAt (Cl := Cl) q gp link piece moment arrays).Steps (KeepsTr) :=
  k1_stepsT _ link moment arrays

theorem readsLay_stepsT (P : K8.ReadsQuiet.PG) :
    (K8.ReadsQuiet.layers P).Steps (KeepsTr) := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact keeps_sameT (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsHead_stepsT (P : K8.ReadsQuiet.PH) :
    (K8.ReadsQuiet.head P).Steps (KeepsTr) := by
  intro s rs gs s' h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact keeps_sameT (by simp [S.fork?, ha]) (by simp [S.link?, ha])

theorem readsAtt_stepsT {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : b.Steps (KeepsTr) := by
  unfold First.Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' e
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq (A := A) e
  exact keeps_sameT (by simp [S.fork?, ha]) (by simp [S.link?, ha])

/-- The steps without a round behind a lookup. -/
theorem quietAt_keepsT {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : KeepsTr s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → KeepsTr s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, hF, k⟩ := K9L.ok_bind k
    obtain ⟨G, hG, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    have hF' := named_some hF
    have hG' := named_some hG
    unfold First.Look.slotsTaken at hG'
    split at hG'
    · obtain rfl := Option.some.inj hG'
      refine keeps_of_casesT fun G' L' e1 e2 => ⟨F, L', hF', ?_, rfl, ?_⟩
      · rw [← link_putFork s]
        exact e2
      · rw [fork_putFork s F hF'] at e1
        rw [← Option.some.inj e1]
        rfl
    · exact nomatch hG'
  have hd : K3.quietHead X s = .ok t → KeepsTr s t := by
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
      exact keeps_sameT (by simp [S.fork?, ha]) (by simp [S.link?, ha])
    · exact nomatch k
  have lq : ∀ fs, K3.quietLook fs s = .ok t → KeepsTr s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact keeps_reflT s
  unfold K3.quietAt at hf
  dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact dig _ _ h)
    | (obtain rfl := Option.some.inj hf
       first
         | exact hd h
         | exact lq _ h)
    | cases hf

theorem k1Later_wholeT {Cl : Type} (q : Params.First) (gp : _) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Whole (KeepsTr) (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  ⟨k1Later_stepsT q gp link piece moment arrays, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem readsLay_wholeT (P : K8.ReadsQuiet.PG) :
    Whole (KeepsTr) (K8.ReadsQuiet.layers P) :=
  ⟨readsLay_stepsT P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem readsHead_wholeT (P : K8.ReadsQuiet.PH) :
    Whole (KeepsTr) (K8.ReadsQuiet.head P) :=
  ⟨readsHead_stepsT P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem readsAtt_wholeT {Cl : Type} {W : Verify.Public} {l g : ℕ} {b : Block S Cl}
    (h : First.Att.readsAtO W l g = some b) : Whole (KeepsTr) b := by
  refine ⟨readsAtt_stepsT h, ?_, ?_⟩ <;>
    (unfold First.Att.readsAtO at h
     obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
     exact fun _ hc => nomatch hc)

theorem readsBlockAt_wholeT {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (ℕ × ℕ)} {l : ℕ} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole (KeepsTr) b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact readsLay_wholeT _
  · split at h
    · cases h
      exact readsHead_wholeT _
    · cases h

/-- The step behind the reads' sending, as the lots make it. -/
theorem readsQuietAt_wholeT {G : ProofFile.Ground} {l : ℕ} {X : Stages.LinkH} {piece : ℕ}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) :
    Whole (KeepsTr) b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtt_wholeT h
    | exact readsBlockAt_wholeT h
    | cases h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mergeHear_tr
#print axioms VerifiableInference.Desc.LinkJoin.k11_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.k4C_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.k8W_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.readsLay_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.readsHead_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.readsAtt_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_keepsT
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_wholeT
#print axioms VerifiableInference.Desc.LinkJoin.readsLay_wholeT
#print axioms VerifiableInference.Desc.LinkJoin.readsHead_wholeT
#print axioms VerifiableInference.Desc.LinkJoin.readsAtt_wholeT
#print axioms VerifiableInference.Desc.LinkJoin.readsBlockAt_wholeT
#print axioms VerifiableInference.Desc.LinkJoin.readsQuietAt_wholeT
