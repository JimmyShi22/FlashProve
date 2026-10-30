-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/K2Share/K2Whole.lean: the code switch's kind's two steps for the chain's
general rules (Johnson/Desc/FoldKeeps.lean: Whole R b): the statement only grows
(Johnson/Desc/Grows.lean); and RecAll (Johnson/Goal/Meaning/RecAll.lean) is handed on.


  grows_newGroupG, grows_joinG, grows_joins, grows_ledgerG, grows_addRowsG: the switch's own forms
    of the plain ground's changes, by Johnson/Desc/GrowsGround.lean.
  grows_sent: SentOk (K2Hears/SentKeeps.lean) gives Grows.
  grows_switch: behind a yes of switchE switchBehind (par9 p) sendByL8 at a front x: Grows x.st
    w.st.
  k2_grows: Whole (GrowsBy (·.st)) (codeSwitchKind p): K2's step for StatementGrows.lean's premise.
  k2_recAll: Whole (RecRel cs sh) (codeSwitchKind p), RecRel cs sh (Johnson/Goal/Meaning/RecRel.lean) being the
    relation fun s s' => RecAll cs sh s → RecAll cs sh s'.
LIMITS. The switch's kind alone. No soundness is claimed.
-/
import Johnson.Goal.Meaning.K2Share.RecKept
import Johnson.Goal.Meaning.RecRel
import Johnson.Desc.GrowsGround
import Johnson.Desc.StatementGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Keeps (Whole Decides)
open VerifiableInference.Desc.ChainEnd (GrowsBy)
open Meaning.K2 (RecAll RecRel FramePub framesIn)
open _root_.Tw.K2 (switchNotices firstFront firstBehind sendByL8 switchE switchBehind addRowsG dOf
  SwOut newGroupG joinG closeLedgerG)

theorem grows_newGroupG {S S' : Statement} {c z g : Nat} (h : newGroupG S c z = .ok (S', g)) :
    Grows S S' := by
  unfold newGroupG at h
  split at h
  · rename_i g' d hd
    have k := Ground.newGroupP_grows (dOf S) d c z g' hd
    cases h
    exact k
  · cases h

theorem grows_joinG {S S' : Statement} {g o : Nat} {kept : Bool}
    (h : joinG S g o kept = .ok S') : Grows S S' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    exact Ground.joinP_grows (dOf S) d g o kept hd
  · cases h

theorem grows_joins {α : Type} (g : Nat) (f : α → Nat) (k : α → Bool) : ∀ (l : List α)
    (S S' : Statement), l.foldlM (fun S p => joinG S g (f p) (k p)) S = .ok S' → Grows S S'
  | [], S, S', h => by
    cases h
    exact Grows.refl S
  | p :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bindOk h
    exact (grows_joinG h1).trans (grows_joins g f k l S1 S' h2)

theorem grows_ledgerG {S S' : Statement} {o : Nat} (h : closeLedgerG S o = .ok S') :
    Grows S S' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    exact Ground.closeLedgerP_grows (dOf S) d o hd
  · cases h

theorem grows_addRowsG {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG S g rows = .ok S') : Grows S S' := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    exact Ground.addRowsP_grows (dOf S) d g rows hd
  · cases h

/-- A sending that is SentOk grows the statement. -/
theorem grows_sent {S S' : Statement} {N : Array OracleNotice} {ids : Array Nat}
    (K : SentOk S N ids S') : Grows S S' := by
  refine ⟨K.codes, fun i G hG => ⟨G, by rw [K.groups]; exact hG, GroupGrows.refl G⟩,
    fun i x hx => ⟨x, ?_, OracleGrows.refl x⟩⟩
  have hi : i < S.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  rw [K.old i hi]
  exact hx

/-- **Behind a yes of the switch the statement has grown.** -/
theorem grows_switch {p : P2} {s9 : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView}
    {cols w roots}
    (h : switchE switchBehind (par9 p) sendByL8 s9 x r₁ r₂ cols = .ok (w, roots)) :
    Grows x.st w.st := by
  obtain ⟨y, hs⟩ := switchE_inv h
  obtain ⟨c, Y, S1, S2, S3, rows, hb⟩ := switchBehind_inv hs.hBehind
  have a0 : Grows x.st y.st := grows_sent (sent_ok hs.hSend)
  have a1 : Grows y.st S1 := by
    have hl := hb.hLedger
    split at hl
    · exact grows_ledgerG hl
    · cases hl
      exact Grows.refl _
  have a2 : Grows S1 S2 := grows_joinG hb.hJoinG
  have a3 : Grows S2 S3 := by
    have hk := hb.hJoinKept
    rw [← Array.foldlM_toList] at hk
    exact grows_joins (α := Nat × KeptTarget) _ (fun p => p.1) (fun p => p.2.keptAgain) _ S2 S3 hk
  exact (((a0.trans a1).trans a2).trans a3).trans (grows_addRowsG hb.hAdded)

theorem grows_front {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S0 f = .ok x) : Grows S0 x.st := by
  unfold firstFront at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · dsimp only at h
        split at h
        · cases h
        · rename_i S' g hn
          cases h
          exact grows_newGroupG hn
      · cases h
      · cases h

theorem grows_behind {S S' : Statement} {x : _root_.Tw.K2.Front} {sw : Switched} {plain : List E}
    {f : ReqFrame} {mine : Array Nat} (h : firstBehind S x sw plain = .ok (S', f, mine)) :
    Grows S S' := by
  unfold firstBehind at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i S1 hj
          have hs := grows_joins (α := Params.ReqMessage × Nat) _ (fun y => y.2)
            (fun y => decide (0 < y.1.life)) _ S S1 hj
          cases h
          exact hs

/-- **A yes of the switch's text grows the record's statement.** -/
theorem grows_kept {p : P2} {s s' : S} {rs gs} (h : decideWith sendByL8 p s rs gs = .ok s') :
    Grows s.st s'.st := by
  cases hp : p.stands with
  | link =>
    obtain ⟨r₁, r₂, x, w, roots, S', f, mine, -, L⟩ := link_inv hp h
    rw [L.hOut]
    exact ((grows_front L.hFront).trans (grows_switch L.hSwitch)).trans (grows_behind L.hBehind)
  | head =>
    obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := head_inv hp h
    rw [H.hOut]
    exact grows_switch H.hSwitch
  | finish =>
    obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := finish_inv hp h
    rw [H.hOut]
    exact grows_switch H.hSwitch

/-- **K2's step for "the statement only grows".** -/
theorem k2_grows {Cl : Type} (p : P2) : Whole (GrowsBy fun s : S => s.st) (codeSwitchKind (Cl := Cl) p) :=
  ⟨fun _ _ _ _ h => grows_kept h, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-! ## RecAll -/

theorem recPub_of_all {cs : Codes} {sh : ReqShape} {s : S} (R : RecAll cs sh s) :
    RecPub cs sh s :=
  ⟨R.codes, R.walk.shape, R.walk.groups, R.ok⟩

/-- **A yes of the switch hands RecAll on.** -/
theorem recAll_kept {cs : Codes} {sh : ReqShape} {p : P2} {s s' : S} {rs gs}
    (h : decideWith sendByL8 p s rs gs = .ok s') : RecRel cs sh s s' := by
  intro R
  have hc : s'.st.codes = cs := (grows_kept h).1.trans R.codes
  refine ⟨hc, ?_, R.ok⟩
  cases hp : p.stands with
  | link =>
    obtain ⟨r₁, r₂, x, w, roots, S', f, mine, -, L⟩ := link_inv hp h
    obtain ⟨f1, f2, -⟩ := behind_frame L.hBehind
    obtain ⟨g1, g2⟩ := front_frame L.hFront
    have hf : FramePub sh f :=
      R.walk.carry (f1.trans g1) (f2.trans g2)
        ((behind_carried L.hBehind).1.trans (front_carried L.hFront).1)
        ((behind_carried L.hBehind).2.trans (front_carried L.hFront).2)
    rw [L.hOut]
    intro f' hm
    have e : f' = f := by
      unfold framesIn at hm
      simpa [L.hHere, _root_.Johnson.Desc.First.Walk.firstKept] using hm
    rw [e]
    exact hf
  | head =>
    obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := head_inv hp h
    rw [H.hOut]
    intro f' hm
    refine R.frames f' ?_
    unfold framesIn at hm ⊢
    rw [H.hHere]
    exact hm
  | finish =>
    obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := finish_inv hp h
    rw [H.hOut]
    intro f' hm
    refine R.frames f' ?_
    unfold framesIn at hm ⊢
    rw [H.hHere]
    exact hm

/-- **K2's step for RecAll.** -/
theorem k2_recAll {Cl : Type} (cs : Codes) (sh : ReqShape) (p : P2) :
    Whole (RecRel cs sh) (codeSwitchKind (Cl := Cl) p) :=
  ⟨fun _ _ _ _ h => recAll_kept h, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.grows_switch
#print axioms VerifiableInference.Desc.First.K2.k2_grows
#print axioms VerifiableInference.Desc.First.K2.k2_recAll
