-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FunsStay.lean: THE SUB-PROTOCOLS THAT STAND BETWEEN THE MAKER OF A
SEGMENT's LIST
OF TABLES (`S.funs?`, Johnson/Desc/First/State.lean) AND THE BATCHING LEAVE THAT LIST AS IT WAS: at
a yes
of the decision. By the written list of places these are: the sending of the reads with its quiet
step (at a layers' segment alone a keeper: at an attention segment and the head that quiet step
MAKES
the list), the approximate range proof's hearing (K8), the sending of the digits (K1), the lookup on
the digits (K3), and at the head the merge (K11). Statements and proofs.

  `SameFuns s s'`: s'.funs? = s.funs?.
  PROVED IN OTHER FILES, GATHERED HERE IN ONE FORM: `k8_sameFuns` (`K8.hear_leaves_funs`),
`k1Later_sameFuns`
    (`K1.laterAt_funs`), `quietLayers_sameFuns` (`layers_funs`,
Johnson/Desc/K8/ReadsQuietFuns.lean).
  NEW: `hearLook_funs`, `mark_funs`; `via_sameFuns`: K3's decision at a seat whose laying leaves the
    list; `quietAt_sameFuns`: the three steps without a round behind a lookup; `k3_sameFuns`: **K3's
    sub-protocol at an address, with its runs stated: the decision leaves the list: no premise on
    the plan**; `k11_sameFuns`: **so does the merge's.**
Limits. ON THE DECISIONS ALONE: nothing on the runs of claims or on the runs behind the batching.
That
a seated sub-protocol is one of these texts is the seats' files' to show. Nothing on what the list
is. No soundness statement.

-/
import Johnson.Desc.First.K8.LawCondK1
import Johnson.Desc.First.K8.LawFunsStay
import Johnson.Desc.K8.ReadsQuietFuns
import Johnson.Desc.First.Link.Law.SlotsSeated
import Johnson.Desc.First.Link.Law.SlotsFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open Johnson.Desc.First.ForkMerge (headMergeDecide headClaimMergeKind)

/-- The list of tables is left as it was. -/
def SameFuns (s s' : S) : Prop := s'.funs? = s.funs?

theorem sameFuns_refl (s : S) : SameFuns s s := rfl

theorem sameFuns_trans (a b c : S) (h : SameFuns a b) (k : SameFuns b c) : SameFuns a c :=
  Eq.trans k h

/-- Two sub-protocols joined as one. -/
theorem andThen_sameFuns {Cl : Type} (nm : String) (p q : Block S Cl) (hp : Decides SameFuns p)
    (hq : Decides SameFuns q) : Decides SameFuns (Block.andThen nm p q) := by
  intro s rs gs s' h
  obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok h
  exact sameFuns_trans _ _ _ (hp _ _ _ _ h1) (hq _ _ _ _ h2)

/-! ## Proved in other files -/

theorem k8_sameFuns (p : First.K8.ParW) : Decides SameFuns (First.K8.whole p) :=
  fun s rs gs s' h => First.K8.hear_leaves_funs (Cl := Claim) p.toPar s rs gs s' h

theorem k1Later_sameFuns {Cl : Type} (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : ℕ) (arrays : Option (List ℕ)) :
    Decides SameFuns (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  fun s rs gs s' h => K1.laterAt_funs q gp link piece moment arrays s s' rs gs h

theorem quietLayers_sameFuns (P : K8.ReadsQuiet.PG) : Decides SameFuns (K8.ReadsQuiet.layers P) :=
    by
  intro s rs gs s' h
  obtain ⟨_, funs, _, _, h1, _, h2⟩ := K8.ReadsQuiet.layers_funs h
  exact h2.trans h1.symm

/-! ## The writings -/

theorem mark_funs (s : S) (w : String) : (s.mark w).funs? = s.funs? := by
  unfold S.mark
  split <;> rfl

theorem hearLook_funs (s : S) (g : Forest.Heard) : (s.hearLook g).funs? = s.funs? := by
  unfold S.hearLook
  split
  · rename_i a ha
    split
    · exact mark_funs s _
    · simp [S.funs?, ha]
  · rename_i a ha
    split
    · exact mark_funs s _
    · simp [S.funs?, ha]
  · rename_i a ha
    split
    · exact mark_funs s _
    · split
      · exact mark_funs s _
      · simp [S.funs?, ha]
  · exact mark_funs s _

theorem putCalls_funs {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatCalls claim).put s g G).funs? = s.funs? :=
  (hearLook_funs _ g).trans (K1.putFork_funs s G)

theorem putDigits_funs {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatDigits claim).put s g G).funs? = s.funs? := by
  show (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test").funs? = s.funs?
  split
  · exact (K1.putFork_funs _ G).trans (First.K8.putTl_funs s _)
  · exact mark_funs s _

/-! ## K3 -/

/-- The decision of `blockVia`, at a seat whose laying leaves the list. -/
theorem via_sameFuns {Cl : Type} (seat : Seat S Cl)
    (hp : ∀ s g G, (seat.put s g G).funs? = s.funs?) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Decides SameFuns (K3.Law.blockVia seat piece laid before p guests) := by
  intro s rs gs s' h
  have h' : K3.Law.decideVia seat p s rs = .ok s' := h
  unfold K3.Law.decideVia at h'
  obtain ⟨F, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨x, _, h'⟩ := K9L.ok_bind h'
  obtain rfl := Except.ok.inj h'
  exact hp s x.1 x.2

/-- The steps without a round behind a lookup. -/
theorem quietAt_sameFuns {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : SameFuns s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → SameFuns s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, _, k⟩ := K9L.ok_bind k
    obtain ⟨G, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact K1.putFork_funs s _
  have hd : K3.quietHead X s = .ok t → SameFuns s t := by
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
      show S.funs? _ = S.funs? s
      simp [S.funs?, ha]
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → SameFuns s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact sameFuns_refl s
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

theorem theOwn_sameFuns {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Decides SameFuns b := by
  unfold K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have W : Decides SameFuns (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact via_sameFuns _ (putDigits_funs claim) a.piece laid sent p []
        | false => exact via_sameFuns _ (putCalls_funs claim) a.piece laid sent p []
      cases runs with
      | true => exact W
      | false => exact W

theorem theWhole_sameFuns {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Decides SameFuns b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_sameFuns claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact andThen_sameFuns _ _ _ W
      (steps_quiet _ _ _ _ f fun s t k => quietAt_sameFuns hq k)

/-- **K3's sub-protocol at an address, with its runs stated: the decision leaves the list.** -/
theorem k3_sameFuns {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Decides SameFuns b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_sameFuns claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact W

/-! ## K11 -/

/-- **The merge's decision leaves the list.** -/
theorem k11_sameFuns (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Decides SameFuns (headClaimMergeKind P) := by
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
    show S.funs? _ = S.funs? s
    simp [S.funs?, ha]
  · exact nomatch h'

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.sameFuns_refl
#print axioms VerifiableInference.Desc.LinkJoin.sameFuns_trans
#print axioms VerifiableInference.Desc.LinkJoin.andThen_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.k8_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.quietLayers_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.mark_funs
#print axioms VerifiableInference.Desc.LinkJoin.hearLook_funs
#print axioms VerifiableInference.Desc.LinkJoin.putCalls_funs
#print axioms VerifiableInference.Desc.LinkJoin.putDigits_funs
#print axioms VerifiableInference.Desc.LinkJoin.via_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.k3_sameFuns
#print axioms VerifiableInference.Desc.LinkJoin.k11_sameFuns
