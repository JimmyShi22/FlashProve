-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OwnStay.lean: WHAT A LAYERS' SEGMENT's OWN ROUNDS RETURNED (`S.own?`,
Johnson/Desc/First/State.lean) IS LEFT AS IT WAS BY THE SUB-PROTOCOLS BETWEEN K4 AND THE BATCHING,
THE LOOKUP ON THE DIGITS AMONG THEM; AND SO IT IS, IN FRONT OF THE BATCHING, WHAT IT WAS BEHIND K4's
SUB-PROTOCOL. MADE BY PROGRAM out of FunsStay.lean (the same walk through the same texts, at the
reading own? for funs?), then the two ends by hand. Statements and proofs.

  `SameOwn s s'`: s'.own? = s.own?. The keepers, as in FunsStay.lean: `k8_sameOwn`,
    `k1Later_sameOwn`, `quietLayers_sameOwn` (by StretchParts.lean's), `k3_sameOwn`, `k11_sameOwn`.
  `sameOwn_stretch`: `StretchKeeps SameOwn` (StretchBack.lean).
  `own_from_k4`: **g < 12: reached at 28 g + 9 (in front of the batching) ⊢ there is a state reached
    at 28 g + 5 (behind K4's sub-protocol), with the same public part and the same own?.**
Limits. ON THE DECISIONS ALONE. Nothing on what own? finds. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.StretchParts
import Johnson.Desc.First.Link.Law.FunsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open Johnson.Desc.First.ForkMerge (headMergeDecide headClaimMergeKind)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What a layers' segment's own rounds returned is left as it was. -/
def SameOwn (s s' : S) : Prop := s'.own? = s.own?

theorem sameOwn_refl (s : S) : SameOwn s s := rfl

theorem sameOwn_trans (a b c : S) (h : SameOwn a b) (k : SameOwn b c) : SameOwn a c :=
  Eq.trans k h

/-- Two sub-protocols joined as one. -/
theorem andThen_sameOwn {Cl : Type} (nm : String) (p q : Block S Cl) (hp : Decides SameOwn p)
    (hq : Decides SameOwn q) : Decides SameOwn (Block.andThen nm p q) := by
  intro s rs gs s' h
  obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok h
  exact sameOwn_trans _ _ _ (hp _ _ _ _ h1) (hq _ _ _ _ h2)

/-! ## By other files' laws -/

theorem k8_sameOwn (p : First.K8.ParW) : Decides SameOwn (First.K8.whole p) :=
  fun s rs gs s' h => First.K8.hear_leaves_own (Cl := Claim) p.toPar s rs gs s' h

theorem k1Later_sameOwn (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : ℕ) (arrays : Option (List ℕ)) :
    Decides SameOwn (K1.laterAt (Cl := Unit) q gp link piece moment arrays) :=
  fun s rs gs s' h => (k1_ownLater q gp link piece moment arrays s rs gs s' h).1

theorem quietLayers_sameOwn (P : K8.ReadsQuiet.PG) : Decides SameOwn (K8.ReadsQuiet.layers P) :=
  fun s rs gs s' h => (quietLayers_ownLater P s rs gs s' h).1

/-! ## The writings -/

theorem mark_own (s : S) (w : String) : (s.mark w).own? = s.own? := by
  unfold S.mark
  split <;> rfl

theorem hearLook_own (s : S) (g : Forest.Heard) : (s.hearLook g).own? = s.own? := by
  unfold S.hearLook
  split
  · rename_i a ha
    split
    · exact mark_own s _
    · simp [S.own?, ha]
  · rename_i a ha
    split
    · exact mark_own s _
    · simp [S.own?, ha]
  · rename_i a ha
    split
    · exact mark_own s _
    · split
      · exact mark_own s _
      · simp [S.own?, ha]
  · exact mark_own s _

theorem putCalls_own {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatCalls claim).put s g G).own? = s.own? :=
  (hearLook_own _ g).trans (putFork_own s G)

theorem putDigits_own {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatDigits claim).put s g G).own? = s.own? := by
  show (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test").own? = s.own?
  split
  · exact (putFork_own _ G).trans (First.K8.putTl_own s _)
  · exact mark_own s _

/-! ## K3 -/

/-- The decision of `blockVia`, at a seat whose laying leaves it. -/
theorem via_sameOwn {Cl : Type} (seat : Seat S Cl)
    (hp : ∀ s g G, (seat.put s g G).own? = s.own?) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Decides SameOwn (K3.Law.blockVia seat piece laid before p guests) := by
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
theorem quietAt_sameOwn {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : SameOwn s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → SameOwn s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, _, k⟩ := K9L.ok_bind k
    obtain ⟨G, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact putFork_own s _
  have hd : K3.quietHead X s = .ok t → SameOwn s t := by
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
      show S.own? _ = S.own? s
      simp [S.own?, ha]
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → SameOwn s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact sameOwn_refl s
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

theorem theOwn_sameOwn {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Decides SameOwn b := by
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
      have W : Decides SameOwn (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact via_sameOwn _ (putDigits_own claim) a.piece laid sent p []
        | false => exact via_sameOwn _ (putCalls_own claim) a.piece laid sent p []
      cases runs with
      | true => exact W
      | false => exact W

theorem theWhole_sameOwn {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Decides SameOwn b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_sameOwn claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact andThen_sameOwn _ _ _ W
      (steps_quiet _ _ _ _ f fun s t k => quietAt_sameOwn hq k)

/-- **K3's sub-protocol at an address, with its runs stated: the decision leaves it.** -/
theorem k3_sameOwn {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Decides SameOwn b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_sameOwn claim true X codes shape a h0
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

/-- **The merge's decision leaves it.** -/
theorem k11_sameOwn (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Decides SameOwn (headClaimMergeKind P) := by
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
    show S.own? _ = S.own? s
    simp [S.own?, ha]
  · exact nomatch h'


theorem sameOwn_stretch : StretchKeeps SameOwn where
  trans := sameOwn_trans
  k8 := k8_sameOwn
  k1 := k1Later_sameOwn
  k3 := fun claim readers X codes shape a _ h => k3_sameOwn claim readers X codes shape a h
  k11 := k11_sameOwn

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **FROM THE BATCHING's BORDER BACK TO THE BORDER BEHIND K4's SUB-PROTOCOL.** -/
theorem own_from_k4 (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ s'.own? = s.own? :=
  stretch_back_layers sameOwn_stretch quietLayers_sameOwn hS hR O hg h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.sameOwn_refl
#print axioms VerifiableInference.Desc.LinkJoin.sameOwn_trans
#print axioms VerifiableInference.Desc.LinkJoin.andThen_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.k8_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.quietLayers_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.mark_own
#print axioms VerifiableInference.Desc.LinkJoin.hearLook_own
#print axioms VerifiableInference.Desc.LinkJoin.putCalls_own
#print axioms VerifiableInference.Desc.LinkJoin.putDigits_own
#print axioms VerifiableInference.Desc.LinkJoin.via_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.k3_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.k11_sameOwn
#print axioms VerifiableInference.Desc.LinkJoin.sameOwn_stretch
#print axioms VerifiableInference.Desc.LinkJoin.own_from_k4
