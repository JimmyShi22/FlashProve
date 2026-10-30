-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TabsStay.lean: THE HEAD's TABLES, AS THE STATE HOLDS THEM (the field t
of the head's part: the list of tables AND the table of tables), ARE, IN FRONT OF THE HEAD's
BATCHING, WHAT THE TEXT THAT MAKES THEM RETURNED. In the goals' scope. One definition, statements
and proofs.

  `S.tabs?`: the reading: the field t at the head's segment; none elsewhere.
  `SameTabs s s'`: s'.tabs? = s.tabs?. The keepers `k8_sameTabs`, `k1Later_sameTabs`, `k3_sameTabs`,
    `k11_sameTabs`: MADE BY PROGRAM out of OwnStay.lean (the same walk through the same texts, at
      the reading tabs? for own?). `sameTabs_stretch`: `StretchKeeps SameTabs` (StretchBack.lean).
  `quietHead_tabs`: behind a yes of the head's quiet step (`ReadsQuiet.head P`): the state holds the
    very tt that `tables P.h P.L P.hp cov x` returned.
  `tabs_at_reads`: **so at every state reached at 343.** `tabs_at_batch`: **and at 347: ∃ cov x tt,
    s.tabs? = some tt ∧ tables Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H cov x = .ok tt.**
Limits. ON THE DECISIONS ALONE. Nothing on the weights. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.HeadSkel
import Johnson.Desc.First.Link.Law.StretchParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

/-- The head's tables, as the state holds them. -/
def VerifiableInference.Desc.First.S.tabs? (s : VerifiableInference.Desc.First.S) :
    Option OnBytes.Model.Head.Tables :=
  match s.here with
  | .head a => a.t
  | _ => none

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc (Block Chain FileDescription need)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open Johnson.Desc.First.ForkMerge (headMergeDecide headClaimMergeKind)
open Johnson.Desc.First.Walk.Tied (Reach stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

theorem putLink_tabs (s : S) (L : LinkCtx) : (s.putLink L).tabs? = s.tabs? := by
  unfold S.putLink
  split <;> (try split) <;> simp_all [S.tabs?]

theorem putFork_tabs (s : S) (G : Fork) : (s.putFork G).tabs? = s.tabs? := by
  unfold S.putFork
  split <;> (try split) <;> simp_all [S.tabs?]

theorem putTl_tabs (s : S) (tl : HTailF2) : (s.putTl tl).tabs? = s.tabs? := by
  unfold S.putTl S.tabs?
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho]
  | _ => simp [h]

/-- The head's tables are left as they were. -/
def SameTabs (s s' : S) : Prop := s'.tabs? = s.tabs?

theorem sameTabs_refl (s : S) : SameTabs s s := rfl

theorem sameTabs_trans (a b c : S) (h : SameTabs a b) (k : SameTabs b c) : SameTabs a c :=
  Eq.trans k h

/-- Two sub-protocols joined as one. -/
theorem andThen_sameTabs {Cl : Type} (nm : String) (p q : Block S Cl) (hp : Decides SameTabs p)
    (hq : Decides SameTabs q) : Decides SameTabs (Block.andThen nm p q) := by
  intro s rs gs s' h
  obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok h
  exact sameTabs_trans _ _ _ (hp _ _ _ _ h1) (hq _ _ _ _ h2)

/-! ## K8 and K1 -/

theorem k8_sameTabs (p : First.K8.ParW) : Decides SameTabs (First.K8.whole p) :=
  fun s rs gs s' h => First.K8.hear_leaves (Cl := Claim) S.tabs? putTl_tabs p.toPar s rs gs s' h

theorem k1Later_sameTabs (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : ℕ) (arrays : Option (List ℕ)) :
    Decides SameTabs (K1.laterAt (Cl := Unit) q gp link piece moment arrays) := by
  intro s rs gs s' h
  have h' := h
  unfold K1.laterAt K1.commitAtS at h'
  dsimp only at h'
  split at h'
  · obtain ⟨y, _, rfl⟩ := VerifiableInference.Desc.mapOk h'
    exact ((putFork_tabs _ _).trans (putLink_tabs _ _)).trans rfl
  · cases h'

/-! ## The writings -/

theorem mark_tabs (s : S) (w : String) : (s.mark w).tabs? = s.tabs? := by
  unfold S.mark
  split <;> rfl

theorem hearLook_tabs (s : S) (g : Forest.Heard) : (s.hearLook g).tabs? = s.tabs? := by
  unfold S.hearLook
  split
  · rename_i a ha
    split
    · exact mark_tabs s _
    · simp [S.tabs?, ha]
  · rename_i a ha
    split
    · exact mark_tabs s _
    · simp [S.tabs?, ha]
  · rename_i a ha
    split
    · exact mark_tabs s _
    · split
      · exact mark_tabs s _
      · simp [S.tabs?, ha]
  · exact mark_tabs s _

theorem putCalls_tabs {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatCalls claim).put s g G).tabs? = s.tabs? :=
  (hearLook_tabs _ g).trans (putFork_tabs s G)

theorem putDigits_tabs {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatDigits claim).put s g G).tabs? = s.tabs? := by
  show (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test").tabs? = s.tabs?
  split
  · exact (putFork_tabs _ G).trans (putTl_tabs s _)
  · exact mark_tabs s _

/-! ## K3 -/

/-- The decision of `blockVia`, at a seat whose laying leaves it. -/
theorem via_sameTabs {Cl : Type} (seat : Seat S Cl)
    (hp : ∀ s g G, (seat.put s g G).tabs? = s.tabs?) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Decides SameTabs (K3.Law.blockVia seat piece laid before p guests) := by
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
theorem quietAt_sameTabs {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) {s t : S} (h : f s = .ok t) : SameTabs s t := by
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → SameTabs s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, _, k⟩ := K9L.ok_bind k
    obtain ⟨G, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact putFork_tabs s _
  have hd : K3.quietHead X s = .ok t → SameTabs s t := by
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
      show S.tabs? _ = S.tabs? s
      simp [S.tabs?, ha]
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → SameTabs s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact sameTabs_refl s
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

theorem theOwn_sameTabs {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Decides SameTabs b := by
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
      have W : Decides SameTabs (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact via_sameTabs _ (putDigits_tabs claim) a.piece laid sent p []
        | false => exact via_sameTabs _ (putCalls_tabs claim) a.piece laid sent p []
      cases runs with
      | true => exact W
      | false => exact W

theorem theWhole_sameTabs {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Decides SameTabs b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_sameTabs claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact andThen_sameTabs _ _ _ W
      (steps_quiet _ _ _ _ f fun s t k => quietAt_sameTabs hq k)

/-- **K3's sub-protocol at an address, with its runs stated: the decision leaves it.** -/
theorem k3_sameTabs {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Decides SameTabs b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_sameTabs claim true X codes shape a h0
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
theorem k11_sameTabs (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Decides SameTabs (headClaimMergeKind P) := by
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
    show S.tabs? _ = S.tabs? s
    simp [S.tabs?, ha]
  · exact nomatch h'



theorem sameTabs_stretch : StretchKeeps SameTabs where
  trans := sameTabs_trans
  k8 := k8_sameTabs
  k1 := k1Later_sameTabs
  k3 := fun claim readers X codes shape a _ h => k3_sameTabs claim readers X codes shape a h
  k11 := k11_sameTabs

/-- Behind a yes of the head's quiet step. -/
theorem quietHead_tabs (P : K8.ReadsQuiet.PH) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (K8.ReadsQuiet.head P).decide s rs gs = .ok s') :
    ∃ cov x tt, s'.tabs? = some tt ∧ K8.ReadsQuiet.tables P.h P.L P.hp cov x = .ok tt := by
  have h' : (match s.here with
      | .head a => do
        need "reads: the head's link is not opened" a.opened
        let cov ← K8.ReadsQuiet.under "reads: the covered positions cannot be said"
          (s.covered P.h.T P.h.V)
        let x ← (a.x.elim (.error "reads: what the head heard is not laid") .ok : Except String _)
        let t ← K8.ReadsQuiet.tables P.h P.L P.hp cov x
        let tl ← K8.ReadsQuiet.closed P.hp.tl t.funs a.L s.st
        pure { s with here := .head { a with t := some t, tl := tl } }
      | _ => .error "reads: the head's link is not open" : Except String S) = .ok s' := h
  split at h'
  · rename_i a ha
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨cov, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨x, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨t, ht, h'⟩ := K9L.ok_bind h'
    obtain ⟨tl, _, h'⟩ := K9L.ok_bind h'
    obtain rfl := Except.ok.inj h'
    exact ⟨cov, x, t, rfl, ht⟩
  · exact nomatch h'

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **BEHIND THE SENDING OF THE READS AT THE HEAD's SEGMENT.** -/
theorem tabs_at_reads (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 343 (z, s')) :
    ∃ cov x tt, s'.tabs? = some tt ∧
      K8.ReadsQuiet.tables Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H cov x = .ok tt := by
  obtain ⟨z', s, s'', b₀, e, _, hb, hy⟩ := reach_pred (k := 342) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, _, e4⟩ := IM.k1_reads_of hS hR O 24 (by omega)
  have hf : c.blocksInOrder[342]? = some b := by
    have := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) _] at this
    exact this
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' : (IM.k1Reads Z Bs.G₀ 24 Xl (IM.k1Ix 24 false + 1) reads).decide s rs gs = .ok s' :=
    ((IM.yes_alone e4 (fun k => nomatch k) s _ rs gs).1 hd).1
  unfold IM.k1Reads at hd'
  obtain ⟨m, _, h2⟩ := Keeps.ebind_ok hd'
  unfold IM.k1Quiet at h2
  obtain ⟨l24, f24, k24, -⟩ := (IM.ground_named hS hR O.pub O.blank).2
  rcases First.K8.Ready.quiet_arms Bs.G₀ 24 Xl _ _ _ _ h2 with ⟨k1, _⟩ | ⟨_, Y, hY, hc⟩
  · rw [← Option.some.inj (f24.symm.trans hX), k24] at k1
    exact absurd k1 (by decide)
  · rcases hc with ⟨k0, _⟩ | ⟨_, hq⟩
    · rw [← Option.some.inj (f24.symm.trans hY), k24] at k0
      exact absurd k0 (by decide)
    · obtain ⟨cov, x, tt, a1, a2⟩ := quietHead_tabs
        ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩ hq
      exact ⟨cov, x, tt, a1, a2⟩

/-- **IN FRONT OF THE HEAD's BATCHING.** -/
theorem tabs_at_batch (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ cov x tt, s'.tabs? = some tt ∧
      K8.ReadsQuiet.tables Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H cov x = .ok tt := by
  obtain ⟨s, r, q⟩ := stretch_back_head sameTabs_stretch hS hR O h
  obtain ⟨cov, x, tt, a1, a2⟩ := tabs_at_reads hS hR O r
  exact ⟨cov, x, tt, q.trans a1, a2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.putLink_tabs
#print axioms VerifiableInference.Desc.LinkJoin.putFork_tabs
#print axioms VerifiableInference.Desc.LinkJoin.putTl_tabs
#print axioms VerifiableInference.Desc.LinkJoin.sameTabs_refl
#print axioms VerifiableInference.Desc.LinkJoin.sameTabs_trans
#print axioms VerifiableInference.Desc.LinkJoin.andThen_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.k8_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.k1Later_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.mark_tabs
#print axioms VerifiableInference.Desc.LinkJoin.hearLook_tabs
#print axioms VerifiableInference.Desc.LinkJoin.putCalls_tabs
#print axioms VerifiableInference.Desc.LinkJoin.putDigits_tabs
#print axioms VerifiableInference.Desc.LinkJoin.via_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.k3_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.k11_sameTabs
#print axioms VerifiableInference.Desc.LinkJoin.sameTabs_stretch
#print axioms VerifiableInference.Desc.LinkJoin.quietHead_tabs
#print axioms VerifiableInference.Desc.LinkJoin.tabs_at_reads
#print axioms VerifiableInference.Desc.LinkJoin.tabs_at_batch
