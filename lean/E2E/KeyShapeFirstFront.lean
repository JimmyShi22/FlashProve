--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstFront.lean: THE KEY FILE's FIRST CHAIN ON ITS SHAPE (E2E/KeyShapeFirst.lean): THE
FIRST SHAPE OF EVERY RUN, WRITTEN OUT; and the chain's first two sub-protocols, "idx.1.send" and
"msg.1.send", cut in two: STRUCTURE | VALUES (the cut:
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean). BOTH DIRECTIONS. Definitions, statements and
proofs. Sub-protocols of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

  **`a₀`**, **`start_shape`**: the description starts the first chain at `chainStart codes {}`,
    whatever the instance: its shape, written out: no message, no group, no tree; every mark true.
    At all public values.
  `fit_front`: a sub-protocol with rounds, joined with one without behind it: at rounds that fit the
    joined one's, the first is handed all rounds.
  `gNumber`, `number_exact`: "the index-mask message's number".
  **`gIdx`**, **`idx_carries`**, **`idx_returns`**: "idx.1.send": E2E/KeyShapeSend.lean's `gSend`,
    then `gNumber`.
  `gOpenA`, **`gOpen`**, **`open_exact`**: "the ranges' group": five tests on the shape; a new
    group; the own message joins it: where the guards return, the step returns a state of the shape
    that they return. No test on values.
  **`gMsg`**, **`msg_carries`**, **`msg_returns`**: "msg.1.send": `gSend`, then `gOpen`.

Limits.
- (B2r) is said at rounds that fit the declared ones: they pass the sending's two tests
  (E2E/KeyShapeSend.lean's `vSend_fit`): so no named test on values is left.


-/
import E2E.KeyShapeSend
import Johnson.Desc.K13.Law.Then

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest (CarriesR ReturnsR carries_join returns_join valsThen)
open VerifiableInference.Desc (Block roundsFit noDigest named need)
open VerifiableInference.Desc.Ground (newGroupP joinP)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (FirstState chainStart sendingSeat sendingPar quietAt
  openRangesGroup sendIndexMasks sendOwnMessage Pieces)
open AtPublicFiles.KeyShape (Sh₁ sh₁ Pub1 BackOf both_of_exact)

variable {Bk Cl : Type} (Q : Pub1) (bk : BackOf → Bk)

/-! ## The first shape -/

/-- **The first shape of every run of the first chain**, written out. b₀: the back part's shape
where nothing is laid. -/
def a₀ (codes : Codes) (b₀ : Bk) : Sh₁ Bk :=
  (⟨⟨codes, [], []⟩, ⟨[], []⟩, 0⟩,
    { owed := none, sent := [], idx := noId, grp := noId, rider := none, atEnd := false
      tidy := true
      look := { led := none, heard := none, home := [], rows := [], plain := true, keys := []
                keysOk := true }
      back := b₀ })

/-- **The reader gives it at the state at which the description starts the chain.** -/
theorem start_shape (codes : Codes) :
    sh₁ Q bk (chainStart codes {}) = a₀ codes (bk ([], #[], #[], none)) := by
  have hT : stTidyB (chainStart (β := VerifiableInference.Desc.Key.LookupRecord) codes {}).d.st =
      true := start_tidy codes
  have hk : keysB (Wf.matrixOf Q.one.lin) Q.one.ranges.lookups [] = true := by
    unfold keysB
    rw [zipT_eq, List.zip_nil_right]
    rfl
  refine Prod.ext rfl ?_
  show AtPublicFiles.KeyShape.locSh Q bk (chainStart codes {}) = _
  unfold AtPublicFiles.KeyShape.locSh AtPublicFiles.KeyShape.lookSh
  rw [hT]
  show (⟨none, [], noId, noId, none, false, true,
    ⟨none, none, [], [], true, [], keysB (Wf.matrixOf Q.one.lin) Q.one.ranges.lookups []⟩, _⟩ :
      AtPublicFiles.KeyShape.LocSh Bk) = _
  rw [hk]
  rfl

/-! ## A sub-protocol with rounds, and one without behind it -/

theorem fit_front {S : Type} (nm : String) (A B : Block S Cl) (hB : B.rounds = [])
    (rs : List Fmt.RoundView) (hfit : roundsFit (A.andThen nm B).rounds rs = true) :
    roundsFit A.rounds rs = true ∧ ∀ s gs, (A.andThen nm B).decide s (rs.map noDigest) gs =
      (A.decide s (rs.map noDigest) (gs.take A.openings)).bind fun s' =>
        B.decide s' [] (gs.drop A.openings) := by
  have hr : (A.andThen nm B).rounds = A.rounds := by
    show A.rounds ++ B.rounds = _
    rw [hB, List.append_nil]
  rw [hr] at hfit
  have hlen : (rs.map noDigest).length = A.rounds.length := by
    rw [List.length_map]
    exact VerifiableInference.Desc.K13.Law.roundsFit_length _ _ hfit
  refine ⟨hfit, fun s gs => ?_⟩
  show (A.decide s ((rs.map noDigest).take A.rounds.length) (gs.take A.openings)).bind
    (fun s' => B.decide s' ((rs.map noDigest).drop A.rounds.length) (gs.drop A.openings)) = _
  rw [List.take_of_length_le (Nat.le_of_eq hlen), List.drop_of_length_le (Nat.le_of_eq hlen)]

/-! ## "idx.1.send" -/

/-- "The index-mask message's number", on the shape. -/
def gNumber (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  match a.2.sent[0]? with
  | some i => .ok (a.1, { a.2 with idx := i })
  | none => .error "the sending has left no number"

theorem number_exact (s : FirstState) (t : Sh₁ Bk) (h : gNumber (sh₁ Q bk s) = .ok t) :
    ∃ s', (do
      let i ← named "the sending has left no number" s.sent[0]?
      pure { s with idx := i } : Except String FirstState) = .ok s' ∧ sh₁ Q bk s' = t := by
  unfold gNumber at h
  have e : (sh₁ Q bk s).2.sent[0]? = s.sent[0]? := by
    show s.sent.toList[0]? = _
    rw [Array.getElem?_toList]
  rw [e] at h
  cases hs : s.sent[0]? with
  | none =>
    rw [hs] at h
    cases h
  | some i =>
    rw [hs] at h
    exact ⟨{ s with idx := i }, rfl, Except.ok.inj h⟩

/-- The sending's numbers. -/
abbrev parIdx (N : Pieces) (groups : List (List Nat)) : VerifiableInference.Desc.K1.Par :=
  sendingPar Q.one N.idx "the index masks" #[Q.one.indexMasks] groups

/-- **"idx.1.send" on the shape.** -/
def gIdx (N : Pieces) (groups : List (List Nat)) (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  (gSend (parIdx Q N groups) a).bind gNumber

/-- **(B1r), at rounds that fit.** -/
theorem idx_carries (N : Pieces) (groups : List (List Nat)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (sendIndexMasks (β := VerifiableInference.Desc.Key.LookupRecord) (Cl := Cl)
      Q.one N groups).rounds rs = true) :
    CarriesR (sh₁ Q bk) (fun s => (sendIndexMasks (Cl := Cl) Q.one N groups).decide s
      (rs.map noDigest) gs) (gIdx Q N groups) := by
  obtain ⟨hf, hd⟩ := fit_front (Cl := Cl) "idx.1.send"
    (sendingSeat "K1: the index masks' sending" (parIdx Q N groups))
    (quietAt "the index-mask message's number" (parIdx Q N groups).place fun s => do
      let i ← named "the sending has left no number" s.sent[0]?
      pure { s with idx := i }) rfl rs hfit
  have e : (fun s => (sendIndexMasks (Cl := Cl) Q.one N groups).decide s (rs.map noDigest) gs) =
      fun s => ((sendingSeat (Cl := Cl) "K1: the index masks' sending"
        (parIdx Q N groups)).decide s (rs.map noDigest) (gs.take _)).bind fun s' => (do
          let i ← named "the sending has left no number" s'.sent[0]?
          pure { s' with idx := i } : Except String FirstState) := funext fun s => hd s gs
  rw [e]
  exact carries_join (send_carries Q bk _ _ rs _ hf)
    (both_of_exact (number_exact Q bk)).1

/-- **(B2r), at rounds that fit**: no test on values. -/
theorem idx_returns (N : Pieces) (groups : List (List Nat)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (sendIndexMasks (β := VerifiableInference.Desc.Key.LookupRecord) (Cl := Cl)
      Q.one N groups).rounds rs = true) :
    ReturnsR (sh₁ Q bk) (fun s => (sendIndexMasks (Cl := Cl) Q.one N groups).decide s
      (rs.map noDigest) gs) (gIdx Q N groups) (fun _ => true) := by
  obtain ⟨hf, hd⟩ := fit_front (Cl := Cl) "idx.1.send"
    (sendingSeat "K1: the index masks' sending" (parIdx Q N groups))
    (quietAt "the index-mask message's number" (parIdx Q N groups).place fun s => do
      let i ← named "the sending has left no number" s.sent[0]?
      pure { s with idx := i }) rfl rs hfit
  intro s t hg _
  obtain ⟨t₁, g1, g2⟩ := ProofFile.Honest.bindR_ok hg
  obtain ⟨s₁, h1⟩ := send_returns₁ (Cl := Cl) Q bk "K1: the index masks' sending"
    (parIdx Q N groups) (rs.map noDigest) (gs.take (sendingSeat (β :=
      VerifiableInference.Desc.Key.LookupRecord) (Cl := Cl) "K1: the index masks' sending"
      (parIdx Q N groups)).openings) s t₁ g1 (vSend_fit (parIdx Q N groups) rs hf)
  obtain rfl := send_carries (Cl := Cl) Q bk _ _ rs _ hf s s₁ t₁ h1 g1
  obtain ⟨s₂, h2, -⟩ := number_exact Q bk s₁ t g2
  have h1' : (sendingSeat (Cl := Cl) "K1: the index masks' sending" (parIdx Q N groups)).decide s
      (rs.map noDigest) (gs.take (sendingSeat (β := VerifiableInference.Desc.Key.LookupRecord)
        (Cl := Cl) "K1: the index masks' sending" (parIdx Q N groups)).openings) = .ok s₁ := h1
  exact ⟨s₂, (hd s gs).trans (by rw [h1']; exact h2)⟩

/-! ## "msg.1.send" -/

/-- **"The ranges' group" on the shape.** adm: one clause on public values, as an argument: so that
it can be paid by a theorem where it cannot be evaluated. -/
def gOpenA (adm : Bool) (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  if a.2.tidy && adm &&
      ((a.1.st.oracles[a.2.idx]?).any fun o => o.sampled && o.shape.mainRows == 0) &&
      Q.one.ranges.message.shape.answers == Q.one.given.plan.samples &&
      a.2.sent[0]? == some Q.one.ranges.messageId then
    match newGroupS a.1 Q.one.ranges.message.shape.code Q.one.ranges.message.shape.maskCode with
    | none => .error "the ranges' group cannot be made"
    | some g =>
      match joinS g.2 g.1 Q.one.ranges.messageId false with
      | none => .error "the own message cannot join its group"
      | some c => .ok (c, { a.2 with
          grp := g.1, rider := if Q.one.ranges.choice.masksRide then a.2.sent[1]? else none })
  else .error "the ranges' group: a test on the shape"

/-- The same, with its clause on public values laid in: "the parameters are admitted". -/
def gOpen (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  gOpenA Q (Wf.admitted a.1.st.codes Q.one.ranges (Wf.matrixOf Q.one.lin)) a

/-- **Where the guards return, the step returns a state of the shape that they return.** -/
theorem open_exact (s : FirstState) (t : Sh₁ Bk) (h : gOpen Q (sh₁ Q bk s) = .ok t) :
    ∃ s', openRangesGroup Q.one s = .ok s' ∧ sh₁ Q bk s' = t := by
  unfold gOpen gOpenA at h
  split at h
  case isFalse => cases h
  rename_i h0
  simp only [Bool.and_eq_true, beq_iff_eq] at h0
  obtain ⟨⟨⟨⟨hT, hA⟩, hI⟩, hS⟩, hM⟩ := h0
  have hT' : stTidyB s.d.st = true := hT
  have hA' : Wf.admitted s.d.st.codes Q.one.ranges (Wf.matrixOf Q.one.lin) = true := hA
  have e0 : s.sent[0]? = some Q.one.ranges.messageId := by
    have : s.sent.toList[0]? = some Q.one.ranges.messageId := hM
    rwa [Array.getElem?_toList] at this
  obtain ⟨o, ho, hform⟩ : ∃ o, s.d.st.oracles[s.idx]? = some o ∧
      (o.sampled && o.shape.mainRows == 0) = true := by
    have hI' : (((stSh s.d.st).oracles[s.idx]?).any fun o => o.sampled && o.shape.mainRows == 0) =
      true := hI
    rw [orc_get] at hI'
    cases hq : s.d.st.oracles[s.idx]? with
    | none => rw [hq] at hI'; cases hI'
    | some o => rw [hq] at hI'; exact ⟨o, rfl, hI'⟩
  cases hg : newGroupS (sh₁ Q bk s).1 Q.one.ranges.message.shape.code
      Q.one.ranges.message.shape.maskCode with
  | none => rw [hg] at h; cases h
  | some g =>
    rw [hg] at h
    obtain ⟨x, hx⟩ := newGroup_returns s.d _ _ g hg
    obtain rfl : (x.1, shD x.2) = g :=
      Option.some.inj ((newGroup_carries s.d x.2 _ _ x.1 hx).symm.trans hg)
    dsimp only at h
    cases hj : joinS (shD x.2) x.1 Q.one.ranges.messageId false with
    | none => rw [hj] at h; cases h
    | some c =>
      rw [hj] at h
      dsimp only at h
      obtain ⟨d, hd⟩ := join_returns x.2 _ _ _ c hj
      obtain rfl : shD d = c :=
        Option.some.inj ((join_carries x.2 d _ _ _ hd).symm.trans hj)
      have hTd : stTidyB d.st = true :=
        join_tidy x.2 d _ _ _ hd (newGroup_tidy s.d x.2 _ _ x.1 hx hT')
      refine ⟨{ s with
        d := d, grp := x.1,
        rider := if Q.one.ranges.choice.masksRide then s.sent[1]? else none }, ?_, ?_⟩
      · unfold openRangesGroup
        simp only [hA', ho, hform, hS, e0, hx, hd, named, need, bind, Except.bind, pure,
          Except.pure, if_true, beq_self_eq_true]
      · rw [← Except.ok.inj h]
        refine Prod.ext rfl ?_
        show AtPublicFiles.KeyShape.locSh Q bk { s with
                    d := d, grp := x.1,
                    rider := if Q.one.ranges.choice.masksRide then s.sent[1]? else none } = _
        unfold AtPublicFiles.KeyShape.locSh
        have hTd' : stTidyB d.st = true := hTd
        rw [hTd']
        show _ = ({ AtPublicFiles.KeyShape.locSh Q bk s with
          grp := x.1,
          rider := if Q.one.ranges.choice.masksRide then s.sent.toList[1]? else none } :
            AtPublicFiles.KeyShape.LocSh Bk)
        unfold AtPublicFiles.KeyShape.locSh
        rw [hT', Array.getElem?_toList]
        rfl

/-- The sending's numbers. -/
abbrev parMsg (N : Pieces) (groups : List (List Nat)) : VerifiableInference.Desc.K1.Par :=
  sendingPar Q.one N.msg "the lookups' own message and what rides with it"
    (Wf.messageOf Q.one.ranges) groups

/-- **"msg.1.send" on the shape.** -/
def gMsg (N : Pieces) (groups : List (List Nat)) (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  (gSend (parMsg Q N groups) a).bind (gOpen Q)

/-- **(B1r), at rounds that fit.** -/
theorem msg_carries (N : Pieces) (groups : List (List Nat)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (sendOwnMessage (β := VerifiableInference.Desc.Key.LookupRecord) (Cl := Cl)
      Q.one N groups).rounds rs = true) :
    CarriesR (sh₁ Q bk) (fun s => (sendOwnMessage (Cl := Cl) Q.one N groups).decide s
      (rs.map noDigest) gs) (gMsg Q N groups) := by
  obtain ⟨hf, hd⟩ := fit_front (Cl := Cl) "msg.1.send"
    (sendingSeat "K1: the own message's sending" (parMsg Q N groups))
    (quietAt "the ranges' group" (parMsg Q N groups).place (openRangesGroup Q.one)) rfl rs hfit
  have e : (fun s => (sendOwnMessage (Cl := Cl) Q.one N groups).decide s (rs.map noDigest) gs) =
      fun s => ((sendingSeat (Cl := Cl) "K1: the own message's sending"
        (parMsg Q N groups)).decide s (rs.map noDigest) (gs.take _)).bind
          (openRangesGroup Q.one) := funext fun s => hd s gs
  rw [e]
  exact carries_join (send_carries Q bk _ _ rs _ hf) (both_of_exact (open_exact Q bk)).1

/-- **(B2r), at rounds that fit**: no test on values. -/
theorem msg_returns (N : Pieces) (groups : List (List Nat)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (sendOwnMessage (β := VerifiableInference.Desc.Key.LookupRecord) (Cl := Cl)
      Q.one N groups).rounds rs = true) :
    ReturnsR (sh₁ Q bk) (fun s => (sendOwnMessage (Cl := Cl) Q.one N groups).decide s
      (rs.map noDigest) gs) (gMsg Q N groups) (fun _ => true) := by
  obtain ⟨hf, hd⟩ := fit_front (Cl := Cl) "msg.1.send"
    (sendingSeat "K1: the own message's sending" (parMsg Q N groups))
    (quietAt "the ranges' group" (parMsg Q N groups).place (openRangesGroup Q.one)) rfl rs hfit
  intro s t hg _
  obtain ⟨t₁, g1, g2⟩ := ProofFile.Honest.bindR_ok hg
  obtain ⟨s₁, h1⟩ := send_returns₁ (Cl := Cl) Q bk "K1: the own message's sending"
    (parMsg Q N groups) (rs.map noDigest) (gs.take (sendingSeat (β :=
      VerifiableInference.Desc.Key.LookupRecord) (Cl := Cl) "K1: the own message's sending"
      (parMsg Q N groups)).openings) s t₁ g1 (vSend_fit (parMsg Q N groups) rs hf)
  obtain rfl := send_carries (Cl := Cl) Q bk _ _ rs _ hf s s₁ t₁ h1 g1
  obtain ⟨s₂, h2, -⟩ := open_exact Q bk s₁ t g2
  have h1' : (sendingSeat (Cl := Cl) "K1: the own message's sending" (parMsg Q N groups)).decide s
      (rs.map noDigest) (gs.take (sendingSeat (β := VerifiableInference.Desc.Key.LookupRecord)
        (Cl := Cl) "K1: the own message's sending" (parMsg Q N groups)).openings) = .ok s₁ := h1
  exact ⟨s₂, (hd s gs).trans (by rw [h1']; exact h2)⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.start_shape
#print axioms AtPublicFiles.AtFiles.fit_front
#print axioms AtPublicFiles.AtFiles.number_exact
#print axioms AtPublicFiles.AtFiles.idx_carries
#print axioms AtPublicFiles.AtFiles.idx_returns
#print axioms AtPublicFiles.AtFiles.open_exact
#print axioms AtPublicFiles.AtFiles.msg_carries
#print axioms AtPublicFiles.AtFiles.msg_returns
