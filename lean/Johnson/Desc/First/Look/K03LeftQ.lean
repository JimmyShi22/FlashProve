-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K03LeftQ.lean: THE KIND "LOOKUP" (K3): THE LOOKUP ON THE CALLS, AS IT IS
REACHED along the fold of the first chain of the IOP as written in Lean (our files: the description)
that `ProofFile.onlineDescription` returns, in the goals' scope, AT THE 24 LINKS IN FRONT OF THE HEAD's: (1) the
ledger in front of it is `LeftQ` at the place's own number of slots: it has its sizes, that many
slots, and every slot is free; (2) the fold's return behind it is an accept of the kind's own
decision `K3.block (seatCalls K3Lot.ofForm) …`; (3) so the test `FillBare.leftAtB` (FillBare.lean)
accepts what was heard and the ledger behind. NO PREMISE ON THE ROUNDS' WORDS: a reached state may
stand behind rounds that are not canonical. Theorems with their proofs.

  `startFork_leftQ`: the ledger from which a sub-proof starts is `LeftQ ns`. (The like in other
    letters: `startFork_room`, Walk/FrameRoom.lean; `room_startFork`, Att/K05RoomOpened.lean:
    two files that are not in this library.)
  `zipped_g`: `zipped_kind` (Johnson/IMR/Subs.lean) with the group's number beside the kind.
  `zeroAt_ns`, `frameAt_att_ns`, `frameAt_lay_ns`: which entry of the public data the frame's
    letters take their number of slots from.
  **`stated_calls_block`**: general in the maker of claims, the public data and the address: an
    accept of `K3.theStated`'s value at the lookup on the calls is an accept of `K3.block`'s
    decision from the same state to the same state: `blockVia_decide`; the lookups'
    `quiet_calls_same`.
  `built_at_scope`: in scope, l < 24: the built link's kind is l % 2, its group l / 2.
  `placeAt_ns`: in scope: which entry `placeAt` takes its number of slots from.
  **`opened_leftQ`**: behind the link's first place: `LeftQ p.ns`.
  **`calls_reached`**: (1) and (2) in one.
  **`leftAt_reached`**: (3): by `calls_reached`, the lookups' `planOk_room` and their
    `k3_calls_leftAt` (Johnson/Desc/First/Look/K3CallsLeftAt.lean: an accept from `LeftQ p.ns`
    leaves `leftAtB`).

PREMISES: the goals' scope (hS, hR); the description's letters (O); its test on the list of rounds
(our files: the plan) accepts (hOk). THE START OF THE FOLD IS FREE.

Limits. Nothing on soundness. Not at the head's link. Laws from an accept: idle where the fold
rejects.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Desc.First.Look.K3CallsStated
import Johnson.Desc.First.Look.K3CallsLookLeftSeated
import Johnson.Desc.First.Look.K3CallsLeftAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits pieceAt)
open Johnson.Desc.First.Walk (startFork emptySlots)
open VerifiableInference.Desc.First.FillBare (leftAtB)

/-- The ledger from which a sub-proof starts: it has its sizes, ns slots, and every slot is free. -/
theorem startFork_leftQ (X : Johnson.Desc.First.Walk.LinkPub) (ns : ℕ) :
    LeftQ ns (startFork X ns) := by
  refine ⟨Johnson.Desc.First.Walk.startFork_sized X ns, rfl, fun j _ hj => ?_⟩
  have hj' : j < ns := hj
  show (Array.replicate ns false).getD j true = false
  simp [Array.getD, hj']

/-- A link of the list that is run has the built link's number of its group. -/
theorem zipped_g {B : Stages.LinksH} {ls : Array Stages.LinkH} {j : ℕ} {l : Stages.LinkH}
    (h : (OnBytes.L5.LinksOrder.zipped B ls)[j]? = some l) :
    ∃ b, B.links[j]? = some b ∧ b.kind = l.kind ∧ b.g = l.g := by
  unfold OnBytes.L5.LinksOrder.zipped at h
  rw [Array.getElem?_zipWith] at h
  cases hb : B.links[j]? with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases hl : ls[j]? with
    | none => rw [hl] at h; cases h
    | some x =>
      rw [hl] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl, rfl⟩

/-! ## The frame's letters' number of slots -/

open Johnson.Desc.First.Walk.Seat (frameAt zeroAt) in
theorem zeroAt_ns {built : Array Stages.LinkH} {W : Verify.Public}
    {P : Johnson.Desc.First.Walk.LayPar} (h : zeroAt built W = some P) :
    ∃ X hq, built[0]? = some X ∧ W.G[X.g]? = some hq ∧ P.ns = hq.ns := by
  unfold zeroAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hq, hG, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    exact ⟨X, hq, hX, hG, rfl⟩

open Johnson.Desc.First.Walk.Seat (frameAt) in
theorem frameAt_att_ns {built : Array Stages.LinkH} {W : Verify.Public} {l : ℕ}
    {P : Johnson.Desc.First.Walk.AttPar} {nLin : ℕ} (h : frameAt built W l = some (.att P nLin)) :
    ∃ X a, built[l]? = some X ∧ X.kind = 1 ∧ W.A[X.g]? = some a ∧ P.ns = a.ns := by
  unfold frameAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
  · split at h
    · rename_i hk
      obtain ⟨a, hA, h⟩ := Option.bind_eq_some_iff.1 h
      cases Option.some.inj h
      exact ⟨X, a, hX, by simpa using hk, hA, rfl⟩
    · split at h
      · obtain ⟨hq, -, h⟩ := Option.bind_eq_some_iff.1 h
        cases Option.some.inj h
      · cases h

open Johnson.Desc.First.Walk.Seat (frameAt) in
theorem frameAt_lay_ns {built : Array Stages.LinkH} {W : Verify.Public} {l : ℕ}
    {P : Johnson.Desc.First.Walk.LayPar} (h : frameAt built W l = some (.lay P)) :
    ∃ X hq, built[l]? = some X ∧ X.kind = 0 ∧ W.G[X.g]? = some hq ∧ P.ns = hq.ns := by
  unfold frameAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
  · split at h
    · obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.1 h
      cases Option.some.inj h
    · split at h
      · rename_i hk
        obtain ⟨hq, hG, h⟩ := Option.bind_eq_some_iff.1 h
        cases Option.some.inj h
        exact ⟨X, hq, hX, by simpa using hk, hG, rfl⟩
      · cases h

section Stated
variable {Cl : Type}

/-- **An accept of the stated block at the lookup on the calls is an accept of the kind's own
decision**, at the place's own parameters, from the same state to the same state. -/
theorem stated_calls_block (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hl : a.link = some i) (hpc : a.piece = pieceAt X i false) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (hdec : B.decide s rs gs = .ok t) :
    ∃ p laid sent rs' gs', Desc.First.Look.placeAt X i false = some p ∧
      (Desc.K3.block (seatCalls claim) a.piece laid sent p []).planOk = true ∧
      (Desc.K3.block (seatCalls claim) a.piece laid sent p []).decide s rs' gs' = .ok t := by
  obtain ⟨B₁, h1, -, ed, -, ep⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hw⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ h1
  obtain ⟨i', digits, p, sent, laid, hl', hpc', hp, -, -, -, edb, -, hpb⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hl.symm.trans hl')
  obtain rfl : false = digits := Desc.K3.pieceAt_inj X i (hpc.symm.trans hpc')
  rw [ed] at hdec
  rw [ep] at hOk
  have e : Desc.K3.seatOfLookupOnDigitsOrCalls claim false = seatCalls claim := by simp [Desc.K3.seatOfLookupOnDigitsOrCalls]
  have own : ∀ (s₁ : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      b.planOk = true → b.decide s rs gs = .ok s₁ →
      (Desc.K3.block (seatCalls claim) a.piece laid sent p []).planOk = true ∧
        (Desc.K3.block (seatCalls claim) a.piece laid sent p []).decide s rs gs = .ok s₁ := by
    intro s₁ rs gs hq hdc
    rw [edb, e] at hdc
    have hv := hpb hq
    rw [e] at hv
    exact ⟨(Desc.K3.Law.blockVia_planOk hv).1, Desc.K3.Law.blockVia_decide hv hdc⟩
  rcases hw with ⟨-, rfl⟩ | ⟨f, hf', rfl⟩
  · exact ⟨p, laid, sent, rs, gs, hp, own t rs gs hOk hdec⟩
  · have hq : b.planOk = true := by
      simpa [Desc.Block.andThen, Desc.roundlessBlock] using hOk
    have hdec' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
        (fun s₁ => f s₁) = .ok t := hdec
    cases hb1 : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
    | error x =>
      rw [hb1] at hdec'
      have k : (Except.error x : Except String S) = .ok t := hdec'
      cases k
    | ok s₁ =>
      rw [hb1] at hdec'
      have hq' : f s₁ = .ok t := hdec'
      obtain rfl := quiet_calls_same X a i hl hpc f hf' s₁ t hq'
      exact ⟨p, laid, sent, _, _, hp, own t _ _ hq hb1⟩

end Stated

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope: the built link number l < 24: its kind and the number of its group. -/
theorem built_at_scope (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 24) :
    ∃ X, Z.p.built.links[l]? = some X ∧ X.kind = l % 2 ∧ X.g = l / 2 := by
  obtain ⟨hn, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨ls, -, -, eB, -⟩ := IM.blank_ground O.blank
  obtain ⟨x, x', h0, k0, g0, -, h1, k1, g1, -⟩ := hn (l / 2) (by omega)
  rcases Nat.mod_two_eq_zero_or_one l with he | he
  · have e2 : 2 * (l / 2) = l := by omega
    rw [e2, eB] at h0
    obtain ⟨b, hb, kb, gb⟩ := zipped_g h0
    exact ⟨b, hb, by rw [kb, k0, he], by rw [gb, g0]⟩
  · have e2 : 2 * (l / 2) + 1 = l := by omega
    rw [e2, eB] at h1
    obtain ⟨b, hb, kb, gb⟩ := zipped_g h1
    exact ⟨b, hb, by rw [kb, k1, he], by rw [gb, g1]⟩

/-- In scope: the number of slots of the parameters of link l's lookup on the calls. -/
theorem placeAt_ns (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 24)
    (p : Desc.First.Look.P) (hp : Desc.First.Look.placeAt Z.p.X l false = some p) :
    (l % 2 = 0 → ∃ hq, Z.p.X.G[l / 2]? = some hq ∧ p.ns = hq.ns) ∧
      (l % 2 = 1 → ∃ a, Z.p.X.A[l / 2]? = some a ∧ p.ns = a.ns) := by
  have hX : Verify.publicOf Pf.pol Pf.KL (some lay) = .ok Z.p.X := O.W ▸ O.public
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  unfold Desc.First.Look.placeAt at hp
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hp
  unfold Desc.First.Look.lookAt at hx
  simp only [h4, hN, if_true] at hx
  rw [if_neg (by simp; omega)] at hx
  constructor
  · intro he
    rw [if_pos (by simp [he])] at hx
    obtain ⟨hq, h1, h2⟩ := Option.bind_eq_some_iff.1 hx
    refine ⟨hq, h1, ?_⟩
    simp only [Bool.false_eq_true, if_false] at h2
    obtain rfl := Option.some.inj h2
    rfl
  · intro he
    rw [if_neg (by simp [he])] at hx
    obtain ⟨a, h1, h2⟩ := Option.bind_eq_some_iff.1 hx
    refine ⟨a, h1, ?_⟩
    simp only [Bool.false_eq_true, if_false] at h2
    obtain rfl := Option.some.inj h2
    rfl

/-- **Behind the first place of a link in front of the head's stands the ledger that the lookup on
the calls wants in front**: it has its sizes, the place's own number of slots, and every slot is
free. -/
theorem opened_leftQ (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 24)
    {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + 1)) s₀ R C = .ok (t, R', C'))
    (p : Desc.First.Look.P) (hp : Desc.First.Look.placeAt Bs.G₀.W l false = some p) :
    ∃ G, t.fork? = some G ∧ LeftQ p.ns G := by
  rw [O.W] at hp
  obtain ⟨hev, hod⟩ := placeAt_ns hS hR O l hl p hp
  obtain ⟨X₀, hX₀, hk₀, hg₀⟩ := built_at_scope hS hR O l hl
  obtain ⟨fs, hfs, H⟩ := IM.frames_sit hS hR O
  obtain ⟨f, Lk, k, bL, b, b', bC, hf, -, -, -, -, -, hb, -, -, -, -, hy, -⟩ := H l (by omega)
  obtain ⟨s, R₁, C₁, rs, gs, -, hd⟩ := foldCut c.blocksInOrder (14 * l + 2) b hb h
  obtain ⟨m, rs', gs', -, hm⟩ := hy s rs gs t hd
  rcases IM.frames_arms hfs l f hf with ⟨X, hX, hk, -⟩ | ⟨rfl, P, hP, -, e, -⟩ |
    ⟨P, nLin, hP, -, e, -⟩ | ⟨P, hP, -, e, -⟩
  · exfalso
    obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
    omega
  · rw [e] at hm
    obtain ⟨X, hq, hX, hG, en⟩ := zeroAt_ns hP
    obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
    obtain ⟨hq', hG', ep⟩ := hev rfl
    rw [hg₀] at hG
    obtain rfl : hq = hq' := Option.some.inj (hG.symm.trans hG')
    refine ⟨_, (Johnson.Desc.First.Walk.openLayZero_is hm).1, ?_⟩
    rw [ep, ← en]
    exact startFork_leftQ _ _
  · rw [e] at hm
    obtain ⟨X, a, hX, hk, hA, en⟩ := frameAt_att_ns hP
    obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
    obtain ⟨a', hA', ep⟩ := hod (by omega)
    rw [hg₀] at hA
    obtain rfl : a = a' := Option.some.inj (hA.symm.trans hA')
    refine ⟨_, (Johnson.Desc.First.Walk.openAtt_is hm).1, ?_⟩
    rw [ep, ← en]
    exact startFork_leftQ _ _
  · rw [e] at hm
    obtain ⟨X, hq, hX, hk, hG, en⟩ := frameAt_lay_ns hP
    obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
    obtain ⟨hq', hG', ep⟩ := hev (by omega)
    rw [hg₀] at hG
    obtain rfl : hq = hq' := Option.some.inj (hG.symm.trans hG')
    refine ⟨_, (Johnson.Desc.First.Walk.openLay_is hm).1, ?_⟩
    rw [ep, ← en]
    exact startFork_leftQ _ _

/-- **THE LOOKUP ON THE CALLS, AS IT IS REACHED**, at the 24 links in front of the head's: the
fold's return behind it is an accept of the kind's own decision, at the place's own parameters,
whose test on the public data accepts, from a state whose ledger is `LeftQ` at the place's number
of slots. -/
theorem calls_reached (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (l : ℕ) (hl : l < 24) {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + IM.k3Ix l false + 1)) s₀ R C =
      .ok (t, R', C')) :
    ∃ (s : S) (G : Fork) (p : Desc.First.Look.P) (piece : ℕ) (laid : Array ℕ)
      (sent : List (ℕ × ℕ)) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      Desc.First.Look.placeAt Bs.G₀.W l false = some p ∧ s.fork? = some G ∧ LeftQ p.ns G ∧
      (Desc.K3.block (seatCalls K3Lot.ofForm) piece laid sent p []).planOk = true ∧
      (Desc.K3.block (seatCalls K3Lot.ofForm) piece laid sent p []).decide s rs gs = .ok t := by
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of hS hR O l (by omega) false
  have h5 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix l false)] at h5
  have hix : IM.k3Ix l false = 1 := by
    show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = _
    rw [if_neg (show ¬ l = 24 by omega)]
    rfl
  rw [hix] at h h5
  obtain ⟨s, R₁, C₁, rs, gs, hf, hd⟩ := foldCut c.blocksInOrder (14 * l + 2 + 1) b
    (by rw [show 14 * l + 2 + 1 = 14 * l + 1 + 2 by omega]; exact h5) h
  obtain ⟨b'', h3', hk⟩ := k03_const_ok hS hR O hOk l (by omega) false
  obtain rfl : b' = b'' := Option.some.inj (h3.symm.trans h3')
  obtain ⟨p, laid, sent, rs', gs', hp, hpl, hdc⟩ := stated_calls_block _ _ _ _ _ _ b' h3 hk l rfl
    (K3Lot.k03_place _ _ _ _ _ l false b' h3).1 s t rs gs ((IM.alone_underR h4).2 s rs gs t hd)
  obtain ⟨G, hG, hQ⟩ := opened_leftQ hS hR O l hl hf p hp
  exact ⟨s, G, p, _, laid, sent, rs', gs', hp, hG, hQ, hpl, hdc⟩

/-- **`leftAtB` AT THE STATE THAT IS REACHED BEHIND THE LOOKUP ON THE CALLS**, at the 24 links in
front of the head's: the test accepts what was heard and the ledger behind. -/
theorem leftAt_reached (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (l : ℕ) (hl : l < 24) {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + IM.k3Ix l false + 1)) s₀ R C =
      .ok (t, R', C')) :
    ∃ g G, t.lookHeard? = some g ∧ t.fork? = some G ∧ leftAtB g G = true := by
  obtain ⟨s, G, p, piece, laid, sent, rs, gs, hp, hG, hQ, hpl, hd⟩ :=
    calls_reached hS hR O hOk l hl h
  have hpl' : Desc.K3.planOk p laid ([] : List (Desc.First.Look.Guest S ProofFile.Cl)) = true := hpl
  unfold Desc.K3.planOk at hpl'
  rw [Bool.and_eq_true] at hpl'
  obtain ⟨hs, hsh, -⟩ := planOk_room hpl'.1
  exact k3_calls_leftAt K3Lot.ofForm piece laid sent p [] s t rs gs hsh hd hG hQ

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.startFork_leftQ
#print axioms VerifiableInference.OnPublicFiles.zipped_g
#print axioms VerifiableInference.OnPublicFiles.zeroAt_ns
#print axioms VerifiableInference.OnPublicFiles.frameAt_att_ns
#print axioms VerifiableInference.OnPublicFiles.frameAt_lay_ns
#print axioms VerifiableInference.OnPublicFiles.stated_calls_block
#print axioms VerifiableInference.OnPublicFiles.built_at_scope
#print axioms VerifiableInference.OnPublicFiles.placeAt_ns
#print axioms VerifiableInference.OnPublicFiles.opened_leftQ
#print axioms VerifiableInference.OnPublicFiles.calls_reached
#print axioms VerifiableInference.OnPublicFiles.leftAt_reached
