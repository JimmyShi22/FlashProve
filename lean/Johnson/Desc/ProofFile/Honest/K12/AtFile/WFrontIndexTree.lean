-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontIndexTree.lean: the tree of the index masks' message at
the end of the first chain's fold, under the head AtMgA at the older hash: it holds that message alone
and is not opened at one list only.

  firstTree_written  the closed line at the written first sending
  joinAll_book, decideSend_behind, firstAtS_book   the first sending behind its record, on the book
  tree_at_three      behind the first sending
  indexTree_at_end   at the first chain's end

Limits.
- The full size alone.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontTreeStays
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontAtOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (firstPar firstSegmentOpening qFull shapesOf)
open OnBytes.Params (ReqMessage)
open Johnson.AtFull.Shape (gpW)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

set_option maxRecDepth 1000000 in
/-- **At the written first sending tree 1 holds message 4 alone, and has not the mark of one list.** -/
theorem firstTree_written :
    ((partsLaid (firstPar qFull gpW).sent
        ((layTrees (firstPar qFull gpW).codes (firstPar qFull gpW).sent).getD {}) 0 0
        (treesSent (firstPar qFull gpW).gp.firstTree
          ((layTrees (firstPar qFull gpW).codes (firstPar qFull gpW).sent).getD {}).shapes.toList 0
          #[]))[1]?).map (fun T => (T.parts, T.oneList)) = some (#[4], false) := by
  decide +kernel

theorem joinAll_book {L : Type} (p : _root_.Desc.Plain.GPar) (g : ℕ) :
    ∀ (l : List (ReqMessage × ℕ)) (d d' : _root_.Desc.Plain.DState L),
      VerifiableInference.Desc.First.Send.joinAll VerifiableInference.Desc.Ground.groundG p g l d =
        some d' → d'.book = d.book ∧ d'.roots = d.roots
  | [], d, d', h => by
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  | x :: l, d, d', h => by
    simp only [VerifiableInference.Desc.First.Send.joinAll, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨d₁, h1, h2⟩ := h
    obtain ⟨a, b⟩ := joinAll_book p g l d₁ d' h2
    have k := VerifiableInference.Desc.Ground.coreStill_same.join _ _ _ _ _ h1
    exact ⟨a.trans k.1, b.trans k.2⟩

theorem decideSend_behind {L : Type} (P : VerifiableInference.Desc.K1.Par) (owed : Option ℕ)
    (d d' : _root_.Desc.Plain.DState L) (rs : List Fmt.RoundView) (ids : Array ℕ)
    (h : VerifiableInference.Desc.K1.decideSend P owed d rs = .ok (ids, d')) :
    ∃ seeds ys, d' = VerifiableInference.Desc.K1.behind P d seeds ys := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨-, -, e⟩ := (VerifiableInference.Desc.K1.decideSend_iff P owed d d' r₁ r₂ ids).1 h
    exact ⟨_, _, e⟩

/-- **The first sending behind its record, on the book.** -/
theorem firstAtS_book {Cl : Type} (q : Params.First) (gp : _root_.Desc.Plain.GPar) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s rs gs = .ok s') :
    ∃ c d', VerifiableInference.Desc.K1.firstOwn (firstPar q gp) (VerifiableInference.Desc.K1.owedOf s)
        s.check (VerifiableInference.Desc.K1.stateOf s ()) rs = .ok (c, d') ∧ s'.book = d'.book := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact ⟨c, d', h2, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Behind the first sending.** -/
theorem tree_at_three (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {t₃ : S}
    {R R₃ : List Fmt.RoundView} {C C₃ : List OpenedColumn}
    (f₃ : foldBlocks 0 (cF.blocksInOrder.take 3) (ProofFile.startS Zp pI) R C = .ok (t₃, R₃, C₃)) :
    ∃ T : OnBytes.Tree, t₃.book.trees[1]? = some T ∧ T.parts = #[4] ∧ T.oneList = false := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨t₀, R₀, C₀, f₀⟩ := Meaning.K2.fold_back (k := 2) f₃
  have e0s := Meaning.K2.laid_is_start h.scope h.reads O f₀
  obtain ⟨e, nm, X, hfl, hX, hu⟩ := IM.first_under h.scope h.reads O
  obtain ⟨rs, gs, d⟩ := Meaning.K2.fold_next hfl f₀ f₃
  have hy := hu.2 _ _ _ _ d
  obtain ⟨m, y1, y3⟩ := VerifiableInference.Desc.Keeps.ebind_ok
    (x := (firstSegmentOpening Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) :
      Block S ProofFile.Cl).decide t₀ (rs.take (firstSegmentOpening Bs.G₀.first
              (VerifiableInference.Desc.K1.gpOf Zp) : Block S ProofFile.Cl).rounds.length)
        (gs.take (firstSegmentOpening Bs.G₀.first
        (VerifiableInference.Desc.K1.gpOf Zp) : Block S ProofFile.Cl).openings)) hy
  obtain ⟨a, eT⟩ := Johnson.Desc.First.Walk.Tied.openLayZero_eq y3
  have ebk : t₃.book = m.book := by rw [eT]
  have hq : Bs.G₀.first = Zp.first := O.first
  have hP := Johnson.AtFull.Shape.firstPar_at_head h.toAtMg O
  rw [hq] at y1 hP
  obtain ⟨c', d', h1, e1⟩ := firstAtS_book _ _ t₀ m _ _ y1
  obtain ⟨g, d₁, ids, d₂, hng, hds, f₁, own, mine, f₂, hjo⟩ :=
    VerifiableInference.Desc.K1.firstOwn_ok _ _ _ c' _ d' _ h1
  have hjb : d'.book = d₂.book := by
    unfold VerifiableInference.Desc.First.Send.joinOwnP at hjo
    split at hjo
    · obtain ⟨d₃, h3, e3⟩ := Option.map_eq_some_iff.1 hjo
      obtain rfl : d₃ = d' := (Prod.mk.inj e3).2
      exact (joinAll_book _ _ _ _ _ h3).1
    · cases hjo
  have hst := Meaning.K2.start_empty O.pub pI
  have hm₀ : (VerifiableInference.Desc.K1.stateOf t₀ ()).st.oracles = #[] := by
    show t₀.st.oracles = #[]
    rw [e0s]
    exact Meaning.K2.start_msgs O.pub pI
  have hn₁ := VerifiableInference.Desc.Ground.coreStill_same.newGroup _ _ _ _ _ hng
  have hb₁ : d₁.book.trees = #[] := by
    have k : d₁.book = t₀.book := hn₁.1
    rw [k, e0s, hst.1]
  have hr₁ : d₁.roots = 0 := by
    have k : d₁.roots = t₀.roots := hn₁.2
    rw [k, e0s, hst.2]
  have hg₁ : d₁.st.oracles.size = 0 := by
    have k := hng
    unfold VerifiableInference.Desc.Ground.newGroupP at k
    split at k
    · simp only [Option.some.injEq, Prod.mk.injEq] at k
      obtain ⟨-, rfl⟩ := k
      show (VerifiableInference.Desc.K1.stateOf t₀ ()).st.oracles.size = 0
      rw [hm₀]
      rfl
    · cases k
  obtain ⟨seeds, ys, hb⟩ := decideSend_behind _ _ _ _ _ _ hds
  have w := firstTree_written
  obtain ⟨T, hT, eT₂⟩ := Option.map_eq_some_iff.1 w
  obtain ⟨p₁, p₂⟩ := Prod.mk.inj eT₂
  refine ⟨T, ?_, p₁, p₂⟩
  have e : d₂.book.trees = partsLaid (firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)).sent
      ((layTrees (firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)).codes
        (firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)).sent).getD {})
      d₁.st.oracles.size d₁.book.trees.size
      (treesSent (firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)).gp.firstTree
        ((layTrees (firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)).codes
          (firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)).sent).getD {}).shapes.toList
        d₁.roots d₁.book.trees) := by
    rw [hb]
    rfl
  rw [ebk, e1, hjb, e, hg₁, hb₁, hr₁, hP]
  exact hT

/-- **At the first chain's end.** -/
theorem indexTree_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) :
    IndexTreeIs e₁.book := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rw [← List.take_append_drop 3 cF.blocksInOrder] at hf
  obtain ⟨t, r₁, c₁, f1, f2⟩ := Johnson.Desc.First.Walk.Tied.fold_split 0 _ _ _ _ _ _ hf
  obtain ⟨T, hT, hp, ho⟩ := tree_at_three h f1
  have hstay : TreeStays t.book e₁.book :=
    VerifiableInference.Desc.Keeps.foldBlocks_keeps TS
      (fun _ => TreeStays.refl _) (fun _ _ _ h k => h.trans k) 0 _
      (fun b hb => Meaning.K2.open_flat seatKeeps_tree seatBack_tree O trivial
        (fun _ _ _ => trivial) b (List.mem_of_mem_drop hb)
        (Johnson.AtFull.Shape.plans_at h b (List.mem_of_mem_drop hb)))
      t r₁ c₁ _ f2
  obtain ⟨T', hT', e₁', e₂⟩ := hstay 1 T hT
  exact ⟨T', hT', e₁'.trans hp, e₂.trans ho⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.tree_at_three
#print axioms ProofFile.Honest.K12.AtFile.indexTree_at_end
#print axioms ProofFile.Honest.K12.AtFile.firstTree_written
#print axioms ProofFile.Honest.K12.AtFile.firstAtS_book
