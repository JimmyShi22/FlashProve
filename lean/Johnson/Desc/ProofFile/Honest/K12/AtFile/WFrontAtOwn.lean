-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontAtOwn.lean: the shape on entry to the last chain's own test
agrees with the closed shape narrowW, so the test frontFiveB says yes there.

  takeOver_parts, adopt_tree   what the block "K14, second part" does, and the tree that it lays
  OmegaIs          the named premise on Omega in the shared chain's end
  IndexTreeIs      the named premise on the index masks' tree at the first chain's end
  sameCore_at_own  the relation at the record on entry
  frontFive_at_own the test

The head is AtMgA at the older hash.

Limits.
- OmegaIs and IndexTreeIs are premises here; WFrontAtSeat.lean pays them.
- The parameters are the written ones: WFrontAtSeat.lean carries the test to the seated place.
- The full size alone, at the files in the head's scope.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontEndIs
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontEndTrees
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontFile
import Johnson.Desc.Third.Law.StartBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (linAt LFull)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut batchLinearConstraintsSecondPart start₃E startAtEnds sharedOfEnd)
open VerifiableInference.Desc.Third.Law (laid_k14Second start₃E_inv start₃_inv firstOutFrom_inv)
open ProofFile.Honest.Sh (TestSh testSh)
open H2K.Member (piWFull codesFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- **The named premise on Omega**, in the shared chain's end. -/
structure OmegaIs (o : SharedOut) : Prop where
  tree : ∃ (q : ℕ × ℕ) (T : OnBytes.Tree), o.book.place[o.omega]? = some q ∧
    o.book.trees[q.1]? = some T ∧ T.number = 1

/-- **The named premise on the index masks' tree**, at the first chain's end. -/
structure IndexTreeIs (B : TreeBook) : Prop where
  tree : ∃ T : OnBytes.Tree, B.trees[1]? = some T ∧ T.parts = #[4] ∧ T.oneList = false

theorem stripT_of (T : OnBytes.Tree) (m : TreeSh) (h1 : T.shape = m.shape) (h2 : T.number = m.number)
    (h3 : T.parts.toList = m.parts) : stripT (treeSh T) = stripT m := by
  cases m
  simp only [stripT, treeSh] at *
  rw [h1, h2, h3]

set_option maxRecDepth 1000000 in
theorem narrow_msgs : narrowW.st.oracles[4]? = some indexMsg ∧ narrowW.st.oracles[197]? = some wMsg ∧
    narrowW.st.oracles[198]? = some maskMsg ∧ narrowW.st.oracles[199]? = some omegaMsg ∧
    narrowW.st.oracles.length = 200 ∧ narrowW.book.place.length = 200 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem narrow_book : narrowW.book.place[4]? = some (1, 0) ∧ narrowW.book.place[197]? = some (82, 0) ∧
    narrowW.book.place[198]? = some (82, 1) ∧ narrowW.book.place[199]? = some (83, 0) ∧
    narrowW.book.trees[1]? = some indexTree ∧ narrowW.book.trees[82]? = some wTree ∧
    narrowW.book.trees[83]? = some omegaTree := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem narrow_guards : openedAt indexTree = true ∧ openedAt wTree = true ∧
    openedAt omegaTree = true ∧ sharesAt narrowW.st indexTree = true ∧
    sharesAt narrowW.st wTree = true ∧ sharesAt narrowW.st omegaTree = true := by
  decide +kernel

theorem early_written : piWFull.early = true := by decide +kernel

/-- **What the taking over of Omega has done**, with Omega's shape. -/
theorem takeOver_parts (S : Params.LinShape) (own : ℕ) (o : SharedOut)
    (d : _root_.Desc.Plain.DState VerifiableInference.Desc.Third.Loc₃)
    (r : ℕ × _root_.Desc.Plain.DState VerifiableInference.Desc.Third.Loc₃)
    (h : VerifiableInference.Desc.Third.takeOver S own o d = .ok r) :
    ∃ q t y a d₁, o.book.place[o.omega]? = some q ∧ o.book.trees[q.1]? = some t ∧
      o.st.oracles[o.omega]? = some y ∧ y.shape = S.omega ∧
      VerifiableInference.Desc.Ground.adoptP d #[{ shape := y.shape, leafClass := S.omegaLeafClass }]
        #[(t.number, t.src)] = some a ∧
      a.1[0]? = some r.1 ∧ VerifiableInference.Desc.Ground.elsewhereP a.2 r.1 o.st o.omega = some d₁ ∧
      VerifiableInference.Desc.Ground.joinP d₁ own r.1 false = some r.2 := by
  obtain ⟨q, t, y, a, d₁, c1, c2, c3, c4, c5, c6, c7⟩ :=
    VerifiableInference.Desc.Third.Law.takeOver_inv S own o d r h
  refine ⟨q, t, y, a, d₁, c1, c2, c3, ?_, c4, c5, c6, c7⟩
  unfold VerifiableInference.Desc.Third.takeOver at h
  obtain ⟨q', hq, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨t', ht, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨y', hy, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨_, hn, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain rfl := Option.some.inj ((VerifiableInference.Desc.Third.Law.some_of_named hy).symm.trans c3)
  unfold VerifiableInference.Desc.need at hn
  split at hn
  · rename_i hc
    exact of_decide_eq_true hc
  · cases hn

/-- **The new tree behind an adoption of one message.** -/
theorem adopt_tree {L : Type} (d : _root_.Desc.Plain.DState L) (n : OracleNotice) (num : ℕ)
    (src : Fmt.Src) (a : Array ℕ × _root_.Desc.Plain.DState L)
    (h : VerifiableInference.Desc.Ground.adoptP d #[n] #[(num, src)] = some a)
    (lay : TreeLay) (hl : VerifiableInference.Desc.Own.treesMade d.st.codes #[n] = some lay)
    (ht : lay.tree.getD 0 0 = 0) :
    a.2.book.trees[d.book.trees.size]? = some
      { shape := lay.shapes.getD 0 {}, number := num, src := src, parts := #[d.st.oracles.size] } := by
  unfold VerifiableInference.Desc.Ground.adoptP at h
  split at h
  · rw [hl] at h
    obtain rfl := Option.some.inj h
    have er : List.range 1 = [0] := rfl
    have sz : (#[n] : Array OracleNotice).size = 1 := rfl
    have sz₂ : (#[(num, src)] : Array (ℕ × Fmt.Src)).size = 1 := rfl
    dsimp only
    simp only [sz, sz₂, er, List.foldl_cons, List.foldl_nil, ht, Nat.add_zero]
    rw [Array.getElem?_modify, if_pos rfl, Array.getElem?_push_eq]
    rfl
  · cases h

theorem elsewhere_book {L : Type} {d d' : _root_.Desc.Plain.DState L} {m t : ℕ} {o : Statement}
    (h : VerifiableInference.Desc.Ground.elsewhereP d m o t = some d') : d'.book = d.book := by
  unfold VerifiableInference.Desc.Ground.elsewhereP at h
  split at h
  · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h

theorem join_book {L : Type} {d d' : _root_.Desc.Plain.DState L} {g o : ℕ} {k : Bool}
    (h : VerifiableInference.Desc.Ground.joinP d g o k = some d') : d'.book = d.book := by
  unfold VerifiableInference.Desc.Ground.joinP at h
  split at h
  · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h

theorem addRow_book {L : Type} {d d' : _root_.Desc.Plain.DState L} {g : ℕ} {row : OnBytes.Row}
    (h : VerifiableInference.Desc.Ground.addRowP d g row = some d') : d'.book = d.book := by
  unfold VerifiableInference.Desc.Ground.addRowP at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

set_option maxRecDepth 1000000 in
theorem omega_lay :
    (((VerifiableInference.Desc.Own.treesMade codesFull
      #[{
        shape := proofSizedFull.batch.shape.omega
        leafClass := proofSizedFull.batch.shape.omegaLeafClass }]).map fun l =>
        (l.tree.getD 0 0, l.shapes.getD 0 {})) = some (0, omegaTree.shape)) ∧
    proofSizedFull.batch.shape.omega = omegaMsg.shape := by
  decide +kernel

theorem sharesAt_single (a : StSh) (T : TreeSh) (o : ℕ) (y : OrcSh) (hp : T.parts = [o])
    (hy : a.oracles[o]? = some y) (hans : y.shape.answers ≠ 0)
    (hg : T.oneList = false ∨ y.groups.length ≤ 1) : sharesAt a T = true := by
  unfold sharesAt
  rw [hp]
  simp only [List.filterMap_cons, List.filterMap_nil, hy, Option.bind_some, beq_iff_eq, hans,
    if_false]
  simp only [sharesOk, List.all_nil, Bool.true_and]
  rcases hg with e | e
  · simp [e]
  · simp [e]

theorem sharesAt_pair (a : StSh) (T : TreeSh) (o₁ o₂ : ℕ) (y₁ y₂ : OrcSh) (hp : T.parts = [o₁, o₂])
    (h₁ : a.oracles[o₁]? = some y₁) (h₂ : a.oracles[o₂]? = some y₂) (a₁ : y₁.shape.answers ≠ 0)
    (a₂ : y₂.shape.answers = 0) (hg : y₁.groups.length ≤ 1) : sharesAt a T = true := by
  unfold sharesAt
  rw [hp]
  simp only [List.filterMap_cons, List.filterMap_nil, h₁, h₂, Option.bind_some, beq_iff_eq, a₁, a₂,
    if_false, if_true]
  simp only [sharesOk, List.all_nil, Bool.true_and]
  simp [hg]

/-- Omega in the last chain's statement. -/
def omegaCopy (y : OnBytes.Oracle) (own : ℕ) : OnBytes.Oracle := {
  shape := y.shape, sampled := true, sampleRows := y.sampleRows.map (·.renamed 199), pad := y.pad
  groups := [own] }

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The shape on entry to the last chain's own test agrees with the closed shape.** -/
theorem sameCore_at_own {Cl : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (pI : ProofFile.InstPub)
    {e₁ : S} {d : Desc.K14.St} {r₁ r₀ r₂ u : List Fmt.RoundView} {c₁ c₀ c₂ v : List OpenedColumn}
    (hf₁ : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀))
    (hf₂ : foldBlocks 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₂ pI) r₂ c₂ = .ok (d, u, v)) {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12}
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ pI e₁ d = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) (H2K.JointK.p₁₄N Zp)).decide s₀ rs gs = .ok s)
    (h₂ : enterOwn s = .ok t)
    (hO : ∀ E₂, Desc.K14.ended d = some E₂ → OmegaIs (sharedOfEnd E₂))
    (hT : IndexTreeIs e₁.book) :
    SameCore [4, 197, 198, 199] t.g 0 (coreSh ⟨t.st, t.book, t.roots⟩) narrowW ∧
      t.mask = some 198 ∧ t.pass = .nothing := by
  obtain ⟨E₂, f, hE, hfo, h0⟩ := startParts hs
  obtain ⟨l, hl, e1, e2, e3, e4, e5⟩ := firstOfS_parts hfo
  have hm : e₁.failed = none := start_noMark hs
  have EW := endWritten h hf₁ hm
  obtain ⟨hw, hmk, ⟨y₇, hy₇, hg₇⟩, -⟩ := atW_numbers h hf₁ hm hl
  rw [e5, hmk] at h0
  have hn : ∀ y : OnBytes.Oracle, e₁.st.oracles[198]? = some y → y.sampled = false :=
    fun y hy => (mask_of_start h0 (by rw [e1]; exact hy)).1
  have EI := endIs h hf₁ hm hl hn
  obtain ⟨htr, Tw, hTw, nW, sW, pW, lW⟩ := wTree_at_end h hf₁ hm hl
  obtain ⟨Ti, hTi, pTi, oTi⟩ := hT.tree
  have nI := EW.number _ _ hTi
  have sI : Ti.shape = indexTree.shape := by
    have k := tree_shape EW.seats hTi
    rw [treeShapes_written.1] at k
    exact (Option.some.inj k).symm
  -- the start
  obtain ⟨ff, hff, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h0
  obtain ⟨-, ef, -, eo, em, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hff
  obtain ⟨ec₁, ec₂, e0⟩ := start₃_inv _ _ _ _ hst
  have es₀ : s₀.st = e₁.st := by rw [e0, ← e1]; exact ef
  have eown : s₀.loc.own = l.own := by rw [e0, ← e3]; exact eo
  have emask : s₀.loc.mask = some 198 := by rw [e0]; exact em
  obtain ⟨eb, er, -⟩ := VerifiableInference.Desc.Third.Law.start₃E_book _ _ _ _ _ _ _ _ _ _ _ h0
  have eb' : s₀.book = e₁.book := eb.trans e2
  obtain ⟨g₀, hbd₀⟩ := VerifiableInference.Desc.Third.Law.start₃E_border _ _ _ _ _ _ _ _ _ _ _ h0
  -- the block
  obtain ⟨b, y₀, G, dot, L⟩ := laid_k14Second _ s₀ s rs gs h₁
  obtain ⟨x₂, a₂, dt, b₂, i1, i2, i3, i4, i5⟩ :=
    VerifiableInference.Desc.Third.Law.k14Second_inv _ s₀ s rs gs h₁
  have hbd : b.shared = sharedOfEnd E₂ := by
    have e := L.border.symm.trans hbd₀
    rw [Option.some.injEq] at e
    rw [e]
  have hxb : b = x₂ := Option.some.inj (L.border.symm.trans i1)
  subst hxb
  obtain ⟨q₂, t₂, y₂, a₃, d₁, k1, k2, k3, k4, k5, k6, k7, k8⟩ := takeOver_parts _ _ _ _ _ i2
  obtain rfl : y₀ = y₂ := Option.some.inj (L.there.symm.trans k3)
  have hlin : (H2K.JointK.p₁₄N Zp).S = proofSizedFull.batch.shape := by
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    have hpl : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (Desc.K14.Law.seatZ Zp Np)
        (Desc.K14.Law.secondAt Zp Np) (fun s => s) (ProofFile.startS Zp) cF).planOk = true := by
      rw [← O.desc]
      exact h.laid.planOk
    have k := P2R0.lin_sized O.pub (P2R0.front2_at_planOk _ _ _ _ _ _ _ _ _ _ _ _ _ hpl)
    exact k.symm.trans (lin_at_head h)
  rw [hlin] at k4
  obtain ⟨ow₁, ow₂⟩ := omega_lay
  have ysh : y₀.shape = omegaMsg.shape := k4.trans ow₂
  -- Omega's tree
  have hO' := (hO E₂ hE).tree
  rw [← hbd] at hO'
  obtain ⟨q₃, T₃, l1, l2, n₃⟩ := hO'
  obtain rfl : q₃ = q₂ := Option.some.inj (l1.symm.trans k1)
  obtain rfl : T₃ = t₂ := Option.some.inj (l2.symm.trans k2)
  have hcod : e₁.st.codes = codesFull := EI.codes
  obtain ⟨lay, hlay, elay⟩ := Option.map_eq_some_iff.1 ow₁
  obtain ⟨ht₀, hsh₀⟩ := Prod.mk.inj elay
  have hbook₀ : (s₀.withCols []).book = e₁.book := eb'
  have hst₀ : (s₀.withCols []).st = e₁.st := es₀
  have hnote : ({ shape := y₀.shape, leafClass := (H2K.JointK.p₁₄N Zp).S.omegaLeafClass } :
      OracleNotice) = {
        shape := proofSizedFull.batch.shape.omega
        leafClass := proofSizedFull.batch.shape.omegaLeafClass } := by
    rw [k4, hlin]
  rw [hnote] at k5
  have hadopt := adopt_tree _ _ _ _ _ k5 lay (by rw [hst₀, hcod]; exact hlay) ht₀
  rw [hbook₀, hst₀, htr, EW.msgs] at hadopt
  have bk : b₂.book = a₃.2.book := by
    rw [addRow_book i4, join_book k8, elsewhere_book k7]
  have hs₅ := i5
  have esb : s.book = b₂.book := by rw [hs₅]
  have htω : s.book.trees[83]? = some {
      shape := lay.shapes.getD 0 {}, number := T₃.number, src := T₃.src, parts := #[199] } := by
    rw [esb, bk]
    exact hadopt
  -- the block's statement and book
  have hsz₀ : s₀.st.oracles.size = 199 := by rw [es₀]; exact EW.msgs
  have hpl₀ : s₀.book.place.size = 199 := by rw [eb']; exact EW.places
  have htr₀ : s₀.book.trees.size = 83 := by rw [eb']; exact htr
  have oS : ∀ o, o < 199 → s.st.oracles[o]? = e₁.st.oracles[o]? := fun o ho => by
    rw [L.old o (by omega), es₀]
  have pS : ∀ o, o < 199 → s.book.place[o]? = e₁.book.place[o]? := fun o ho => by
    rw [L.oldPlaces o (by omega), eb']
  have tS : ∀ i, i < 83 → s.book.trees[i]? = e₁.book.trees[i]? := fun i hi => by
    rw [L.oldTrees i (by omega), eb']
  have hcopy := L.copy
  rw [hsz₀] at hcopy
  have hplω := L.place
  rw [hsz₀, htr₀] at hplω
  have hsize : s.st.oracles.size = 200 := by rw [L.size, hsz₀]
  have hplsz : s.book.place.size = 200 := by rw [L.places, hpl₀]
  have hcodS : s.st.codes = codesFull := by rw [L.codes, es₀]; exact hcod
  obtain ⟨y₄, hy₄, sy₄⟩ := EI.msg₄
  obtain ⟨z₇, hz₇, sz₇, gz₇⟩ := EI.msg₁₉₇
  obtain ⟨y₈, hy₈, sy₈⟩ := EI.msg₁₉₈
  obtain ⟨G₁, row, hG₁, gc, gm, gr, gmem, gk, grow, gkind⟩ := EI.group
  have hG₀ : s₀.st.groups[s₀.loc.own]? = some G₁ := by rw [es₀, eown]; exact hG₁
  obtain rfl : G = G₁ := Option.some.inj (L.group.symm.trans hG₀)
  have hF : MembersFacts e₁.st := membersFacts_reached h 358 0 pI r₁ c₁ (e₁, r₀, c₀) (by
    rw [← Johnson.AtFull.Shape.flat_len h, List.take_length]
    exact hf₁)
  have hWd : WellSampled d.st := wellSampled_at_end h pI.key hf₂
  have hst₂ : E₂.st = d.st := Desc.K14.ended_st hE
  have hshared : b.shared.st = d.st := by rw [hbd]; exact hst₂
  have hΩ := hWd b.shared.omega y₀ (by rw [← hshared]; exact L.there) L.sampled
  obtain ⟨wa, wl, whl, wp⟩ := hΩ
  have hcod₂ : d.st.codes = codesFull := by
    have e₀ : (sharedOfEnd E₂).st.codes = ff.st.codes := ec₂.trans ec₁.symm
    have e₂ : (sharedOfEnd E₂).st = d.st := hst₂
    rw [← e₂, e₀, ef, e1]
    exact hcod
  have spads := pads_written.2.2
  rw [← ysh, hcod₂.symm, whl] at spads
  have sΩ : strip (orcSh (omegaCopy y₀ s₀.loc.own)) = strip omegaMsg := by
    refine strip_of _ _ ysh rfl ?_ ?_ rfl
    · show (y₀.sampleRows.map _).size = 1
      rw [Array.size_map, wa, ysh]
      rfl
    · show y₀.pad = omegaMsg.pad
      rw [wp]
      exact Option.some.inj spads
  have et : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                  mask := s.loc.mask } := (Except.ok.inj h₂).symm
  subst et
  have hown : s.loc.own = s₀.loc.own := by rw [L.loc]
  have hmS : s.loc.mask = some 198 := by rw [L.loc]; exact emask
  have hp₄ := (pS 4 (by omega)).trans ((EW.place 4 (by omega)).trans places_written.1)
  have hp₇ := (pS 197 (by omega)).trans ((EW.place 197 (by omega)).trans places_written.2.1)
  have hp₈ := (pS 198 (by omega)).trans ((EW.place 198 (by omega)).trans places_written.2.2)
  have ht₁ := (tS 1 (by omega)).trans hTi
  have ht₈ := (tS 82 (by omega)).trans hTw
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := narrow_msgs
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := narrow_book
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := narrow_guards
  have ho₄ : (stSh s.st).oracles[4]? = some (orcSh y₄) := by
    rw [orc_get, oS 4 (by omega), hy₄]
    rfl
  have ho₇ : (stSh s.st).oracles[197]? = some (orcSh z₇) := by
    rw [orc_get, oS 197 (by omega), hz₇]
    rfl
  have ho₈ : (stSh s.st).oracles[198]? = some (orcSh y₈) := by
    rw [orc_get, oS 198 (by omega), hy₈]
    rfl
  have ho₉ : (stSh s.st).oracles[199]? = some (orcSh (omegaCopy y₀ s₀.loc.own)) := by
    rw [orc_get, hcopy]
    rfl
  have ea₄ : y₄.shape.answers ≠ 0 := by
    have e := congrArg (fun m : OrcSh => m.shape.answers) sy₄
    have e' : y₄.shape.answers = 1 := e
    omega
  have ea₇ : z₇.shape.answers ≠ 0 := by
    have e := congrArg (fun m : OrcSh => m.shape.answers) sz₇
    have e' : z₇.shape.answers = 1 := e
    omega
  have ea₈ : y₈.shape.answers = 0 := congrArg (fun m : OrcSh => m.shape.answers) sy₈
  have tω : stripT (treeSh {
      shape := lay.shapes.getD 0 {}, number := T₃.number, src := T₃.src, parts := #[199] }) =
      stripT omegaTree := stripT_of _ _ hsh₀ n₃ rfl
  have hgroup : (stSh s.st).groups[s.loc.own]? = some ownGroup := by
    rw [grp_get, hown, L.group']
    have m₁ : G.members = #[4, 197] := Array.toList_inj.1 gmem
    have k₁ : G.kept = #[false, false] := Array.toList_inj.1 gk
    rw [hsz₀]
    show some (grpSh _) = some ownGroup
    refine congrArg some ?_
    simp only [grpSh, ownGroup, gc, gm, gr, m₁, k₁, grow]
    have e₁ : ((#[4, 197] : Array ℕ).insertIdxIfInBounds
        ((#[4, 197] : Array ℕ).filter (· < 199)).size 199).toList = [4, 197, 199] := by decide +kernel
    have e₂ : ((#[false, false] : Array Bool).insertIdxIfInBounds
        ((#[4, 197] : Array ℕ).filter (· < 199)).size false).toList = [false, false, false] := by
      decide +kernel
    rw [e₁, e₂]
    simp [gkind, L.plain]
  obtain ⟨-, -, -, hm₈⟩ := atW_numbers h hf₁ hm hl
  obtain ⟨y₈', hy₈', -, -, y₈g', -, -⟩ := hm₈ hn
  obtain rfl : y₈ = y₈' := Option.some.inj (hy₈.symm.trans hy₈')
  have y₈g := y₈g'
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, hmS, rfl⟩
  · exact hcodS.symm
  · show narrowW.st.oracles.length = (stSh s.st).oracles.length
    rw [orc_size, hsize, n5]
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · show (narrowW.st.oracles[4]?).map strip = ((stSh s.st).oracles[4]?).map strip
      rw [n1, ho₄]
      exact congrArg some sy₄.symm
    · show (narrowW.st.oracles[197]?).map strip = ((stSh s.st).oracles[197]?).map strip
      rw [n2, ho₇]
      exact congrArg some sz₇.symm
    · show (narrowW.st.oracles[198]?).map strip = ((stSh s.st).oracles[198]?).map strip
      rw [n3, ho₈]
      exact congrArg some sy₈.symm
    · show (narrowW.st.oracles[199]?).map strip = ((stSh s.st).oracles[199]?).map strip
      rw [n4, ho₉]
      exact congrArg some sΩ.symm
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    show narrowW.book.place[o]? = (bookSh s.book).place[o]?
    rw [place_get]
    rcases ho with rfl | rfl | rfl | rfl
    · rw [b1, hp₄]
    · rw [b2, hp₇]
    · rw [b3, hp₈]
    · rw [b4, hplω]
  · show narrowW.book.place.length = (bookSh s.book).place.length
    rw [place_size, hplsz, n6]
  · intro o ho q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    have hq' : s.book.place[o]? = some q := by
      rw [← place_get]
      exact hq
    rcases ho with rfl | rfl | rfl | rfl
    · rw [hp₄] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[1]?).map stripT = ((bookSh s.book).trees[1]?).map stripT
      rw [b5, tree_get, ht₁]
      exact congrArg some (stripT_of Ti _ sI nI (by rw [pTi]; rfl)).symm
    · rw [hp₇] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[82]?).map stripT = ((bookSh s.book).trees[82]?).map stripT
      rw [b6, tree_get, ht₈]
      exact congrArg some (stripT_of Tw _ sW nW (by rw [pW]; rfl)).symm
    · rw [hp₈] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[82]?).map stripT = ((bookSh s.book).trees[82]?).map stripT
      rw [b6, tree_get, ht₈]
      exact congrArg some (stripT_of Tw _ sW nW (by rw [pW]; rfl)).symm
    · rw [hplω] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[83]?).map stripT = ((bookSh s.book).trees[83]?).map stripT
      rw [b7, tree_get, htω]
      exact congrArg some tω.symm
  · intro o ho q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    have hq' : s.book.place[o]? = some q := by
      rw [← place_get]
      exact hq
    have e₁ : openedAt (treeSh Ti) = true := by simp [openedAt, treeSh, oTi]
    have e₂ : openedAt (treeSh Tw) = true := by simp [openedAt, treeSh, lW]
    rcases ho with rfl | rfl | rfl | rfl
    · rw [hp₄] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[1]?).map openedAt = ((bookSh s.book).trees[1]?).map openedAt
      rw [b5, tree_get, ht₁]
      exact congrArg some (g1.trans e₁.symm)
    · rw [hp₇] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[82]?).map openedAt = ((bookSh s.book).trees[82]?).map openedAt
      rw [b6, tree_get, ht₈]
      exact congrArg some (g2.trans e₂.symm)
    · rw [hp₈] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[82]?).map openedAt = ((bookSh s.book).trees[82]?).map openedAt
      rw [b6, tree_get, ht₈]
      exact congrArg some (g2.trans e₂.symm)
    · rw [hplω] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[83]?).map openedAt = ((bookSh s.book).trees[83]?).map openedAt
      rw [b7, tree_get, htω]
      exact congrArg some g3
  · intro o ho q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    have hq' : s.book.place[o]? = some q := by
      rw [← place_get]
      exact hq
    have e₁ : sharesAt (stSh s.st) (treeSh Ti) = true :=
      sharesAt_single _ _ 4 (orcSh y₄) (by show Ti.parts.toList = [4]; rw [pTi]) ho₄ ea₄
        (Or.inl oTi)
    have e₂ : sharesAt (stSh s.st) (treeSh Tw) = true :=
      sharesAt_pair _ _ 197 198 (orcSh z₇) (orcSh y₈) (by show Tw.parts.toList = [197, 198]; rw [pW])
        ho₇ ho₈ ea₇ ea₈ (by show z₇.groups.length ≤ 1; rw [gz₇]; simp)
    rcases ho with rfl | rfl | rfl | rfl
    · rw [hp₄] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[1]?).map (sharesAt narrowW.st) =
        ((bookSh s.book).trees[1]?).map (sharesAt (stSh s.st))
      rw [b5, tree_get, ht₁]
      exact congrArg some (g4.trans e₁.symm)
    · rw [hp₇] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[82]?).map (sharesAt narrowW.st) =
        ((bookSh s.book).trees[82]?).map (sharesAt (stSh s.st))
      rw [b6, tree_get, ht₈]
      exact congrArg some (g5.trans e₂.symm)
    · rw [hp₈] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[82]?).map (sharesAt narrowW.st) =
        ((bookSh s.book).trees[82]?).map (sharesAt (stSh s.st))
      rw [b6, tree_get, ht₈]
      exact congrArg some (g5.trans e₂.symm)
    · rw [hplω] at hq'
      obtain rfl := Option.some.inj hq'
      show (narrowW.book.trees[83]?).map (sharesAt narrowW.st) =
        ((bookSh s.book).trees[83]?).map (sharesAt (stSh s.st))
      rw [b7, tree_get, htω]
      have e₃ : sharesAt (stSh s.st) (treeSh {
          shape := lay.shapes.getD 0 {}, number := T₃.number, src := T₃.src, parts := #[199] }) =
          true :=
        sharesAt_single _ _ 199 _ rfl ho₉ (by show y₀.shape.answers ≠ 0; rw [ysh]; decide)
          (Or.inl rfl)
      exact congrArg some (g6.trans e₃.symm)
  · show 0 = s.roots
    rw [L.roots, er]
  · exact (hgroup).symm
  · intro G' hG' o ho
    have hG'' : (stSh s.st).groups[s.loc.own]? = some G' := hG'
    rw [hgroup] at hG''
    obtain rfl := Option.some.inj hG''
    have : o ∈ [4, 197, 199] := ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    omega
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    have hownl : s.loc.own = l.own := hown.trans eown
    rcases ho with rfl | rfl | rfl | rfl
    · show (narrowW.st.oracles[4]?).map _ = ((stSh s.st).oracles[4]?).map _
      rw [n1, ho₄]
      have hk := (hF.2 _ _ hG₁).2 4 (by rw [gmem]; simp) y₄ hy₄
      have hc : y₄.groups.contains s.loc.own = true := by
        rw [hownl]
        simpa using hk
      exact congrArg some (by show true = y₄.groups.contains s.loc.own; rw [hc])
    · show (narrowW.st.oracles[197]?).map _ = ((stSh s.st).oracles[197]?).map _
      rw [n2, ho₇]
      have hc : z₇.groups.contains s.loc.own = true := by
        rw [gz₇, hownl]
        simp
      exact congrArg some (by show true = z₇.groups.contains s.loc.own; rw [hc])
    · show (narrowW.st.oracles[198]?).map _ = ((stSh s.st).oracles[198]?).map _
      rw [n3, ho₈]
      have hc : y₈.groups = [] := y₈g
      exact congrArg some (by show false = y₈.groups.contains s.loc.own; rw [hc]; rfl)
    · show (narrowW.st.oracles[199]?).map _ = ((stSh s.st).oracles[199]?).map _
      rw [n4, ho₉]
      have hc : [s₀.loc.own].contains s.loc.own = true := by
        rw [hown]
        simp
      exact congrArg some (by show true = [s₀.loc.own].contains s.loc.own; rw [hc])

/-- **The test frontFiveB says yes on entry to the last chain's own test**, at the written parameters. -/
theorem frontFive_at_own {Cl : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (pI : ProofFile.InstPub)
    {e₁ : S} {d : Desc.K14.St} {r₁ r₀ r₂ u : List Fmt.RoundView} {c₁ c₀ c₂ v : List OpenedColumn}
    (hf₁ : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀))
    (hf₂ : foldBlocks 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₂ pI) r₂ c₂ = .ok (d, u, v)) {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12}
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ pI e₁ d = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) (H2K.JointK.p₁₄N Zp)).decide s₀ rs gs = .ok s)
    (h₂ : enterOwn s = .ok t)
    (hO : ∀ E₂, Desc.K14.ended d = some E₂ → OmegaIs (sharedOfEnd E₂))
    (hT : IndexTreeIs e₁.book) : frontFiveB piWFull codesFull (testSh t) = true := by
  obtain ⟨hc, hm, hp⟩ := sameCore_at_own h pI hf₁ hf₂ hs h₁ h₂ hO hT
  have e : testSh t = ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, .nothing, some 198⟩ := by
    unfold testSh
    rw [hp, hm]
    rfl
  rw [e, ← frontFive_same hc piWFull codesFull early_written (id := 198) (by simp)]
  exact frontFive_narrowW

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.sameCore_at_own
#print axioms ProofFile.Honest.K12.AtFile.frontFive_at_own
#print axioms ProofFile.Honest.K12.AtFile.narrow_msgs
#print axioms ProofFile.Honest.K12.AtFile.narrow_book
#print axioms ProofFile.Honest.K12.AtFile.narrow_guards
#print axioms ProofFile.Honest.K12.AtFile.early_written
