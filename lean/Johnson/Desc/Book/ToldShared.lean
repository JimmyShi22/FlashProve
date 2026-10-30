-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/ToldShared.lean: WHAT AN IOP AS WRITTEN IN LEAN TELLS OF OMEGA's TREE, READ OFF
THE SHARED CHAIN's OWN MAKE (Johnson/Desc/K14/Blocks.lean: oraclesOf, sendAt, blocks, chainOf), AND
SO THE LAST TABLE's TEST ON THE PLAN AT THE TREE OF OMEGA's COPY ("PlanTreeO",
Johnson/LLT25R/LastTreeO.lean, whose right side is written out here) AT THE NUMBER D.t₁ + 1.
Statements and
proofs. No definition.

Why. "send o_omega" is K14's sendAt, which lays `Desc.K14.oraclesOf P.codes Q.sent groups` over
K1's own field `oracles` (the tenants' groups part). An equation on K1's field, taken as a
premise, would be false at the real make; here the premises are read off that make.

  told_omega14     at Desc.K14.oraclesOf codes (linMessageOmega S) [g0, g1], S lawful, the trees
                   laid: the first oracle message told has ShapeIs against shapeAlone codes S.omega.
  shapes_one_u     the prover's message with o_u (withU S) is laid in ONE tree, with no premise on
                   the shape: the first mask has no main rows and o_u's class of leaves.
  told_u_len       so "send o_u" tells of one tree: Omega's tree is the shared chain's number 1.
  blocks_told, told_chainOf   what the eight sub-protocols, and the shared chain's flat list, tell:
                   o_u's tree, then the trees of the message with Omega, then the rest.
  oracleAt_behind  the index: behind the first chain's told trees and a front part of the shared
                   chain's.
  told_at_shared   G tells of the tree number D.t₁ + 1 an oracle message o, and
                   ShapeIs (shapeAlone P.codes P.S.omega) o.
  planTreeO_at_shared   so the test holds at G, P.codes, P.S, D.t₁ + 1.
  Both FROM: G's data are D · the first chain's sub-protocols pass blocksOk (so they tell of D.t₁
  trees: toldCount) · hsh: G's shared chain tells what chainOf c P ts last tells · withU
  returns · both sendings' trees can be laid · P.S is lawful.
  oraclesOf_retype, first_ok_retype, back_ok_retype, blocksOk_of_planOk, sendAt_can, can_of_back
                   tools by which Johnson/Desc/ProofFile/Law/OmegaTold.lean meets all these premises
                   at the proof file's own description from its data and its planOk.
IS IT EMPTY? See Johnson/Desc/ProofFile/Law/OmegaTold.lean. P IS THE SHARED CHAIN's Desc.K14.P14:
that its codes and shape are the last chain's is an equation of the make, shown there by rfl.
Nothing is evaluated here. ShapeIs has three fields (main, mask, log): of a tree shape's fourth
field, logNzk, nothing is said.
Nothing on soundness.
-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.Sound.ToldCount
import Johnson.Desc.Own.TreesAgree
import Johnson.Desc.K12.Coin.FramesTie
import Johnson.Desc.Book.LayOmega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open OnBytes.Params (LinShape laidOf layPass layStep)
open VerifiableInference.Desc.K12.Coin (ShapeIs)
open _root_.Desc.K14 (P14 St withU withOmega parK1 sendAt blocks blocksOr chainOf frontBlock
  entries behindU behindOmega)

/-- What K14 tells first of the message with Omega. -/
theorem told_omega14 (codes : Codes) (S : LinShape) (g0 g1 : List Nat) (hok : S.ok = true)
    (T : TreeLay) (hT : layTrees codes (linMessageOmega S) = some T) :
    ∃ o : VerifiableInference.Desc.Oracle,
      (_root_.Desc.K14.oraclesOf codes (linMessageOmega S) [g0, g1])[0]? = some o ∧
        ShapeIs (shapeAlone codes S.omega) o := by
  have hM : Own.treesMade codes (linMessageOmega S) = some T := (Own.treesMade_eq _ _).trans hT
  obtain ⟨a0, a1⟩ := tree_omega_at hok hT
  have h0 : T.shapes[0]? = some (shapeAlone codes S.omega) := by
    rw [getElem?_of_getD T.shapes 0 {} (shapes_pos_omega hok hT), lay_omega_alone hok hT]
  have key : (_root_.Desc.K14.oraclesOf codes (linMessageOmega S) [g0, g1])[0]? = some
      { logLength := (shapeAlone codes S.omega).logN
        words := (shapeAlone codes S.omega).mainWidth + (shapeAlone codes S.omega).maskWidth
        tenants := ((((linMessageOmega S).toList.zip [g0, g1]).zipIdx.filter
          fun x => T.tree[x.2]? == some 0).map fun x =>
          { main := x.1.1.shape.mainRows * x.1.1.shape.mainDeg, mask := x.1.1.shape.maskRows * 3
            degree := x.1.1.shape.mainDeg, sampled := x.1.1.shape.answers != 0
            groups := x.1.2 }) } := by
    unfold _root_.Desc.K14.oraclesOf
    rw [hM]
    simp [h0]
  refine ⟨_, key, ⟨?_, ?_, rfl⟩⟩
  · cases hsp : S.sharedSplitNeeded with
    | true => simp [omega_two S hsp, a0, a1 hsp, shapeAlone]
    | false => simp [omega_one S hsp, a0, shapeAlone]
  · cases hsp : S.sharedSplitNeeded with
    | true => simp [omega_two S hsp, a0, a1 hsp, shapeAlone]
    | false => simp [omega_one S hsp, a0, shapeAlone]

/-- Two messages of one class of leaves, the second without main rows: one tree. -/
theorem size_two_same (codes : Codes) (n0 n1 : OracleNotice)
    (h1 : (n1.shape.mainRows == 0) = true) (hc : (n0.leafClass == n1.leafClass) = true) :
    (laidOf codes #[n0, n1]).1.size = 1 := by
  have r2 : List.range 2 = [0, 1] := rfl
  have r1 : List.range 1 = [0] := rfl
  cases h0 : (n0.shape.mainRows == 0) <;> simp [laidOf, layPass, layStep, h0, h1, hc, r2, r1]

/-- One message: one tree. -/
theorem size_one (codes : Codes) (n0 : OracleNotice) : (laidOf codes #[n0]).1.size = 1 := by
  cases h0 : (n0.shape.mainRows == 0) <;> simp [laidOf, layPass, layStep, h0]

/-- **The prover's message with o_u is laid in one tree.** -/
theorem shapes_one_u {codes : Codes} {S : LinShape} {u : Array OracleNotice} {T : TreeLay}
    (hU : withU S = some u) (hT : layTrees codes u = some T) : T.shapes.size = 1 := by
  rw [OnBytes.Params.layTrees_size hT]
  unfold _root_.Desc.K14.withU linWithU at hU
  cases hm : S.masksAhead with
  | false =>
    simp [hm] at hU
    rw [← hU]
    exact size_one codes _
  | true =>
    cases hn : linMaskNotice S.testU S.fold.leafClass with
    | none => simp [hm, hn] at hU
    | some n1 =>
      simp [hm, hn] at hU
      rw [← hU]
      unfold linMaskNotice at hn
      obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 hn
      exact size_two_same codes _ _ rfl (by simp [foldMaskNotice])

/-- So "send o_u" tells of one tree. -/
theorem told_u_len {codes : Codes} {S : LinShape} {u : Array OracleNotice} {T : TreeLay}
    (gs : List (List Nat)) (hU : withU S = some u) (hT : layTrees codes u = some T) :
    (_root_.Desc.K14.oraclesOf codes u gs).length = 1 := by
  have hM : Own.treesMade codes u = some T := (Own.treesMade_eq _ _).trans hT
  unfold _root_.Desc.K14.oraclesOf
  rw [hM]
  simp [shapes_one_u hU hT]

theorem sent_parK1' (P : P14) (i : Nat) (s : String) (sent : Array OracleNotice) :
    (parK1 P i s sent).sent = sent := by
  simp [K1.Par.sent, parK1]

theorem oraclesOf_cons' {S Cl : Type} (b : Block S Cl) (l : List (Block S Cl)) :
    oraclesOf (b :: l) = b.oracles.flatMap id ++ oraclesOf l := by
  simp [oraclesOf]

theorem oraclesOf_append' {S Cl : Type} (l l' : List (Block S Cl)) :
    oraclesOf (l ++ l') = oraclesOf l ++ oraclesOf l' := by
  simp [oraclesOf]

theorem oraclesOf_bare' {S Cl : Type} (l : List (Block S Cl)) :
    oraclesOf (l.map fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) = oraclesOf l := by
  simp [oraclesOf, List.flatMap_map]

/-- What the eight sub-protocols tell. -/
theorem blocks_told {P : P14} {l : List (Block St Unit)} {u : Array OracleNotice}
    (hU : withU P.S = some u) (h : blocks P = some l) :
    oraclesOf l = _root_.Desc.K14.oraclesOf P.codes u [[0], []] ++
      _root_.Desc.K14.oraclesOf P.codes (withOmega P.S) [[1], [1, 0]] := by
  unfold blocks at h
  simp only [hU] at h
  have e := Option.some.inj h
  rw [← e]
  cases P.S.sharedSplitNeeded <;> simp [oraclesOf, sendAt, sent_parK1']

/-- What the shared chain's flat list tells. -/
theorem told_chainOf (c : Model.Verify.Chains) (P : P14) (ts : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) {u : Array OracleNotice}
    (hU : withU P.S = some u) :
    ∃ rest, oraclesOf (chainOf c P ts last).blocksInOrder =
      _root_.Desc.K14.oraclesOf P.codes u [[0], []] ++
        (_root_.Desc.K14.oraclesOf P.codes (withOmega P.S) [[1], [1, 0]] ++ rest) := by
  obtain ⟨l, hl⟩ : ∃ l, blocks P = some l := by
    unfold blocks
    simp only [hU]
    exact ⟨_, rfl⟩
  have hor : blocksOr P = l := by
    unfold blocksOr
    rw [hl]
    rfl
  refine ⟨oraclesOf ts ++ (last (l ++ ts)).oracles.flatMap id, ?_⟩
  unfold chainOf Chain.blocksInOrder
  simp only [hor, List.map_nil, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, oraclesOf_cons', oraclesOf_append', oraclesOf_bare', blocks_told hU hl]
  simp [oraclesOf, frontBlock, roundlessBlock]

/-- The index: behind the first chain's told trees and a front part of the shared chain's. -/
theorem oracleAt_behind {Xi : Type} (G : FileDescription Xi) (t₁ : Nat) (A B R : List Oracle)
    (h1 : (oraclesOf G.first.blocksInOrder).length = t₁) (h2 : oraclesOf G.shared.blocksInOrder = A ++ (B ++ R))
    (o : Oracle) (hB : B[0]? = some o) : G.oracleAt (t₁ + A.length) = some o := by
  unfold FileDescription.oracleAt
  cases B with
  | nil => cases hB
  | cons b B' =>
    obtain rfl : b = o := Option.some.inj hB
    rw [List.append_assoc, List.getElem?_append_right (by omega), h1, Nat.add_sub_cancel_left, h2,
      List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

/-- **What G tells of the tree number D.t₁ + 1.** -/
theorem told_at_shared {Xi : Type} (G : FileDescription Xi) (file : String) (D : Maker.WholeD)
    (c : Model.Verify.Chains) (P : P14) (ts : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) (u : Array OracleNotice) (Tu TO : TreeLay)
    (hD : G.data file = .ok D) (hb : blocksOk G.first.blocksInOrder = true)
    (hsh : oraclesOf G.shared.blocksInOrder = oraclesOf (chainOf c P ts last).blocksInOrder)
    (hU : withU P.S = some u) (hTu : layTrees P.codes u = some Tu)
    (hTO : layTrees P.codes (withOmega P.S) = some TO) (hok : P.S.ok = true) :
    ∃ o, G.oracleAt (D.t₁ + 1) = some o ∧ ShapeIs (shapeAlone P.codes P.S.omega) o := by
  obtain ⟨rest, hr⟩ := told_chainOf c P ts last hU
  obtain ⟨o', ho', h3⟩ := told_omega14 P.codes P.S [1] [1, 0] hok TO hTO
  have hat := oracleAt_behind G D.t₁ _ _ rest ((Sound.toldCount Xi G file D hD).1 hb)
    (hsh.trans hr) o' ho'
  rw [told_u_len _ hU hTu] at hat
  exact ⟨o', hat, h3⟩

/-- **The last table's test on the plan at the tree of Omega's copy, at the number D.t₁ + 1.** -/
theorem planTreeO_at_shared {Xi : Type} (G : FileDescription Xi) (file : String) (D : Maker.WholeD)
    (c : Model.Verify.Chains) (P : P14) (ts : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) (u : Array OracleNotice) (Tu TO : TreeLay)
    (hD : G.data file = .ok D) (hb : blocksOk G.first.blocksInOrder = true)
    (hsh : oraclesOf G.shared.blocksInOrder = oraclesOf (chainOf c P ts last).blocksInOrder)
    (hU : withU P.S = some u) (hTu : layTrees P.codes u = some Tu)
    (hTO : layTrees P.codes (withOmega P.S) = some TO) (hok : P.S.ok = true) :
    ∀ lay, layTrees P.codes #[⟨P.S.omega, P.S.omegaLeafClass⟩] = some lay →
      ∀ o, G.oracleAt (D.t₁ + 1) = some o → ShapeIs (lay.shapes.getD 0 {}) o := by
  intro lay hl o ho
  obtain ⟨o', hat, h3⟩ := told_at_shared G file D c P ts last u Tu TO hD hb hsh hU hTu hTO hok
  obtain rfl : o' = o := Option.some.inj (hat.symm.trans ho)
  rw [lay_single hl]
  exact h3

/-! ## Tools: from a description's planOk to these premises -/

theorem oraclesOf_map_of {S Cl Cl' : Type} (f : Block S Cl → Block S Cl')
    (hf : ∀ b, (f b).oracles = b.oracles) (l : List (Block S Cl)) :
    oraclesOf (l.map f) = oraclesOf l := by
  simp [oraclesOf, List.flatMap_map, hf]

/-- A chain without links, carried to another type of claims, tells the same. -/
theorem oraclesOf_retype {S Cl Cl' : Type} (c : Chain S Cl) (hl : c.links = []) :
    oraclesOf (c.retype : Chain S Cl').blocksInOrder = oraclesOf c.blocksInOrder := by
  unfold Chain.blocksInOrder
  rw [hl]
  simp [Chain.retype, Block.retype, oraclesOf, List.flatMap_map]

/-- The three chains' sub-protocols pass blocksOk. -/
theorem blocksOk_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    blocksOk F.first.blocksInOrder = true ∧ blocksOk F.shared.blocksInOrder = true ∧
      blocksOk F.second.blocksInOrder = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.1.1.2⟩

/-- The first sub-protocol of a carried chain passes its own test on the plan. -/
theorem first_ok_retype {S Cl Cl' : Type} (c : Chain S Cl)
    (h : blocksOk (c.retype : Chain S Cl').blocksInOrder = true) : c.first.planOk = true := by
  unfold blocksOk at h
  have h1 := List.all_eq_true.1 h _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ List.mem_cons_self)))
  simp only [Chain.retype, Block.retype, Bool.and_eq_true] at h1
  exact h1.1.1.1.1

/-- So does every sub-protocol behind the links. -/
theorem back_ok_retype {S Cl Cl' : Type} (c : Chain S Cl)
    (h : blocksOk (c.retype : Chain S Cl').blocksInOrder = true) : ∀ b ∈ c.back, b.planOk = true := by
  intro b hb
  unfold blocksOk at h
  have h1 := List.all_eq_true.1 h _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (List.mem_map_of_mem (f := Block.retype) hb))))
  simp only [Block.retype, Bool.and_eq_true] at h1
  exact h1.1.1.1

/-- A sending's test on the plan holds K1's "the trees can be laid". -/
theorem sendAt_can (P : P14) (n : String) (Q : K1.Par) (f : Option Fmt.Entry)
    (g : List (List Nat)) (b : St → Array Nat → Option St)
    (h : (sendAt P n Q f g b).planOk = true) : Own.treesCan Q.codes Q.sent = true := by
  simp only [sendAt, Block.inside, K1.sendOwn, K1.planOkOwn, K1.planOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

/-- If the eight sub-protocols pass their tests on the plan: withU returns, and both sendings' trees
can be laid. -/
theorem can_of_back (P : P14) (hall : ∀ b ∈ blocksOr P, b.planOk = true) :
    ∃ u Tu TO, withU P.S = some u ∧ layTrees P.codes u = some Tu ∧
      layTrees P.codes (withOmega P.S) = some TO := by
  cases hU : withU P.S with
  | none =>
    have hb : blocksOr P =
        [{ roundlessBlock "the shared chain's rounds cannot be made from the plan" 2 none 1 .ok with
            planOk := false }] := by
      unfold blocksOr blocks
      simp only [hU]
      rfl
    have t := hall _ (by rw [hb]; exact List.mem_singleton.2 rfl)
    cases t
  | some u =>
    obtain ⟨l, hl⟩ : ∃ l, blocks P = some l := by
      unfold blocks
      simp only [hU]
      exact ⟨_, rfl⟩
    have hor : blocksOr P = l := by
      unfold blocksOr
      rw [hl]
      rfl
    have hl' := hl
    unfold blocks at hl'
    simp only [hU] at hl'
    have e := Option.some.inj hl'
    have m1 : l[1]? = some (sendAt P "send o_u" (parK1 P 2 "o_u and the first mask" u)
        (entries P)[0]? [[0], []] (behindU P.par)) := by
      rw [← e]
      rfl
    have m2 : l[4]? = some (sendAt P "send o_omega"
        (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) (entries P)[1]? [[1], [1, 0]]
        (behindOmega P.par)) := by
      rw [← e]
      rfl
    have c1 := sendAt_can _ _ _ _ _ _ (hall _ (by rw [hor]; exact List.mem_of_getElem? m1))
    have c2 := sendAt_can _ _ _ _ _ _ (hall _ (by rw [hor]; exact List.mem_of_getElem? m2))
    rw [sent_parK1', Own.treesCan_eq] at c1 c2
    obtain ⟨Tu, hTu⟩ := Option.isSome_iff_exists.1 c1
    obtain ⟨TO, hTO⟩ := Option.isSome_iff_exists.1 c2
    exact ⟨u, Tu, TO, rfl, hTu, hTO⟩

end VerifiableInference.Desc.Book

#print axioms VerifiableInference.Desc.Book.told_omega14
#print axioms VerifiableInference.Desc.Book.shapes_one_u
#print axioms VerifiableInference.Desc.Book.told_chainOf
#print axioms VerifiableInference.Desc.Book.told_at_shared
#print axioms VerifiableInference.Desc.Book.planTreeO_at_shared
#print axioms VerifiableInference.Desc.Book.oraclesOf_retype
#print axioms VerifiableInference.Desc.Book.blocksOk_of_planOk
#print axioms VerifiableInference.Desc.Book.can_of_back
