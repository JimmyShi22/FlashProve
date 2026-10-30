-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/RecRun.lean: AT THE PROOF FILE's SEAT: RecAll (Johnson/Goal/Meaning/RecAll.lean), at the plan's
own codes and shape, holds of the first chain's first record and of every record that the fold over
the description's blocks passes through in front of the blocks behind the last link.

  pub_start: the plain road's public part (Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean: pureRoad.pub) holds, as the
    state in front of the first link, what S.startP returns at the plan's codes, shape and layout.
  recAll_startS: so RecAll Z.first.codes Z.first.shape (startS Z p), WHERE THE REQUEST PASSES
    reqOk.
  not_recAll_blank: else startS is the marked blank record, of which RecAll is false.
  descPure_recAll: onlineDescription o pol lay KL = .ok F → F is fileDescBy … c; c.blocksInOrder = frontOf c ++
    backOf c;
    and for every instance x that passes the description's own tests on the instance (okBy, the
    first conjunct of F.okStart), every cut frontOf c = l₁ ++ l₂ and every fold over l₁ from
    startS Z x.pub that returns: RecAll at the record that it returns.
  reqOk_of_covered, stFromCall_req, held_ok, okBy_reqOk: okBy o mk Z x = true → the request passes
    reqOk: so the blank arm is not met behind a yes of these tests.
  descPure_run: THE JOIN TO THE DECISION: where F.run x v₁ v₂ v₃ = true (Johnson/Desc/Block.lean),
    for every cut frontOf c = l₁ ++ l₂ the first chain's own fold, from its own first record over
    its own view, passes through a record t behind l₁, and RecAll holds of t: by the library's
    FileDescription.run_ok (Johnson/Desc/RunLaws.lean), chainAt_fold and foldBlocks_split. AND BY PLACE: at
    l₁ := c.blocksInOrder.take (flatIx c l i) (Johnson/IMR/FlatIx.lean: hear_at_flat), the record in front of
      block
    number i in front of the batching of link number l (flatIx_le: that cut lies in frontOf c).
UNDER K2Share (Johnson/IMR/RecSeat.lean) at all codes and shapes.
NOT SAID: at the place behind the last link, the finish's code switch, kind K2's text takes its
target from the finish's own copy of a group (FinOwn.G), which its quiet step in front lays: RecAll
speaks of the codes and of the copies of the frame: of that copy of a group it says nothing.
OBJECT: ProofFile.onlineDescription's value, its first chain's flat list, ProofFile.startS.
-/
import Johnson.IMR.RecSeat
import Johnson.Goal.Meaning.RecWalk
import Johnson.Desc.First.Look.K3Point
import Johnson.Desc.RunLaws
import Johnson.IMR.FlatIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Decides)
open ProofFile (Pub)

theorem pub_start {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {Z : Pub} (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    S.startP Z.P Z.first.codes Z.first.shape Z.first.layout = some Z.s₀ := by
  have h' : ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z := h
  unfold ProofFile.pubBy at h'
  obtain ⟨m, -, h'⟩ := bindE h'
  dsimp only at h'
  split at h'
  · cases h'
  · obtain ⟨_, -, h'⟩ := bindE h'
    obtain ⟨D, -, h'⟩ := bindE h'
    obtain ⟨told, -, h'⟩ := bindE h'
    obtain ⟨depth, -, h'⟩ := bindE h'
    obtain ⟨cuts, -, h'⟩ := bindE h'
    obtain ⟨s₀, hs, h'⟩ := bindE h'
    cases h'
    unfold ProofFile.orSay at hs
    cases e : ProofFile.plainStarts.start (ProofFile.plainStarts.par m.p.chains.proof.first)
        m.p.chains.proof.first with
    | none => rw [e] at hs; cases hs
    | some s =>
      rw [e] at hs
      cases hs
      exact e

/-- **The first chain's first record**, where the request passes the tests that read no reply. -/
theorem recAll_startS {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {p : ProofFile.InstPub}
    (hq : (Z.s₀.withReq (Verify.words32 p.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) :
    RecAll Z.first.codes Z.first.shape (ProofFile.startS Z p) := by
  unfold ProofFile.startS
  dsimp only
  rw [if_pos hq]
  exact recAll_withReq (recAll_first (pub_start h)) _

/-! ## A yes of the tests on the instance: the request passes reqOk -/

theorem reqOk_of_covered {so : Head.StOwn} {T V : Nat} {cov : Head.Covered}
    (h : Head.coveredOf so T V = .ok cov) (s : S) : (s.withReq so.req).reqOk T V = true := by
  have nd : ∀ {b : Bool} {n : String} {u : Unit}, Head.needed b n = .ok u → b = true := by
    intro b n u k
    unfold Head.needed at k
    split at k
    · assumption
    · cases k
  unfold Head.coveredOf at h
  obtain ⟨_, -, h⟩ := bindE h
  obtain ⟨_, h2, h⟩ := bindE h
  dsimp only at h
  obtain ⟨_, h3, h⟩ := bindE h
  obtain ⟨_, h4, -⟩ := bindE h
  have e2 := nd h2
  have e3 := nd h3
  have e4 := nd h4
  have hT : so.req.size - 2 = T := by
    have := eq_of_beq e2
    omega
  unfold S.reqOk S.tokv S.rowR S.rowE S.reqT S.withReq
  simp only [hT]
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨e2, e3⟩, e4⟩

theorem stFromCall_req {P Q : Array UInt32} {T : Nat} {so : Head.StOwn}
    (h : Head.stFromCall P Q T = .ok so) : so.req = P := by
  unfold Head.stFromCall at h
  obtain ⟨_, -, h⟩ := bindE h
  obtain ⟨_, -, h⟩ := bindE h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bindE h
  cases h
  rfl

theorem held_ok {α : Type} {w : String} {y : Except String α} {a : α}
    (h : ProofFile.held w y = .ok a) : y = .ok a := by
  cases y with
  | error e => cases h
  | ok v =>
    have h' : (Except.ok v : Except (String × String) α) = .ok a := h
    cases h'
    rfl

/-- **Where the description's tests on the instance say yes, the request passes reqOk.** -/
theorem okBy_reqOk {o : ProofFile.SecondHashFunctionArgument}
    {mk : ProofFile.LinksBy} {Z : Pub} {x : ProofFile.Inst} (h : ProofFile.okBy o mk Z x = true) :
    (Z.s₀.withReq (Verify.words32 x.pub.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true := by
  unfold ProofFile.okBy at h
  cases hG : ProofFile.holdBy o mk Z x with
  | error e => rw [hG] at h; cases h
  | ok G =>
    unfold ProofFile.holdBy at hG
    dsimp only at hG
    obtain ⟨_, -, hG⟩ := K3.ebind_ok hG
    obtain ⟨so, h1, hG⟩ := K3.ebind_ok hG
    obtain ⟨cov, h2, -⟩ := K3.ebind_ok hG
    have e := reqOk_of_covered (held_ok h2) Z.s₀
    rw [stFromCall_req (held_ok h1)] at e
    exact e

/-- The other arm: of the marked blank record RecAll is false, at all codes and shapes. -/
theorem not_recAll_blank {cs : Codes} {sh : Params.ReqShape} : ¬ RecAll cs sh S.blank := by
  intro R
  have h1 : (default : Codes) = cs := R.codes
  have h2 : (default : Params.ReqShape) = sh := R.walk.shape
  subst h1 h2
  exact absurd R.ok (by decide)

/-- The statement below, with one clause more: the driver lays nothing between the first block and
the first link. -/
theorem descPure_core (H : ∀ cs sh, K2Share cs sh) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.front = [] ∧
      ∀ (x : ProofFile.Inst), ProofFile.okBy o ProofFile.pureRoad.links Z x = true →
        ∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : Cols) (r : S × List Fmt.RoundView × Cols),
          foldBlocks ft l₁ (ProofFile.startS Z x.pub) rs cols = .ok r →
          RecAll Z.first.codes Z.first.shape r.1 := by
  obtain ⟨Z, hZ, -⟩ := ProofFile.Law.descPure_made h
  obtain ⟨Z', A, B, c, hZ', e, k0, k⟩ := descPure_front (H Z.first.codes Z.first.shape) h
  obtain rfl : Z = Z' := Except.ok.inj (hZ.symm.trans hZ')
  refine ⟨Z, A, B, c, hZ, e, k0, fun x hx l₁ l₂ hl ft rs cols r hf => ?_⟩
  exact recAll_fold (fun b hb => k b (hl ▸ List.mem_append_left _ hb)) hf
    (recAll_startS hZ (okBy_reqOk hx))

/-- **AT THE PROOF FILE's SEAT: RecAll at every record in front of the blocks behind the last
link.** -/
theorem descPure_recAll (H : ∀ cs sh, K2Share cs sh) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (x : ProofFile.Inst), ProofFile.okBy o ProofFile.pureRoad.links Z x = true →
        ∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : Cols) (r : S × List Fmt.RoundView × Cols),
          foldBlocks ft l₁ (ProofFile.startS Z x.pub) rs cols = .ok r →
          RecAll Z.first.codes Z.first.shape r.1 := by
  obtain ⟨Z, A, B, c, h1, h2, k0, k⟩ := descPure_core H h
  exact ⟨Z, A, B, c, h1, h2, flat_eq k0, k⟩

/-- A block in front of a link's batching stands inside frontOf c. -/
theorem flatIx_le {T Cl : Type} {c : Chain T Cl} (h0 : c.front = []) {l i : Nat} {Lk : Link T Cl}
    {b : Block T Cl} (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b) :
    IM.flatIx c l i ≤ (frontOf c).length := by
  obtain ⟨hl, e⟩ := List.getElem?_eq_some_iff.1 h1
  have hs : c.links = c.links.take l ++ Lk :: c.links.drop (l + 1) := by
    rw [← e, ← List.drop_eq_getElem_cons hl, List.take_append_drop]
  have hi : i < Lk.hear.length := (List.getElem?_eq_some_iff.1 h2).1
  have hLk : 1 + i < Lk.blocksInOrder.length := by
    unfold Link.blocksInOrder
    simp only [List.length_append, List.length_cons]
    omega
  have hlen : (c.links.flatMap Link.blocksInOrder).length =
      ((c.links.take l).flatMap Link.blocksInOrder).length +
        (Lk.blocksInOrder.length + ((c.links.drop (l + 1)).flatMap Link.blocksInOrder).length) := by
    conv_lhs => rw [hs]
    rw [List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
  unfold IM.flatIx frontOf
  rw [h0, List.length_cons, List.length_nil, hlen]
  omega

/-- **A yes of the file's decision: RecAll at every record that the first chain's fold passes
through in front of the blocks behind the last link**: at every cut of frontOf c; and, by place, at
the record in front of block number i in front of the batching of link number l. -/
theorem descPure_run (H : ∀ cs sh, K2Share cs sh) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst}
    {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      (∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∃ (t e : S) (rs : List Fmt.RoundView) (cols : Cols),
          foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
            .ok (t, rs, cols) ∧
          foldBlocks 0 (l₂ ++ backOf c) t rs cols = .ok (e, [], []) ∧
          RecAll Z.first.codes Z.first.shape t) ∧
      ∀ (l i : Nat) (Lk : Link S ProofFile.Cl) (b : Block S ProofFile.Cl), c.links[l]? = some Lk →
        Lk.hear[i]? = some b →
        ∃ (t e : S) (rs : List Fmt.RoundView) (cols : Cols),
          foldBlocks 0 (c.blocksInOrder.take (IM.flatIx c l i)) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
            (withEmptySealRound v₁).opened = .ok (t, rs, cols) ∧
          foldBlocks 0 (b :: c.blocksInOrder.drop (IM.flatIx c l i + 1)) t rs cols = .ok (e, [], []) ∧
          RecAll Z.first.codes Z.first.shape t := by
  obtain ⟨Z, A, B, c, hZ, rfl, k0, k⟩ := descPure_core H h
  have hflat := flat_eq k0
  obtain ⟨e₁, -, -, -, ho, -, -, -, j₁, -⟩ := (FileDescription.run_ok _ x v₁ v₂ v₃).1 hr
  have hok : ProofFile.okBy o ProofFile.pureRoad.links Z x = true := by
    have ho' : (ProofFile.okBy o ProofFile.pureRoad.links Z x && A.okInst x.pub) = true := ho
    exact (Bool.and_eq_true _ _ ▸ ho').1
  have j : chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ := j₁
  have f := Keeps.chainAt_fold _ _ _ _ _ _ j
  have cut : ∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
      ∃ (t e : S) (rs : List Fmt.RoundView) (cols : Cols),
        foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
          .ok (t, rs, cols) ∧
        foldBlocks 0 (l₂ ++ backOf c) t rs cols = .ok (e, [], []) ∧
        RecAll Z.first.codes Z.first.shape t := by
    intro l₁ l₂ hl
    have f' := f
    rw [hflat, hl, List.append_assoc] at f'
    obtain ⟨t, rs, cols, f1, f2⟩ := Keeps.foldBlocks_split 0 _ _ _ _ _ _ f'
    exact ⟨t, e₁, rs, cols, f1, f2, k x hok l₁ l₂ hl 0 _ _ _ f1⟩
  refine ⟨Z, A, B, c, hZ, rfl, hflat, cut, fun l i Lk b h1 h2 => ?_⟩
  have hn := flatIx_le k0 h1 h2
  have e1 : c.blocksInOrder.take (IM.flatIx c l i) = (frontOf c).take (IM.flatIx c l i) := by
    rw [hflat, List.take_append_of_le_length hn]
  have e2 : (frontOf c).drop (IM.flatIx c l i) ++ backOf c =
      b :: c.blocksInOrder.drop (IM.flatIx c l i + 1) := by
    obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.1 (IM.hear_at_flat h1 h2)
    rw [← e, ← List.drop_eq_getElem_cons hlt]
    conv_rhs => rw [hflat]
    rw [List.drop_append_of_le_length hn]
  obtain ⟨t, e, rs, cols, f1, f2, R⟩ := cut _ _ (List.take_append_drop (IM.flatIx c l i) _).symm
  exact ⟨t, e, rs, cols, e1 ▸ f1, e2 ▸ f2, R⟩

#print axioms pub_start
#print axioms recAll_startS
#print axioms okBy_reqOk
#print axioms not_recAll_blank
#print axioms descPure_recAll
#print axioms descPure_run

end Meaning.K2
