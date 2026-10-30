-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SendCounts.lean: HOW MANY ORACLE MESSAGES EACH OF A SEGMENT's THREE
SENDINGS ADDS, IN THE PUBLIC SHAPE's WORDS: segments 1 to 23, in the goals' scope, from the returns
of one fold at the cuts in front of and behind each sending (14 l + 2 | + 3 · + 5 | + 6 · + 7 | +
8). A tool for `ReadFits.own` (Returns/Read.lean; Returns/SeatsWalk.lean has the opened messages as
ranges off the three counts in front). Statements with their proofs: calls.

  `commit_count` ON THE TEXT: behind a yes of kind K1's later sending there are as many messages
                    more as the open segment's frame has messages at its moment
  `step_count` AT THE SEAT: over hearing sub-protocol number 3 or 5 of a segment l < 24, where a
                    segment with the frame f is open in front
  `entry_count` AT THE SEAT: over the code switch of segment l, 1 ≤ l < 24: one carrying message,
                    the kept copies, the own messages of moment 0, one fresh mask. ITS DESCENT TO
                    THE TEXT's YES IS THE LIBRARY's `entry_mask`'s OWN (Johnson/IMR/MaskNamed.lean),
                    retyped
  `counts_link` THE TOP: the three together

By, all the library's: `commitAtS_seated` (Johnson/Desc/K1/Law/SeatedAtRecord.lean) ·
`commitAtS_two` (Johnson/IMR/ListsAtDraw.lean) · `commit_len`, `framesOf_st`
(Johnson/IMR/GroupFill.lean) · `hear_flat`, `hear_commitQ`, `walk_a`, `walk_b`
(Johnson/IMR/FrameAt.lean) · `entry_at` (Johnson/IMR/FrameEntry.lean) · `front_words`, `atMoment_of`
(Johnson/IMR/FlagsAt.lean) · `yes_size` (Johnson/Top/H0/Tw/K2C/StillKeeps.lean) · `link_notices`
(Johnson/Goal/Meaning/K2Share/FrontNotices.lean) · `open_recAll` (Johnson/IMR/ListsEnds.lean) ·
`front_len` (Johnson/IMR/FinPin.lean) · `laid_at` (Johnson/IMR/FrontPin.lean) · `k2_link_sits`,
`Joined.yes` (Johnson/IMR/FirstSeats.lean) · `hear_at_flat` (Johnson/IMR/FlatIx.lean),
`flatIx_scope` (Johnson/IMR/FlatScope.lean) · `head_inv` (Johnson/Top/H0/Tw/K2C/Closed.lean) ·
`andThen_yes`, `fold_next` (Johnson/IMR/FoldTools.lean). Near relatives, not called: over one
sub-protocol "as many messages more as the block declares": `hM_scope` (Johnson/IMR/MsgsScope.lean),
`adds_at_marked` (Johnson/IMR/MsgsPlaces.lean), `k2_adds_of_fence` (Johnson/IMR/MsgsSwitch.lean),
and their sums along a fold (Johnson/IMR/MsgsCut.lean): under premises on what the kinds K1 and K2
tell and the tests on the plan, in the blocks' declared numbers; here no such premise, in the public
shape's words.

Limits. Nothing on segment 0 or segment 24. That a fold returns is shown of no proof here. This
file's imports are heavy. Nothing on any property.



-/
import Johnson.IMR.MaskNamed
import Johnson.IMR.FinPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Model (LinkCtx)
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Meaning.K2 (Opn At laterF commitAtS_two commit_len framesOf_st hear_flat hear_commitQ walk_a
  walk_b entry_at front_words atMoment_of open_recAll front_len laid_at andThen_yes fold_next
  msgsAt)
open ProofFile (Cl)

/-- **On the text: kind K1's later sending.** -/
theorem commit_count {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s v : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v)
    {L : LinkCtx} (hL : s.link? = some L) :
    v.st.oracles.size =
      s.st.oracles.size + (L.check.frame.atMoment L.check.frame.moment).length := by
  obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two h
  have hsz := (K1.commitAtS_seated Q link moment arrays s v r₁ r₂ gs h).msgs
  have hlen := commit_len h hL
  have hk : Q.sent.size = (L.check.frame.atMoment L.check.frame.moment).length := by
    simpa [K1.idsOf, K1.flagsAt] using hlen
  rw [hsz, hk]

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the seat: over a later sending's sub-protocol.** -/
theorem step_count (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 3 ∨ j = 5) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q'))
    {f : ReqFrame} (H : Opn l f s) :
    s'.st.oracles.size = s.st.oracles.size + (f.atMoment f.moment).length := by
  obtain ⟨Lk, eL, hA⟩ := hear_flat hS hR O h24
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  obtain ⟨Q, lk, mo, ar, v, rs2, gs2, cm, qv⟩ := hear_commitQ hS hR O h24 hj eL e d'
  obtain ⟨L, hL, e1, -⟩ := H
  rw [qv.1.1, commit_count cm hL, e1]

/-- **At the seat: over the code switch.** -/
theorem entry_count (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₀ R₁ : List Fmt.RoundView}
    {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    t₁.st.oracles.size = t₀.st.oracles.size +
      (1 + (First.K2.targetAt Z.first.shape l).kept.size + (msgsAt Z.first.shape l 0 + 1)) := by
  obtain ⟨hB, hlk0⟩ := laid_at hS hR O (by omega : l < 25) f₀
  obtain ⟨Lk, b, x0, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O l h1 h24
  have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
    have k := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
      (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y1' : x0.decide t₀ rs' gs' = .ok m := y1
  have st1 : t₁.st = m.st := framesOf_st hfs fr (List.mem_of_getElem? hf) m t₁ y3
  rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
  · obtain ⟨er, he⟩ := hm t₀ rs' gs'
    rw [he] at y1'
    cases y1'
  · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
    · cases hn
    · rw [ex] at y1'
      obtain ⟨w, a1, -⟩ := andThen_yes (n := x0.name) y1'
      obtain ⟨r₁, r₂, a, G', w', roots, -, H⟩ :=
        First.K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
      unfold S.atBetween at hB
      rw [H.hHere] at hB
      cases hB
    · rw [ex] at y1'
      have h' : First.K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x0.name .link n) t₀
          rs' gs' = .ok m := y1'
      obtain ⟨x, hF, e1, -, e2, -⟩ := First.K2.yes_size h'
      have hxf : _root_.Tw.K2.firstFront t₀.st t₀.check.frame = .ok x := by
        rcases hF with ⟨-, a⟩ | ⟨a, -⟩ | ⟨a, -⟩
        · exact a
        · cases a
        · cases a
      have Rr := open_recAll hS hR O (by omega : 2 ≤ 14 * l + 2)
        (by rw [front_len hS hR O]; omega) f₀
      obtain ⟨n1, n2, -⟩ := First.K2.link_notices hxf Rr.walk hlk0
      have hs : (_root_.Tw.K2.switchNotices x.T x.others).size =
          1 + (First.K2.targetAt Z.first.shape l).kept.size + (msgsAt Z.first.shape l 0 + 1) := by
        rw [n1, n2]
        simp [_root_.Tw.K2.switchNotices, First.K2.othersAt, msgsAt, ReqFrame.notices]
        omega
      rw [st1, e2, e1, hs]

/-- **The three sendings of a segment, 1 ≤ l < 24.** -/
theorem counts_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₀ R₁ R₃ R₄ R₅ R₆ : List Fmt.RoundView}
    {C C₀ C₁ C₃ C₄ C₅ C₆ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ t₃ t₄ t₅ t₆ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (f₄ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 6)) (ProofFile.startS Z p) R C = .ok (t₄, R₄, C₄))
    (f₅ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 7)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅))
    (f₆ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8)) (ProofFile.startS Z p) R C = .ok (t₆, R₆, C₆)) :
    t₁.st.oracles.size = t₀.st.oracles.size +
        (1 + (First.K2.targetAt Z.first.shape l).kept.size + (msgsAt Z.first.shape l 0 + 1)) ∧
      t₄.st.oracles.size = t₃.st.oracles.size + msgsAt Z.first.shape l 1 ∧
      t₆.st.oracles.size = t₅.st.oracles.size + msgsAt Z.first.shape l 2 := by
  obtain ⟨x, f, hx, a1, a2, mo, lk, hg, -, sh, -, -⟩ := entry_at hS hR O h1 h24 f₀ f₁
  obtain ⟨-, -, es⟩ := front_words hS hR O h24 f₀ hx
  have s1 : f.shape = Z.first.shape := sh.trans es
  obtain ⟨b1, -⟩ := walk_a hS hR O h24 f₁ a1 a2 2 (by omega) t₃ R₃ C₃ f₃
  obtain ⟨b2, -⟩ := walk_b hS hR O h24 f₁ f₃ hg a1 a2 1 (by omega) t₅ R₅ C₅ f₅
  refine ⟨entry_count hS hR O h1 h24 f₀ f₁, ?_, ?_⟩
  · rw [step_count hS hR O h24 (j := 3) (Or.inl rfl) f₃ f₄ b1.link, mo, atMoment_of s1 lk]
    rfl
  · rw [step_count hS hR O h24 (j := 5) (Or.inr rfl) f₅ f₆ b2.link]
    have m2 : (laterF f t₃.st.oracles.size).moment = 2 := by
      show f.moment + 1 = 2
      rw [mo]
    rw [m2, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk]
    rfl

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.commit_count
#print axioms VerifiableInference.Desc.K2.Honest.Returns.step_count
#print axioms VerifiableInference.Desc.K2.Honest.Returns.entry_count
#print axioms VerifiableInference.Desc.K2.Honest.Returns.counts_link
