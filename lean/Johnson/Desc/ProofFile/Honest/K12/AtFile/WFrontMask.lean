-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontMask.lean: the message that the first chain's record
names as the mask of the own test's first fold: it is the last message of W's sending, it has that
notice's shape, and it is not spent. So four of the premises of cameB_at_own (WFrontCame.lean) come
from the first chain's fold.

  sendAtS_last     behind a sending the statement's last message has the last notice's shape and is
                   not spent
  maskMessage_at_end   at the end of the first chain's fold

Limits.
- hn: the message at the mask's number is not sampled there. The last chain's start tests this.
- That the notice's numbers are the first stage's is a comparison of plans, not said here.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontCame
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontSamples
import Johnson.Desc.K13.Law.K1Ids
import Johnson.Desc.K13.Honest.OwnLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (sendAtS)
open Johnson.Desc.First.Walk.Tied (fold_split)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- **Behind a sending the last message has the last notice's shape and is not spent.** -/
theorem sendAtS_last {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (s mid : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s rs gs = .ok mid) {n : OracleNotice}
    (hn : P.sent.back? = some n) :
    ∃ x : OnBytes.Oracle, mid.st.oracles[mid.st.oracles.size - 1]? = some x ∧ x.shape = n.shape ∧
      x.spentAsMask = false := by
  obtain ⟨ids, d', h1, e1, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok P s mid rs gs h
  have hr : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, h1 with
    | [r₁, r₂], _ => exact ⟨r₁, r₂, rfl⟩
  obtain ⟨r₁, r₂, rfl⟩ := hr
  obtain ⟨⟨_, _, _, _, hf⟩, _, rfl⟩ := (VerifiableInference.Desc.K1.decideSend_iff P _ _ d' r₁ r₂ ids).1 h1
  have hn' : P.sent[P.sent.size - 1]? = some n := by
    rw [← Array.back?_eq_getElem?]
    exact hn
  have hpos : 0 < P.sent.size := by
    by_contra hc
    have hge : P.sent.size ≤ P.sent.size - 1 := by omega
    rw [Array.getElem?_eq_none hge] at hn'
    cases hn'
  have hlen : (VerifiableInference.Desc.K1.shapesOf P).length = P.sent.size := by
    simp [VerifiableInference.Desc.K1.shapesOf]
  have hk : P.sent.size - 1 < (VerifiableInference.Desc.K1.shapesOf P).length := by
    rw [hlen]
    omega
  obtain ⟨ys', -, hget⟩ := VerifiableInference.Desc.K1.outs_spec P.codes
    (VerifiableInference.Desc.K1.seedsOf P r₁) P.seeds (VerifiableInference.Desc.K1.shapesOf P)
    (VerifiableInference.Desc.K1.stateOf s (#[] : Array ℕ)).st.oracles.size
    (VerifiableInference.Desc.K1.answersIn r₂) hf (P.sent.size - 1) hk
  have hsz : mid.st.oracles.size = (VerifiableInference.Desc.K1.stateOf s (#[] : Array ℕ)).st.oracles.size +
      P.sent.size := by
    rw [e1]
    show (_ ++ VerifiableInference.Desc.K1.outs _ _ _ _ _).toArray.size = _
    rw [List.size_toArray, List.length_append, Array.length_toList,
      VerifiableInference.Desc.K13.Law.outs_length, hlen]
  have hidx : mid.st.oracles.size - 1 =
      (VerifiableInference.Desc.K1.stateOf s (#[] : Array ℕ)).st.oracles.size +
        (P.sent.size - 1) := by omega
  have hshape : (VerifiableInference.Desc.K1.shapesOf P)[P.sent.size - 1] = n.shape := by
    have e : (VerifiableInference.Desc.K1.shapesOf P)[P.sent.size - 1]? = some n.shape := by
      simp only [VerifiableInference.Desc.K1.shapesOf, List.getElem?_map, Array.getElem?_toList, hn',
        Option.map_some]
    exact Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans e)
  refine ⟨VerifiableInference.Desc.K1.wr P.codes (VerifiableInference.Desc.K1.seedsOf P r₁)
    ((VerifiableInference.Desc.K1.stateOf s (#[] : Array ℕ)).st.oracles.size + (P.sent.size - 1))
    (VerifiableInference.Desc.K1.shapesOf P)[P.sent.size - 1] ys', ?_, ?_, ?_⟩
  · rw [hidx, e1]
    show (_ ++ VerifiableInference.Desc.K1.outs _ _ _ _ _).toArray[_]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  · unfold VerifiableInference.Desc.K1.wr
    split <;> exact hshape
  · unfold VerifiableInference.Desc.K1.wr
    split <;> rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The two parts of the block at W's place. -/
theorem atM4_parts (p : VerifiableInference.Desc.K13.Where) (P : VerifiableInference.Desc.K1.Par)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (VerifiableInference.Desc.K13.atM4 p (sendAtS P : Block S Unit)).decide s rs gs = .ok s') :
    ∃ (mid : S) (r₁ r₂ : List Fmt.RoundView) (g₁ g₂ : List (List (ℕ × List UInt64))),
      (sendAtS P : Block S Unit).decide s r₁ g₁ = .ok mid ∧
      (VerifiableInference.Desc.K13.rowsB (Cl := Unit) VerifiableInference.Desc.K13.atS p).decide
        mid r₂ g₂ = .ok s' := by
  have h' : ((sendAtS P : Block S Unit).decide s (rs.take (sendAtS P : Block S Unit).rounds.length)
      (gs.take (sendAtS P : Block S Unit).openings)).bind (fun s₁ =>
      (VerifiableInference.Desc.K13.rowsB (Cl := Unit) VerifiableInference.Desc.K13.atS p).decide s₁
        (rs.drop (sendAtS P : Block S Unit).rounds.length)
        (gs.drop (sendAtS P : Block S Unit).openings)) = .ok s' := h
  obtain ⟨mid, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok h'
  exact ⟨mid, _, _, _, _, h1, h2⟩

/-- **The end of the first chain's fold, taken apart**: W's sending and the text behind it, the last
block handing the record on. -/
theorem atW_of_fold₂ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) :
    ∃ (t mid : S) (msg : Array OracleNotice) (R₁ R₂ : List Fmt.RoundView)
      (G₁ G₂ : List (List (ℕ × List UInt64))) (r₁ : List Fmt.RoundView) (c₁ : List OpenedColumn),
      foldBlocks 0 (cF.blocksInOrder.take 356) (ProofFile.startS Zp pI) rs cols = .ok (t, r₁, c₁) ∧
      linMessageW Zp.first.lin = some msg ∧
      (sendAtS (VerifiableInference.Desc.K1.parW Zp.first
        { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg) : Block S Unit).decide t R₁
        G₁ = .ok mid ∧
      (VerifiableInference.Desc.K13.rowsB (Cl := Unit) VerifiableInference.Desc.K13.atS
        (VerifiableInference.Desc.K13.whereOf Zp)).decide mid R₂ G₂ = .ok e₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  obtain ⟨-, -, -, ⟨b₀, b', w, e1, -, hw, rfl, hla⟩⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 3 b₀ e1
  have q7 := (IM.back_numbers h.scope h.reads O).2
  have hdrop : cF.blocksInOrder.drop 356 = [{ b₀ with planOk := b₀.planOk && b₀.hasNoClaimsAndNothingAfter },
               { cF.last with planOk := cF.last.planOk && cF.last.hasNoClaimsAndNothingAfter }] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_of_length_le (by omega)]
    have a1 : cF.blocksInOrder[356] = { b₀ with planOk := b₀.planOk && b₀.hasNoClaimsAndNothingAfter } :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans q)
    have a2 : cF.blocksInOrder[356 + 1] = { cF.last with planOk := cF.last.planOk && cF.last.hasNoClaimsAndNothingAfter } :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans q7)
    rw [a1, a2]
  rw [← List.take_append_drop 356 cF.blocksInOrder, hdrop] at hf
  obtain ⟨t, r₁, c₁, f1, f2⟩ := fold_split 0 _ _ _ _ _ _ hf
  obtain ⟨s', k, -, hs, f3⟩ := VerifiableInference.Desc.Sound.foldBlocks_cons_ok 0 _ _ _ _ _ _ f2
  obtain ⟨s'', k', -, hs', f4⟩ := VerifiableInference.Desc.Sound.foldBlocks_cons_ok 0 _ _ _ _ _ _ f3
  have e4 : s'' = e₁ := by
    unfold foldBlocks at f4
    exact (Prod.mk.inj (Except.ok.inj f4)).1
  subst e4
  obtain ⟨-, -, -, hd⟩ := VerifiableInference.Desc.step_inv _ _ _ _ _ _ _ hs
  obtain ⟨-, -, -, hd'⟩ := VerifiableInference.Desc.step_inv _ _ _ _ _ _ _ hs'
  have e7 : s'' = s' := by
    obtain ⟨b'', -, rfl, hla'⟩ := IM.seal_seated O
    have hy := ((IM.yes_alone hla' (by simp) s' s'' _ _).1 hd').1
    have key : ∀ (R : List Fmt.RoundView) (G : List (List (ℕ × List UInt64))),
        ((VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true
          (VerifiableInference.Desc.K13.inFrontOf Zp) VerifiableInference.Desc.First.endAsks :
          Block S Unit).retype (Cl' := ProofFile.Cl)).decide s' R G = .ok s'' → s'' = s' :=
      fun R G hh => VerifiableInference.Desc.K13.Law.chainEnd_same (Cl := Unit) 1 5 true
        (VerifiableInference.Desc.K13.inFrontOf Zp) VerifiableInference.Desc.First.endAsks s' s'' R G
        hh
    exact key _ _ hy
  subst e7
  have hy := ((IM.yes_alone hla (by simp) t s'' _ _).1 hd).1
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hw
  have key : ∀ (R : List Fmt.RoundView) (G : List (List (ℕ × List UInt64))),
      ((VerifiableInference.Desc.K13.atM4 (VerifiableInference.Desc.K13.whereOf Zp)
        (sendAtS (VerifiableInference.Desc.K1.parW Zp.first
          { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg)) :
        Block S Unit).retype (Cl' := ProofFile.Cl)).decide t R G = .ok s'' → _ :=
    fun R G hh => atM4_parts _ _ t s'' R G hh
  obtain ⟨mid, R₁, R₂, G₁, G₂, h1, h2⟩ := key _ _ hy
  exact ⟨t, mid, msg, R₁, R₂, G₁, G₂, r₁, c₁, f1, hmsg, h1, h2⟩

/-- The same without the fold. -/
theorem atW_of_fold (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) :
    ∃ (t mid : S) (msg : Array OracleNotice) (R₁ R₂ : List Fmt.RoundView)
      (G₁ G₂ : List (List (ℕ × List UInt64))),
      linMessageW Zp.first.lin = some msg ∧
      (sendAtS (VerifiableInference.Desc.K1.parW Zp.first
        { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg) : Block S Unit).decide t R₁
        G₁ = .ok mid ∧
      (VerifiableInference.Desc.K13.rowsB (Cl := Unit) VerifiableInference.Desc.K13.atS
        (VerifiableInference.Desc.K13.whereOf Zp)).decide mid R₂ G₂ = .ok e₁ := by
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, r₁, c₁, -, hmsg, h1, h2⟩ := atW_of_fold₂ h hf
  exact ⟨t, mid, msg, R₁, R₂, G₁, G₂, hmsg, h1, h2⟩

/-- **The mask's message at the end of the first chain's fold.** -/
theorem maskMessage_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀))
    {l : LinFirst} (hl : VerifiableInference.Desc.K13.Law.linAt e₁ = some l) {id : ℕ}
    (hm : l.mask = some id) (hn : ∀ y : OnBytes.Oracle, e₁.st.oracles[id]? = some y →
      y.sampled = false) :
    ∃ (msg : Array OracleNotice) (n : OracleNotice) (y : OnBytes.Oracle),
      linMessageW Zp.first.lin = some msg ∧ msg.back? = some n ∧
      e₁.st.oracles[id]? = some y ∧ y.shape = n.shape ∧ y.spentAsMask = false := by
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  have hpass : OpenRowsPass e₁.st := by
    have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀) := by
      rw [← hlen, List.take_length]
      exact hf
    exact openRowsPass_reached h 358 0 pI rs cols (e₁, r₀, c₀) hfold
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, hmsg, h1, h2⟩ := atW_of_fold h hf
  have hr : ∃ a b, R₁ = [a, b] := by
    obtain ⟨ids, d', h3, -, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok _ _ _ _ _ h1
    match R₁, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨a, b, rfl⟩ := hr
  obtain ⟨m, hm₁, hsz, hI⟩ := VerifiableInference.Desc.K13.Law.sendAtS_idsLast _ t mid a b G₁ h1
  obtain ⟨m₀, l₀, hm₀, hl₀, hmask⟩ := VerifiableInference.Desc.K13.Law.rowsB_mask h2
  rw [hm₁] at hm₀
  obtain rfl : m = m₀ := by
    injection hm₀
  obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hl)
  obtain ⟨-, e2, e3⟩ := hmask hI
  have hahead : (VerifiableInference.Desc.K13.whereOf Zp).lin.masksAhead = true := by
    cases hc : (VerifiableInference.Desc.K13.whereOf Zp).lin.masksAhead with
    | true => rfl
    | false =>
      rw [e3 hc] at hm
      cases hm
  have eid : id = e₁.st.oracles.size - 1 := Option.some.inj (hm.symm.trans (e2 hahead))
  obtain ⟨m₁, l₁, o, owed, hs₀, -, hrows, es⟩ := VerifiableInference.Desc.K13.Law.rowsB_at h2
  have OL := VerifiableInference.Desc.K13.Honest.rows_ownLaid hrows
  have est : e₁.st = o.2.st := by rw [es]
  have hcnt : e₁.st.oracles.size = mid.st.oracles.size := by
    rw [est]
    exact OL.count
  have hsame : e₁.st.oracles[id]? = mid.st.oracles[id]? := by
    rw [est]
    refine OL.out id fun hM => ?_
    obtain ⟨G, hG, hmem⟩ := OL.own
    obtain ⟨y, hy', hs₁⟩ := hpass.1 _ G (by rw [est]; exact hG) id ((hmem id).2 hM)
    rw [hn y hy'] at hs₁
    cases hs₁
  have hsent : (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg).sent = msg := by
    simp [VerifiableInference.Desc.K1.Par.sent, VerifiableInference.Desc.K1.parW]
  have hpos : 0 < msg.size := by
    simp only [VerifiableInference.Desc.K13.Law.rows_is, VerifiableInference.Desc.K13.Law.bind_ok,
      VerifiableInference.Desc.K13.Law.there_ok] at hrows
    obtain ⟨w', hw', -⟩ := hrows
    have e₁' : m₁ = m := by
      rw [hm₁] at hs₀
      injection hs₀ with e
      exact e.symm
    rw [e₁'] at hw'
    have hlt := (Array.getElem?_eq_some_iff.1 hw').1
    rw [hsz, hsent] at hlt
    exact hlt
  obtain ⟨n, hback⟩ : ∃ n, msg.back? = some n :=
    ⟨msg[msg.size - 1], by
      rw [Array.back?_eq_getElem?]
      exact Array.getElem?_eq_getElem _⟩
  obtain ⟨y, hy1, hy2, hy3⟩ := sendAtS_last _ t mid _ _ h1 (n := n) (by rw [hsent]; exact hback)
  refine ⟨msg, n, y, hmsg, hback, ?_, hy2, hy3⟩
  rw [hsame, eid, hcnt]
  exact hy1

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.sendAtS_last
#print axioms ProofFile.Honest.K12.AtFile.atM4_parts
#print axioms ProofFile.Honest.K12.AtFile.atW_of_fold
#print axioms ProofFile.Honest.K12.AtFile.maskMessage_at_end
