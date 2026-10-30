-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/OpenIs.lean: WHAT STANDS OPEN BEHIND A SEGMENT's OPENING, TO THE LETTER: in the goals' scope,
at each of the 25 segments of the first chain: behind every accepting decision of the sub-protocol that opens the segment, the
open book-keeping is the fresh one with the segment's record's table of names and list of arrays, and the open ledger is laid
off the record's arrays, with every weight on a column at 0.

  `OpenedOf X L G`   X: the segment's record. L is the book-keeping that has X's table of names and list, and every other field
                     but the walk's state and the number at its first value; G is `emptySlots (weightsAtZero F₀) n` at a ledger
                     F₀ with X's arrays
  `of_laid`, `headOpen_is`, `yesGives_is`   the three steps "opened"; the head's opening; a code switch's yes in its three forms
  **`opened_is`**     THE STATEMENT, at the sub-protocol number `k2Number l` of the flat list

How. The case split is that of `opened_at` (Honest/K9/OpenFresh.lean), which reads four facts off the same letters; here the
letters themselves are handed on, for whoever wants another fact.

Limits. In the goals' scope, at the hash function `secondHashFunction`. It shows of no state that it is reached. This file proves no
property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.OpenFresh
import Johnson.Desc.ProofFile.Honest.K9.BuiltAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (k2_link_kept)
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero)
open Meaning.K2
open ProofFile (Cl)

/-- **What stands open behind the opening of the segment with the record X.** -/
def OpenedOf (X : LinkH) (L : LinkCtx) (G : Fork) : Prop :=
  (∃ ck m, L = { check := ck, link := m, arrayOf := X.arrayOf, list := X.Tp }) ∧
    ∃ F₀ n, F₀.trees = X.Fp.trees ∧ G = emptySlots (weightsAtZero F₀) n

/-- What is laid to the letter, read. -/
theorem of_laid {t : S} {X : LinkH} {Y : LinkPub} (eY : Y = Johnson.Desc.First.Walk.Seat.pubOf X)
    {ck : ChainCheck} {l n : ℕ}
    (h5 : t.link? = some { check := ck, link := l, arrayOf := Y.arrayOf, list := Y.Tp })
    (h6 : t.fork? = some (startFork Y n)) {L : LinkCtx} {F : Fork} (hL : t.link? = some L)
    (hF : t.fork? = some F) : OpenedOf X L F := by
  subst eY
  obtain rfl := Option.some.inj (h5.symm.trans hL)
  obtain rfl := Option.some.inj (h6.symm.trans hF)
  exact ⟨⟨ck, l, rfl⟩, X.Fp, n, rfl, rfl⟩

/-- **The head's opening.** -/
theorem headOpen_is {HP : K2.HeadPar} {X : LinkH} (e1 : HP.X.arrayOf = X.arrayOf) (e2 : HP.X.Tp = X.Tp)
    (e3 : HP.X.Fp = X.Fp) {m t : S} (h : K2.headOpenQ HP m = .ok t)
    {L : LinkCtx} {F : Fork} (hL : t.link? = some L) (hF : t.fork? = some F) : OpenedOf X L F := by
  obtain ⟨a2, st, f, mine, L0, out, y, cov, s₁, b, q⟩ := (K2.headOpenQ_iff HP m t).1 h
  obtain ⟨-, ⟨b', hb', ho⟩, -⟩ := K2.headOpenOpens HP m t h
  obtain ⟨-, -, hL0, -⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L0
      F := emptySlots (weightsAtZero { trees := HP.X.Fp.trees }) HP.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have g1 : t.link? = some b'.L := by
    unfold S.link?
    rw [hb']
    simp only [ho, if_true]
  have g2 : t.fork? = some b'.F := by
    unfold S.fork?
    rw [hb']
    simp only [ho, if_true]
  obtain rfl := Option.some.inj (g1.symm.trans hL)
  obtain rfl := Option.some.inj (g2.symm.trans hF)
  rw [hb2]
  show OpenedOf X L0 (emptySlots (weightsAtZero { trees := HP.X.Fp.trees }) HP.hp.ns)
  rw [hL0, e1, e2, e3]
  exact ⟨⟨_, _, rfl⟩, { trees := X.Fp.trees }, _, rfl, rfl⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **What a yes of a code switch at a segment gives**, in each of its three forms. -/
theorem yesGives_is (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} {X : LinkH}
    (hX : Z.p.built.links[l]? = some X) {a : Place} (ha : a.link = some l) {nm : String} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (h : P1K2.YesGives Z Bs.G₀ a nm s t rs gs)
    {L : LinkCtx} {G : Fork} (hL : t.link? = some L) (hG : t.fork? = some G) : OpenedOf X L G := by
  obtain ⟨Q, n, -, -, h⟩ := h
  rcases h with ⟨hn, -⟩ | ⟨l', HP, m, rs', gs', hh, hl', hP, -, hd, ho⟩ | ⟨l', -, hb, hd⟩
  · rw [ha] at hn
    cases hn
  · obtain rfl : l = l' := Option.some.inj (ha.symm.trans hl')
    unfold P1K2.pureLetters at hP
    obtain ⟨X', hX', rfl⟩ := Option.map_eq_some_iff.1 hP
    obtain ⟨b, hb, p1, p2, p3⟩ := ground_record O hX'
    obtain rfl : X = b := Option.some.inj (hX.symm.trans hb)
    exact headOpen_is p3.symm p2.symm p1.symm ho hL hG
  · exfalso
    rw [k2_link_kept hd] at hL
    unfold S.link? at hL
    rw [hb] at hL
    cases hL

/-- **BEHIND THE SUB-PROTOCOL THAT OPENS SEGMENT l.** -/
theorem opened_is (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {X : LinkH}
    (hX : Z.p.built.links[l]? = some X) {b : Block S Cl} (hb : c.blocksInOrder[k2Number l]? = some b) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (d : b.decide s rs gs = .ok t)
    {L : LinkCtx} {G : Fork} (hL : t.link? = some L) (hG : t.fork? = some G) : OpenedOf X L G := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, b₀, x, e1, e2, -, hla, hi⟩ := IM.k2_head_of hS hR O
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
    have hb' : c.blocksInOrder[14 * 24 + 1 + 2]? = some b := hb
    obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb')
    exact yesGives_is O hX rfl (P1K2.yes_alone_gives hla (by decide) hi d).1 hL hG
  · by_cases h0 : l = 0
    · subst h0
      obtain ⟨Lk, b₀, e1, e2, L', hL', b', hb', ep, hJ⟩ :=
        IM.first_sits hS hR O 0 (by omega) KindName.K1 rfl
      have hf := IM.hear_at_flat e1 e2
      rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
      have hb₂ : c.blocksInOrder[14 * 0 + 0 + 2]? = some b := hb
      obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb₂)
      obtain ⟨Y, hY, hu⟩ := HashBuild.joined_under hS hR O ⟨L', hL', hb'⟩ ep hJ
      obtain ⟨v, a1, a2⟩ := andThen_yes (hu.2 s rs gs t d)
      have a2' : Johnson.Desc.First.Walk.openLayZero Y
          (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol v = .ok t := a2
      obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLayZero_ok a2'
      obtain ⟨X0, hX0, eX⟩ := zeroAt_pub hY
      obtain rfl : X0 = X := Option.some.inj (hX0.symm.trans hX)
      exact of_laid eX h5 h6 hL hG
    · obtain ⟨Lk, b₀, x, e1, e2, -, hJ, hi⟩ := IM.k2_link_sits hS hR O l (by omega) (by omega)
      have hf := IM.hear_at_flat e1 e2
      rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
      have hb' : c.blocksInOrder[14 * l + 0 + 2]? = some b := by
        unfold k2Number at hb
        rwa [if_neg h24] at hb
      obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb')
      obtain ⟨fs, f, m, rs', gs', hfs, hf', hY, -, ho, -, -⟩ := P1K2.yes_joined_gives hJ hi d
      rcases IM.frames_arms hfs l f hf' with ⟨X', -, -, rfl⟩ | ⟨e0, -⟩ | ⟨Q, nLin, hQ, -, eo, -⟩ |
        ⟨Q, hQ, -, eo, -⟩
      · obtain rfl : m = t := Except.ok.inj ho
        exact yesGives_is O hX rfl hY hL hG
      · exact absurd e0 h0
      · rw [eo] at ho
        obtain ⟨_, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openAtt_ok ho
        obtain ⟨X0, hX0, eX⟩ := frameAt_pub hQ
        obtain rfl : X0 = X := Option.some.inj (hX0.symm.trans hX)
        exact of_laid (show Q.X = Johnson.Desc.First.Walk.Seat.pubOf X0 from eX) h5 h6 hL hG
      · rw [eo] at ho
        obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLay_ok ho
        obtain ⟨X0, hX0, eX⟩ := frameAt_pub hQ
        obtain rfl : X0 = X := Option.some.inj (hX0.symm.trans hX)
        exact of_laid (show Q.X = Johnson.Desc.First.Walk.Seat.pubOf X0 from eX) h5 h6 hL hG

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.of_laid
#print axioms ProofFile.Honest.K9.headOpen_is
#print axioms ProofFile.Honest.K9.yesGives_is
#print axioms ProofFile.Honest.K9.opened_is
