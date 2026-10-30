-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySplitShape.lean: THEOREMS. **THE SHAPES OF THE TWO MESSAGES THAT GO OUT AT 2.5 (o_omega AND THE SPLIT's MASKS o_sp), DRAWN OFF THE HISTORY OF Key.descriptionFromSource's SHARED CHAIN: at every state that the chain reaches from border 6 on, message 2 has the shape S.omega and, where the shape splits,
message 3 the shape S.sharedSplit**, given that the plan lets the kind's eight blocks be made and that one mask goes out with o_u. («State»: what the verifier carries between two blocks.)
OBJECT. LPFD.Hist₂ (Key.descriptionFromSource X N P) D · K14.sendAt at shared.blocksInOrder[5]. USER. The proximity test's files' law at 2.9 | 2.10, which asks of every member of the group that the state's message has the plan's shape. LETTERS. X · N · P · D · j · x; Q := p14At X P; S := Q.S; l: the eight blocks; w: what goes out with o_u.
THE LAYING IS ANOTHER FILE's: send_laid | SendLaid.new (Johnson/Desc/Key/Laid/SendLaid.lean): a yes of the sending's decision: each new message's shape is its notice's. THE CARRY: KeyWalkAny.lean's hist₂_rel at «a statement only grows» (Johnson/Desc/Grows.lean), which keeps EVERY message's shape, sampled or not.
  sendAt_named        a yes of K14.sendAt IS a yes of the sending's decision AT THE STATE IN FRONT, and what the kind notes behind it
  linPoint_same | laysRec_same | loc_same · behindU_st | behindOmega_st      for the count: these steps leave the messages (other files' …_keeps' proofs, at SameMsgs)
  five_blocks         of the eight blocks the first five, by what a yes of each says of the messages
  hist₂_step          one step back on a history, at the bare block
  size₂_at₅           at border 5 the statement has as many messages as went out with o_u
  sent_shape₂         **at border 6 + j: ∀ i n, (K14.withOmega S)[i]? = some n → ∃ o, oracles[w.size + i]? = some o ∧ o.shape = n.shape**
  omega_shape · split_shape      **at numerals: oracles[2]? … S.omega · oracles[3]? … S.sharedSplit** (w.size = 2; the shape splits)
  blocks_some · withU_full · split_full · key_of_scope · omega_shape_scope | split_shape_scope | two_at_scope | groups_apart_scope      **THE FOUR PREMISES PAID IN SCOPE**: from X.chains.made.sized.key = keyFull (key_in_scope, Johnson/RunOne/Law/KeyInScope.lean, with KeyPayD.lean's pubsOf_ok): the eight blocks can be made, two messages go out with o_u, the shape splits: the last two by the kernel
  Two d · two_at · groups_apart      **WHERE THE SHAPE SPLITS THE TWO GROUPS ARE TWO: at every state that the chain reaches at a border from 2 to 9: loc.gOmega = loc.gU + 1 (so ≠) ∧ loc.gOmega < the count of groups**: laid by LIN point's yes at 2.1 (newGroupP hands back the count of groups); the seven blocks 2.2 … 2.8 leave both numbers (other files' …_keeps' proofs once more, at «loc's two numbers stay»)
What is not claimed. Whether the messages are sampled; their sample rows. Nothing where the plan does not let the eight blocks be made. Nothing on soundness.

-/
import Johnson.RunOne.KeyMsgOne
import Johnson.RunOne.KeyCut23
import Johnson.Desc.Key.Laid.SendLaid
import Johnson.RunOne.KeyPayD
import Johnson.RunOne.Law.KeyInScope

set_option autoImplicit false

namespace Johnson.RunOne.KeySplit

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc (Block noDigest roundsFit Grows)
open VerifiableInference.Desc.Sound (held)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Keeps (ebind_ok emap_ok named_ok)
open VerifiableInference.Desc.K1 (SameMsgs decideSend decideSend_size shapesOf)
open _root_.Desc.Plain (obind_ok Par)
open _root_.Desc.K14 (St P14 linPoint laysRec loc behindU behindOmega withU withOmega sendAt parK1)
open Johnson.RunOne.KeyRows23 (p14At seat front₂ shared_at_blocks)
open Johnson.RunOne.KeyMsg (two_of_fit)
open LPFD (Reached Hist₂)

/-- **A yes of K14's sending is a yes of the sending's decision at the state in front.** -/
theorem sendAt_named (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry) (groups : List (List ℕ)) (behind : St → Array ℕ → Option St)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    ∃ ids t, decideSend Q none { st := d.st, book := d.book, roots := d.roots, opened := d.opened, loc := (#[] : Array ℕ) } rs = .ok (ids, t) ∧
      behind { d with st := t.st, book := t.book, roots := t.roots, opened := t.opened } ids = some d' := by
  obtain ⟨t', h2, h3⟩ := ebind_ok h
  obtain ⟨⟨ids, t⟩, hx, e⟩ := emap_ok h2
  subst e
  exact ⟨ids, t, hx, named_ok h3⟩

theorem linPoint_same (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') : SameMsgs d.st d'.st := by
  unfold linPoint at h
  split at h
  · obtain ⟨_, _, h⟩ := obind_ok h
    obtain ⟨⟨gU, d₁⟩, h1, h⟩ := obind_ok h
    dsimp only at h
    split at h
    · obtain ⟨y, h2, h⟩ := obind_ok h
      cases h
      show SameMsgs d.st y.2.st
      exact same_trans (newGroupP_same h1) (newGroupP_same (n := y.1) (d' := y.2) h2)
    · obtain ⟨y, h2, h⟩ := obind_ok h
      cases h2
      cases h
      show SameMsgs d.st d₁.st
      exact newGroupP_same h1
  · cases h

theorem laysRec_same (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') : SameMsgs d.st d'.st := by
  unfold laysRec at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  obtain ⟨rows, _, h⟩ := obind_ok h
  exact same_trans (joinP_same h1) (addRowsP_same h)

theorem loc_same (p : Par) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (h : loc p d rs gs = some d') : SameMsgs d.st d'.st := by
  unfold loc at h
  split at h
  · dsimp only at h
    obtain ⟨rows, _, h⟩ := obind_ok h
    exact addRowsP_same h
  · cases h

theorem behindU_st (p : Par) (d d' : St) (ids : Array ℕ) (h : behindU p d ids = some d') : d'.st = d.st := by
  unfold behindU at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     rfl)

theorem behindOmega_st (p : Par) (d d' : St) (ids : Array ℕ) (h : behindOmega p d ids = some d') : d'.st = d.st := by
  unfold behindOmega at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     rfl)

theorem parK1_sent (P : P14) (piece : ℕ) (part : String) (sent : Array OracleNotice) : (parK1 P piece part sent).sent = sent := by
  simp [VerifiableInference.Desc.K1.Par.sent, parK1]

/-- **Of the eight blocks the first five, by what a yes of each says of the messages.** -/
theorem five_blocks (Q : P14) (l : List (Block St Unit)) (w : Array OracleNotice) (hw : withU Q.S = some w) (h : _root_.Desc.K14.blocks Q = some l) :
    ∃ b₁ b₂ b₃ b₄ b₅ tl, l = b₁ :: b₂ :: b₃ :: b₄ :: b₅ :: tl ∧
      (∀ d rs gs d', b₁.decide d rs gs = .ok d' → d'.st.oracles.size = d.st.oracles.size) ∧
      (∀ d rs gs d', b₂.decide d rs gs = .ok d' → d'.st.oracles.size = d.st.oracles.size + w.size) ∧
      (∀ d rs gs d', b₃.decide d rs gs = .ok d' → d'.st.oracles.size = d.st.oracles.size) ∧
      (∀ d rs gs d', b₄.decide d rs gs = .ok d' → d'.st.oracles.size = d.st.oracles.size) ∧
      (∃ Q₅ : VerifiableInference.Desc.K1.Par, b₅.rounds = VerifiableInference.Desc.K1.rounds Q₅) ∧
      (∀ d r₁ r₂ gs d', b₅.decide d [r₁, r₂] gs = .ok d' → ∀ (i : ℕ) (n : OracleNotice), (withOmega Q.S)[i]? = some n →
        ∃ o : OnBytes.Oracle, d'.st.oracles[d.st.oracles.size + i]? = some o ∧ o.shape = n.shape) := by
  unfold _root_.Desc.K14.blocks at h
  obtain ⟨w', hw', h⟩ := obind_ok h
  obtain rfl : w = w' := Option.some.inj (hw.symm.trans hw')
  cases h
  refine ⟨_, _, _, _, _, _, rfl, ?_, ?_, ?_, ?_, ⟨_, rfl⟩, ?_⟩
  · exact fun d rs _ d' hd => same_size (linPoint_same _ d d' rs (why_ok hd))
  · intro d rs gs d' hd
    obtain ⟨ids, t, hy, hb⟩ := sendAt_named _ _ _ _ _ _ d d' rs gs hd
    rw [behindU_st _ _ _ _ hb]
    have hs := decideSend_size _ _ _ _ _ _ hy
    rw [show (shapesOf (parK1 Q 2 "o_u and the first mask" w)).length = w.size by simp [shapesOf, parK1_sent]] at hs
    exact hs
  · exact fun d rs _ d' hd => same_size (laysRec_same _ d d' rs (why_ok hd))
  · exact fun d rs gs d' hd => same_size (loc_same _ d d' rs gs (why_ok hd))
  · intro d r₁ r₂ gs d' hd i n hn
    obtain ⟨ids, t, hy, hb⟩ := sendAt_named _ _ _ _ _ _ d d' _ gs hd
    rw [behindOmega_st _ _ _ _ hb]
    obtain ⟨o, ho, hsh, _⟩ := (VerifiableInference.Desc.Key.LaidW.send_laid _ _ _ _ _ _ _ hy).new i n (by rw [parK1_sent]; exact hn)
    exact ⟨o, ho, hsh⟩

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- One step back on a history of the shared chain, at the bare block. -/
theorem hist₂_step (D : OnBytes.Maker.WholeD) (k : ℕ) (b₀ : Block (descriptionFromSource X N P).S₂ (descriptionFromSource X N P).Cl) (hb : (descriptionFromSource X N P).shared.blocksInOrder[k]? = some b₀)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (k + 1) x) :
    ∃ (a' : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      Hist₂ (descriptionFromSource X N P) D k a' ∧ b₀.decide a'.2 (rs.map noDigest) gs = .ok x.2 ∧ roundsFit b₀.rounds rs = true := by
  obtain ⟨a', b, rs, cols, hre, hb', hd, hfit⟩ := Reached.last (k := k) h
  rw [List.getElem?_map] at hb'
  obtain ⟨b₁, hb₁, rfl⟩ := Option.map_eq_some_iff.1 hb'
  obtain rfl : b₀ = b₁ := Option.some.inj (hb.symm.trans hb₁)
  exact ⟨a', rs, _, hre, (held_decide _ a' _ _ x hd).2, hfit⟩

/-- **At border 5 the statement has as many messages as went out with o_u.** -/
theorem size₂_at₅ (l : List (Block St Unit)) (w : Array OracleNotice) (hbl : _root_.Desc.K14.blocks (p14At X P) = some l) (hw : withU (p14At X P).S = some w) (D : OnBytes.Maker.WholeD)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D 5 x) : (st₂ (show St from x.2)).oracles.size = w.size := by
  obtain ⟨b₁, b₂, b₃, b₄, b₅, tl, hl, p1, p2, p3, p4, _, _⟩ := five_blocks _ l w hw hbl
  have hf := shared_at_blocks X N P l hbl
  rw [hl] at hf
  obtain ⟨x4, _, _, h4, d4, _⟩ := hist₂_step D 4 (seat b₄) (by rw [hf]; rfl) x h
  obtain ⟨x3, _, _, h3, d3, _⟩ := hist₂_step D 3 (seat b₃) (by rw [hf]; rfl) x4 h4
  obtain ⟨x2, _, _, h2, d2, _⟩ := hist₂_step D 2 (seat b₂) (by rw [hf]; rfl) x3 h3
  obtain ⟨x1, _, _, h1, d1, _⟩ := hist₂_step D 1 (seat b₁) (by rw [hf]; rfl) x2 h2
  obtain ⟨x0, _, _, h0, d0, _⟩ := hist₂_step D 0 (front₂ X) (by rw [hf]; rfl) x1 h1
  have e0 : x0.2 = (descriptionFromSource X N P).start₂ x0.1.1 := (show LPFD.st₂ (descriptionFromSource X N P) D x0 from h0).2
  have s0 : (st₂ (show St from x0.2)).oracles.size = 0 := congrArg (fun s : (descriptionFromSource X N P).S₂ => (st₂ (show St from s)).oracles.size) e0
  have e1 : x1.2 = x0.2 := (Except.ok.inj d0).symm
  have q1 := p1 _ _ _ _ d1
  have q2 := p2 _ _ _ _ d2
  have q3 := p3 _ _ _ _ d3
  have q4 := p4 _ _ _ _ d4
  show (show St from x.2).st.oracles.size = w.size
  rw [q4, q3, q2, q1, e1]
  have : (show St from x0.2).st.oracles.size = 0 := s0
  rw [this, Nat.zero_add]

/-- **The shapes of what goes out at 2.5, at every border from 6 on.** -/
theorem sent_shape₂ (l : List (Block St Unit)) (w : Array OracleNotice) (hbl : _root_.Desc.K14.blocks (p14At X P) = some l) (hw : withU (p14At X P).S = some w) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (6 + j) x) (i : ℕ) (n : OracleNotice) (hn : (withOmega (p14At X P).S)[i]? = some n) :
    ∃ o : OnBytes.Oracle, (st₂ (show St from x.2)).oracles[w.size + i]? = some o ∧ o.shape = n.shape := by
  obtain ⟨x6, h6, _, hg⟩ := Johnson.RunOne.KeyWalk.hist₂_rel VerifiableInference.Desc.Ground.groundKeeps_grows Johnson.RunOne.KeyWalk.begin_grows D 6 j x h
  obtain ⟨b₁, b₂, b₃, b₄, b₅, tl, hl, _, _, _, _, ⟨Q₅, hr⟩, p5⟩ := five_blocks _ l w hw hbl
  have hf := shared_at_blocks X N P l hbl
  rw [hl] at hf
  obtain ⟨x5, rs, gs, h5, d5, hfit⟩ := hist₂_step D 5 (seat b₅) (by rw [hf]; rfl) x6 h6
  have hfit' : roundsFit (VerifiableInference.Desc.K1.rounds Q₅) rs = true := hr ▸ hfit
  obtain ⟨r₁, r₂, rfl⟩ := two_of_fit _ _ rs hfit'
  obtain ⟨o, ho, hsh⟩ := p5 _ _ _ _ _ d5 i n hn
  have hs5 : (show St from x5.2).st.oracles.size = w.size := size₂_at₅ l w hbl hw D x5 h5
  rw [hs5] at ho
  obtain ⟨o', ho', hgo⟩ := hg.2.2 _ o ho
  exact ⟨o', ho', hgo.1.trans hsh⟩

/-- **Message 2 has the shape S.omega.** -/
theorem omega_shape (l : List (Block St Unit)) (w : Array OracleNotice) (hbl : _root_.Desc.K14.blocks (p14At X P) = some l) (hw : withU (p14At X P).S = some w) (h2 : w.size = 2) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (6 + j) x) :
    ∃ o : OnBytes.Oracle, (show St from x.2).st.oracles[2]? = some o ∧ o.shape = (p14At X P).S.omega := by
  have hn : (withOmega (p14At X P).S)[0]? = some ⟨(p14At X P).S.omega, (p14At X P).S.omegaLeafClass⟩ := by
    unfold withOmega linMessageOmega
    split <;> rfl
  have := sent_shape₂ l w hbl hw D j x h 0 _ hn
  rw [h2] at this
  exact this

/-- **Where the shape splits, message 3 has the shape S.sharedSplit.** -/
theorem split_shape (l : List (Block St Unit)) (w : Array OracleNotice) (hbl : _root_.Desc.K14.blocks (p14At X P) = some l) (hw : withU (p14At X P).S = some w) (h2 : w.size = 2)
    (hsp : (p14At X P).S.sharedSplitNeeded = true) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (6 + j) x) :
    ∃ o : OnBytes.Oracle, (show St from x.2).st.oracles[3]? = some o ∧ o.shape = (p14At X P).S.sharedSplit := by
  have hn : (withOmega (p14At X P).S)[1]? = some ⟨(p14At X P).S.sharedSplit, (p14At X P).S.sharedSplitLeafClass⟩ := by
    unfold withOmega linMessageOmega
    rw [if_pos hsp]
    rfl
  have := sent_shape₂ l w hbl hw D j x h 1 _ hn
  rw [h2] at this
  exact this

/-! ## Where the shape splits the two groups are two -/

section Groups
open VerifiableInference.Desc.Ground (newGroupP joinP addRowP addRowsP addRowsFrom takeMaskP)
open _root_.Desc.K14 (joins linZeta split)
variable {L : Type}

theorem newGroupP_loc {d d' : _root_.Desc.Plain.DState L} {a b n : ℕ} (h : newGroupP d a b = some (n, d')) : d'.loc = d.loc ∧ n = d.st.groups.size ∧ d'.st.groups.size = d.st.groups.size + 1 := by
  unfold newGroupP at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, rfl, by simp [VerifiableInference.Desc.Ground.withGroup]⟩
  · cases h

theorem joinP_loc {d d' : _root_.Desc.Plain.DState L} {g o : ℕ} {k : Bool} (h : joinP d g o k = some d') : d'.loc = d.loc := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h

theorem addRowP_loc {d d' : _root_.Desc.Plain.DState L} {g : ℕ} {row : Row} (h : addRowP d g row = some d') : d'.loc = d.loc := by
  unfold addRowP at h
  split at h
  · rw [← Option.some.inj h]
  · cases h

theorem addRowsFrom_loc (g : ℕ) : ∀ (l : List Row) (d d' : _root_.Desc.Plain.DState L), addRowsFrom g l d = some d' → d'.loc = d.loc
  | [], d, d', h => by rw [← Option.some.inj h]
  | row :: l, d, d', h => by
    obtain ⟨d₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (addRowsFrom_loc g l d₁ d' h2).trans (addRowP_loc h1)

theorem addRowsP_loc {d d' : _root_.Desc.Plain.DState L} {g : ℕ} {rows : List Row} (h : addRowsP d g rows = some d') : d'.loc = d.loc := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_loc g rows d d' h
  · cases h

theorem takeMaskP_loc {d d' : _root_.Desc.Plain.DState L} {o n : ℕ} (h : takeMaskP d o = some (n, d')) : d'.loc = d.loc := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨y, _, e⟩ := Option.map_eq_some_iff.1 h
    rw [← (Prod.mk.inj e).2]
  · cases h

end Groups

/-- The two groups' numbers, as the state notes them. -/
def Nums (d : St) : ℕ × ℕ := (d.loc.gU, d.loc.gOmega)

theorem linPoint_two (p : Par) (hsp : p.S.sharedSplitNeeded = true) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') : d'.loc.gOmega = d'.loc.gU + 1 ∧ d'.loc.gOmega < d'.st.groups.size := by
  unfold linPoint at h
  split at h
  · obtain ⟨_, _, h⟩ := obind_ok h
    obtain ⟨⟨gU, d₁⟩, h1, h⟩ := obind_ok h
    dsimp only at h
    rw [if_pos hsp] at h
    obtain ⟨y, h2, h⟩ := obind_ok h
    cases h
    obtain ⟨_, e1, s1⟩ := newGroupP_loc h1
    obtain ⟨_, e2, s2⟩ := newGroupP_loc (n := y.1) (d' := y.2) h2
    refine ⟨?_, ?_⟩
    · show y.1 = gU + 1
      rw [e2, s1, e1]
    · show y.1 < y.2.st.groups.size
      rw [e2, s2]
      exact Nat.lt_succ_self _
  · cases h

theorem behindU_nums (p : Par) (d d' : St) (ids : Array ℕ) (h : behindU p d ids = some d') : Nums d' = Nums d := by
  unfold behindU at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     rfl)

theorem behindOmega_nums (p : Par) (d d' : St) (ids : Array ℕ) (h : behindOmega p d ids = some d') : Nums d' = Nums d := by
  unfold behindOmega at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     rfl)

theorem laysRec_nums (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') : Nums d' = Nums d := by
  unfold laysRec at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  obtain ⟨rows, _, h⟩ := obind_ok h
  unfold Nums
  rw [addRowsP_loc h, joinP_loc h1]

theorem loc_nums (p : Par) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (h : loc p d rs gs = some d') : Nums d' = Nums d := by
  unfold loc at h
  split at h
  · dsimp only at h
    obtain ⟨rows, _, h⟩ := obind_ok h
    unfold Nums
    rw [addRowsP_loc h]
  · cases h

theorem joins_nums (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : _root_.Desc.K14.joins p d rs = some d') : Nums d' = Nums d := by
  unfold _root_.Desc.K14.joins at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  unfold Nums
  split at h
  · obtain ⟨d₂, h2, h⟩ := obind_ok h
    rw [joinP_loc h, joinP_loc h2, joinP_loc h1]
  · cases h
    rw [joinP_loc h1]

theorem linZeta_nums (d d' : St) (rs : List Fmt.RoundView) (h : _root_.Desc.K14.linZeta d rs = some d') : Nums d' = Nums d := by
  unfold _root_.Desc.K14.linZeta at h
  split at h
  · cases h
    rfl
  · cases h

theorem split_nums (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : _root_.Desc.K14.split p d rs = some d') : Nums d' = Nums d := by
  unfold _root_.Desc.K14.split at h
  dsimp only at h
  obtain ⟨row, _, h⟩ := obind_ok h
  unfold Nums
  split at h
  · rw [addRowP_loc h]
  · split at h
    · obtain ⟨mu, _, h⟩ := obind_ok h
      obtain ⟨G, _, h⟩ := obind_ok h
      obtain ⟨_, _, h⟩ := obind_ok h
      obtain ⟨⟨kappa, d₁⟩, h1, h⟩ := obind_ok h
      dsimp only at h
      obtain ⟨d₂, h2, h⟩ := obind_ok h
      rw [addRowP_loc h, addRowP_loc h2, takeMaskP_loc h1]
    · obtain ⟨mu, hm, h⟩ := obind_ok h
      cases hm
  · cases h

/-- **The eight blocks, by what a yes of each says of the two groups' numbers.** -/
theorem eight_nums (Q : P14) (hsp : Q.S.sharedSplitNeeded = true) (l : List (Block St Unit)) (h : _root_.Desc.K14.blocks Q = some l) :
    ∃ b₁ tl, l = b₁ :: tl ∧ tl.length = 7 ∧ (∀ d rs gs d', b₁.decide d rs gs = .ok d' → d'.loc.gOmega = d'.loc.gU + 1 ∧ d'.loc.gOmega < d'.st.groups.size) ∧
      ∀ b ∈ tl, ∀ d rs gs d', b.decide d rs gs = .ok d' → Nums d' = Nums d := by
  unfold _root_.Desc.K14.blocks at h
  obtain ⟨w, _, h⟩ := obind_ok h
  cases h
  refine ⟨_, _, rfl, rfl, fun d rs _ d' hd => linPoint_two _ hsp d d' rs (why_ok hd), fun b hb => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro d rs gs d' hd
    obtain ⟨ids, t, _, hb⟩ := sendAt_named _ _ _ _ _ _ d d' rs gs hd
    have e := behindU_nums _ _ _ _ hb
    exact e
  · exact fun d rs _ d' hd => laysRec_nums _ d d' rs (why_ok hd)
  · exact fun d rs gs d' hd => loc_nums _ d d' rs gs (why_ok hd)
  · intro d rs gs d' hd
    obtain ⟨ids, t, _, hb⟩ := sendAt_named _ _ _ _ _ _ d d' rs gs hd
    have e := behindOmega_nums _ _ _ _ hb
    exact e
  · exact fun d rs _ d' hd => joins_nums _ d d' rs (why_ok hd)
  · exact fun d rs _ d' hd => linZeta_nums d d' rs (why_ok hd)
  · exact fun d rs _ d' hd => split_nums _ d d' rs (why_ok hd)

theorem get_two {α β : Type} (f : α → β) (a : β) (b : α) (tl : List α) (r s : List β) (j : ℕ) (hj : j < tl.length) : (a :: ((b :: tl).map f ++ r ++ s))[2 + j]? = some (f (tl[j]'hj)) := by
  rw [show 2 + j = (j + 1) + 1 by omega]
  simp only [List.map_cons, List.cons_append, List.getElem?_cons_succ, List.append_assoc]
  rw [List.getElem?_append_left (by rw [List.length_map]; exact hj), List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

theorem lt_of_grows {A B : Statement} (g : Grows A B) {q : ℕ} (h : q < A.groups.size) : q < B.groups.size := by
  obtain ⟨G', hG', _⟩ := g.2.1 q _ (Array.getElem?_eq_getElem h)
  rcases Nat.lt_or_ge q B.groups.size with h1 | h1
  · exact h1
  · rw [Array.getElem?_eq_none h1] at hG'
    cases hG'

/-- **Where the shape splits: at every state reached at a border from 2 to 9 the two groups' numbers are neighbours, and G_omega is a group that stands.** -/
theorem two_at (l : List (Block St Unit)) (hbl : _root_.Desc.K14.blocks (p14At X P) = some l) (hsp : (p14At X P).S.sharedSplitNeeded = true) (D : OnBytes.Maker.WholeD) :
    ∀ (j : ℕ), j ≤ 7 → ∀ (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂), Hist₂ (descriptionFromSource X N P) D (2 + j) x →
      (show St from x.2).loc.gOmega = (show St from x.2).loc.gU + 1 ∧ (show St from x.2).loc.gOmega < (show St from x.2).st.groups.size
  | 0, _, x, h => by
    obtain ⟨b₁, tl, hl, _, p1, _⟩ := eight_nums _ hsp l hbl
    have hf := shared_at_blocks X N P l hbl
    rw [hl] at hf
    obtain ⟨x1, _, _, _, d1, _⟩ := hist₂_step D 1 (seat b₁) (by rw [hf]; rfl) x h
    exact p1 _ _ _ _ d1
  | j + 1, hj, x, h => by
    obtain ⟨b₁, tl, hl, h7, _, pt⟩ := eight_nums _ hsp l hbl
    have hf := shared_at_blocks X N P l hbl
    rw [hl] at hf
    have hjl : j < tl.length := by omega
    have hb : (descriptionFromSource X N P).shared.blocksInOrder[2 + j]? = some (seat (tl[j]'hjl)) := by
      rw [hf]
      exact get_two seat _ _ _ _ _ j hjl
    obtain ⟨x', _, _, h', d', _⟩ := hist₂_step D (2 + j) _ hb x h
    have ih := two_at l hbl hsp D j (by omega) x' h'
    have e := pt _ (List.getElem_mem hjl) _ _ _ _ d'
    have e1 : (show St from x.2).loc.gU = (show St from x'.2).loc.gU := congrArg Prod.fst e
    have e2 : (show St from x.2).loc.gOmega = (show St from x'.2).loc.gOmega := congrArg Prod.snd e
    have hg : Grows (st₂ (show St from x'.2)) (st₂ (show St from x.2)) :=
      Johnson.RunOne.KeyWalk.flat_keeps₂' VerifiableInference.Desc.Ground.groundKeeps_grows Johnson.RunOne.KeyWalk.begin_grows _ (List.mem_of_getElem? hb) _ _ _ _ d'
    rw [e1, e2]
    exact ⟨ih.1, lt_of_grows hg ih.2⟩

/-- **So at border 9, in front of the test on G_u, G_omega is another group.** -/
theorem groups_apart (l : List (Block St Unit)) (hbl : _root_.Desc.K14.blocks (p14At X P) = some l) (hsp : (p14At X P).S.sharedSplitNeeded = true) (D : OnBytes.Maker.WholeD)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D 9 x) : (show St from x.2).loc.gOmega ≠ (show St from x.2).loc.gU := by
  have := (two_at l hbl hsp D 7 (Nat.le_refl _) x h).1
  omega

/-! ## The four premises paid in scope -/

open Lk6.AtPlan (keyFull)

/-- Where something goes out with o_u the eight blocks can be made. -/
theorem blocks_some (Q : P14) (w : Array OracleNotice) (hw : withU Q.S = some w) : ∃ l, _root_.Desc.K14.blocks Q = some l := by
  unfold _root_.Desc.K14.blocks
  simp only [hw, bind, Option.bind, pure]
  exact ⟨_, rfl⟩

theorem withU_full : (withU keyFull.once.shape).map (·.size) = some 2 := by decide +kernel
theorem split_full : keyFull.once.shape.sharedSplitNeeded = true := by decide +kernel

/-- In scope the sized key, as the source holds it, is the written value. -/
theorem key_of_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) : X.chains.made.sized.key = keyFull := by
  rw [(Johnson.RunOne.KeyPay.pubsOf_ok hX).1]
  exact Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm

/-- **Message 3 has the split's masks' shape: in scope's spelling.** -/
theorem split_shape_scope (hk : X.chains.made.sized.key = keyFull) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (6 + j) x) :
    ∃ o : OnBytes.Oracle, (show St from x.2).st.oracles[3]? = some o ∧ o.shape = keyFull.once.shape.sharedSplit := by
  have hS : (p14At X P).S = keyFull.once.shape := by
    show X.chains.made.sized.key.once.shape = _
    rw [hk]
  obtain ⟨w, hw, h2⟩ := Option.map_eq_some_iff.1 withU_full
  have hw' : withU (p14At X P).S = some w := by rw [hS]; exact hw
  obtain ⟨l, hbl⟩ := blocks_some _ w hw'
  have r := split_shape l w hbl hw' h2 (by rw [hS]; exact split_full) D j x h
  rw [hS] at r
  exact r

theorem two_at_scope (hk : X.chains.made.sized.key = keyFull) (D : OnBytes.Maker.WholeD) (j : ℕ) (hj : j ≤ 7)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (2 + j) x) :
    (show St from x.2).loc.gOmega = (show St from x.2).loc.gU + 1 ∧ (show St from x.2).loc.gOmega < (show St from x.2).st.groups.size := by
  have hS : (p14At X P).S = keyFull.once.shape := by
    show X.chains.made.sized.key.once.shape = _
    rw [hk]
  obtain ⟨w, hw, _⟩ := Option.map_eq_some_iff.1 withU_full
  obtain ⟨l, hbl⟩ := blocks_some (p14At X P) w (by rw [hS]; exact hw)
  exact two_at l hbl (by rw [hS]; exact split_full) D j hj x h

theorem groups_apart_scope (hk : X.chains.made.sized.key = keyFull) (D : OnBytes.Maker.WholeD)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D 9 x) : (show St from x.2).loc.gOmega ≠ (show St from x.2).loc.gU := by
  have hS : (p14At X P).S = keyFull.once.shape := by
    show X.chains.made.sized.key.once.shape = _
    rw [hk]
  obtain ⟨w, hw, _⟩ := Option.map_eq_some_iff.1 withU_full
  obtain ⟨l, hbl⟩ := blocks_some (p14At X P) w (by rw [hS]; exact hw)
  exact groups_apart l hbl (by rw [hS]; exact split_full) D x h

theorem omega_shape_scope (hk : X.chains.made.sized.key = keyFull) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (6 + j) x) :
    ∃ o : OnBytes.Oracle, (show St from x.2).st.oracles[2]? = some o ∧ o.shape = keyFull.once.shape.omega := by
  have hS : (p14At X P).S = keyFull.once.shape := by
    show X.chains.made.sized.key.once.shape = _
    rw [hk]
  obtain ⟨w, hw, h2⟩ := Option.map_eq_some_iff.1 withU_full
  have hw' : withU (p14At X P).S = some w := by rw [hS]; exact hw
  obtain ⟨l, hbl⟩ := blocks_some _ w hw'
  have r := omega_shape l w hbl hw' h2 D j x h
  rw [hS] at r
  exact r

end Johnson.RunOne.KeySplit
