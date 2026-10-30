-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMsgOne.lean: THEOREMS. **GIVEN TWO PREMISES ON THE PLAN (hC · hk, below): AT EVERY RECORD THAT CHAIN 1 OF Key.descriptionFromSource REACHES FROM BORDER 2 ON, MESSAGE 1 (THE LOOKUPS' OWN MESSAGE) HAS THE PLAN's SHAPE, IS SAMPLED, AND ITS ONE SAMPLE ROW IS THE SENDING KIND's ROW AT A SEED (SeedIs); in the program's words: Send.form's row at a
seed, with the answer as its target.** Drawn off the history: no promise bears it.
OBJECT. LPFD.Hist₁ (Key.descriptionFromSource X N P) D · the block msg.1.send at first.blocksInOrder[1] · parMsg X. USER. MemberFacts, clauses (4) | (6), at the one member of the ranges' group at border 15 · the tables' files' member's premise hrec at pin 1. LETTERS. X · N · P · D · j · x; Q : K1.Par; rad.
  held_below       a yes of a held block: every word of its rounds and columns is below the prime (what held_decide drops)
  cut_snd_mem · readsAs_of_yes    a yes of the sending's decision at drawn words below the prime: THE SEEDS READ AS JOINT SEEDS: ∃ ρ, ReadsAs Q r₁ ρ: the decision's own clause «no seed's factor is zero by its words» makes each factor a unit
  seedIs_form      SeedIs, in the program's words: the shape · Send.form … seed 0 = some row0 · the sample rows are [{ row0 with target := tt }] · the seed is long enough · its factor reads as a unit (form_eq)
  shapes_of · size_at₁      book-keeping: the shapes of a place of Key.sendingPar; at border 1 the statement has one message
  msg_seedIs₂      **at border 2: ∃ ρ y, SeedIs codes shape (the statement) 1 ρ y**
  msg_seedIs       **at border 2 + j** (KeyWalkAny.lean's seedIs_later) · member_one: the same in the program's words
THE TWO PREMISES. hC : condPort (parMsg X) rad = true (KeySendCond.lean's cond_msg gives it from a run's yes and meetsB) · hk : the own message's shape counts an answer.
What is not claimed. Which ρ. Anything on the mask that rides with the message (message 2: not sampled). A reading «smp». Nothing on soundness.

-/
import Johnson.RunOne.KeyWalkAny
import Johnson.RunOne.KeySendCond
import Johnson.Desc.K1.Law.FormEq
import Johnson.Desc.K1.Law.GoodSendSize
import Johnson.Desc.K1.Law.GoodSend3
import OnBytes.Maker.OkViewLaws

set_option autoImplicit false

namespace Johnson.RunOne.KeyMsg

open OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps Johnson.RunOne.KeySendGood
open VerifiableInference.Desc (Block noDigest viewWordsBelowPrime roundsFit)
open VerifiableInference.Desc.Sound (held)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Keeps (ebind_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.K1 (Par SeedIs Tie Seeds ReadsAs seedsOf cutSeeds cutSeeds_length decideSend decideSend_iff decideSend_size shapesOf shapeAt sampledAt condPort cond_tie seedIs_behind_len draw_len form_eq SameMsgs)
open LPFD (Reached Hist₁)
open Johnson.Pack (bitsZ)

section General
variable {Q' S Cl : Type}

/-- **A held block's yes: every word is below the prime.** -/
theorem held_below (b : Block S Cl) (a a' : Q' × S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (h : (held b : Block (Q' × S) Cl).decide a rs gs = .ok a') :
    viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true := by
  have h' : ((if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide a.2 rs gs
      else .error "a word is not below the prime").map fun s => (a.1, s)) = .ok a' := h
  by_cases hv : viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true
  · exact hv
  · rw [if_neg hv] at h'
    cases h'

/-- A drawn element of a round of such a view has its words below the prime. -/
theorem okE_of_view {rs : List Fmt.RoundView} {cols : List (ℕ × ℕ × List UInt64)} (h : viewWordsBelowPrime ⟨rs, cols⟩ = true) (r : Fmt.RoundView) (hr : r ∈ rs) (x : UInt64 × UInt64 × UInt64) (hx : x ∈ r.drawn.elems) :
    okE (E.ofTriple x) = true := by
  simp only [viewWordsBelowPrime, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have k := (h.1 r hr).1 x hx
  exact (OnBytes.Maker.okE_ofTriple x).2 ⟨k.1.1, k.1.2, k.2⟩

/-- The factor of a seed that is cut off a list of the right length is an element of the list. -/
theorem cut_snd_mem (v : ℕ) : ∀ (n : ℕ) (l : List E) (sd : List E × E), l.length = n * (v + 1) → sd ∈ cutSeeds v n l → sd.2 ∈ l
  | 0, _, _, _, h => by simp [cutSeeds] at h
  | n + 1, l, sd, hl, h => by
    have hl' : l.length = n * (v + 1) + (v + 1) := by rw [hl, Nat.succ_mul]
    simp only [cutSeeds, List.mem_cons] at h
    rcases h with rfl | h
    · show (l.drop v).headD zeroE ∈ l
      cases hd : l.drop v with
      | nil =>
        have := congrArg List.length hd
        simp only [List.length_drop, List.length_nil] at this
        omega
      | cons a t =>
        exact List.mem_of_mem_drop (hd ▸ List.mem_cons_self : a ∈ l.drop v)
    · exact List.mem_of_mem_drop (cut_snd_mem v n (l.drop (v + 1)) sd (by rw [List.length_drop, hl']; omega) h)

end General

/-- Rounds that fit two declared rounds are two. -/
theorem two_of_fit (d₁ d₂ : Fmt.DeclaredRound) (rs : List Fmt.RoundView) (h : roundsFit [d₁, d₂] rs = true) : ∃ r₁ r₂, rs = [r₁, r₂] := by
  cases rs with
  | nil => simp [roundsFit] at h
  | cons r₁ t =>
    cases t with
    | nil => simp [roundsFit] at h
    | cons r₂ u =>
      cases u with
      | nil => exact ⟨r₁, r₂, rfl⟩
      | cons _ _ => simp [roundsFit] at h

/-- **A yes of the sending's decision, at drawn words below the prime: the seeds read as joint seeds.** -/
theorem readsAs_of_yes {L : Type} (Q : Par) (owed : Option ℕ) (d d' : _root_.Desc.Plain.DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array ℕ) (hyes : decideSend Q owed d [r₁, r₂] = .ok (ids, d'))
    (hlen : (r₁.drawn.elems.map E.ofTriple).length = Q.seeds * (Q.coordinates + 1)) (hok : ∀ x ∈ r₁.drawn.elems, okE (E.ofTriple x) = true) : ∃ ρ : Seeds Q, ReadsAs Q r₁ ρ := by
  obtain ⟨⟨_, _, hz, _, _⟩, _, _⟩ := (decideSend_iff Q owed d d' r₁ r₂ ids).1 hyes
  have hS : (seedsOf Q r₁).length = Q.seeds := cutSeeds_length _ _ _
  have hne : ∀ sd ∈ seedsOf Q r₁, readE sd.2 ≠ 0 := by
    intro sd hsd h0
    obtain ⟨x, hx, e⟩ := List.mem_map.1 (cut_snd_mem _ _ _ sd hlen hsd)
    have hE : okE sd.2 = true := e ▸ hok x hx
    have hzz := (isZeroE_iff sd.2 hE).2 h0
    rw [hz sd hsd] at hzz
    cases hzz
  refine ⟨fun i => (fun t => readL ((seedsOf Q r₁)[i.val]'(by rw [hS]; exact i.isLt)).1 t.val, Units.mk0 (readE ((seedsOf Q r₁)[i.val]'(by rw [hS]; exact i.isLt)).2) (hne _ (List.getElem_mem _))), fun i => ?_⟩
  exact ⟨(seedsOf Q r₁)[i.val]'(by rw [hS]; exact i.isLt), List.getElem?_eq_getElem _, fun _ => rfl, rfl⟩

/-- **SeedIs in the program's words.** -/
theorem seedIs_form {cs : Codes} {s : OracleShape} {St : Statement} {o : ℕ} {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (hT : Tie cs s) (h : SeedIs cs s St o ρ y) :
    ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ), St.oracles[o]? = some x ∧ x.shape = s ∧ Send.form cs s o seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧ bitsZ cs s ≤ seed.z.length ∧ (β : GE) = readE seed.beta := by
  obtain ⟨_, x, z, β, t, hx, hs, _, hr, hread, _⟩ := h
  obtain ⟨row0, h0, h1⟩ := Option.map_eq_some_iff.1 (form_eq cs s o z β 0 t hT.lengths hT.shape hT.fits)
  exact ⟨x, ⟨z, β⟩, row0, t, ρ.2, hx, hs, h0, by rw [hr, ← h1], hread.long, hread.factor.symm⟩

/-- The shapes of a place of Key.sendingPar. -/
theorem shapes_of (one : OneTime) (piece : ℕ) (what : String) (msg : Array OracleNotice) (groups : List (List ℕ)) :
    shapesOf (sendingPar one piece what msg groups) = msg.toList.map (·.shape) := by
  simp [shapesOf, Par.sent, sendingPar]

theorem msgOf_head (x : WfPublic) : ∃ tl, (Wf.messageOf x).toList = x.message :: tl := by
  unfold Wf.messageOf
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- At border 1 the statement has one message. -/
theorem size_at₁ (D : OnBytes.Maker.WholeD) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D 1 x) : (st₁ (show FirstState from x.2)).oracles.size = 1 := by
  obtain ⟨a', b, rs, cols, hr, hb, hd, _⟩ := Reached.last (k := 0) h
  rw [List.getElem?_map] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain rfl : bareOf (sendIndexMasks X.Y.k.oneTime pieces (gIdx X)) = b₀ := Option.some.inj ((idx_at X N P).symm.trans hb₀)
  have hdec := (held_decide _ a' _ _ x hd).2
  have e0 : a'.2 = (descriptionFromSource X N P).start₁ a'.1 := hr
  obtain ⟨m, h1, h2⟩ := ebind_ok hdec
  obtain ⟨ids, d', hd', e1, _⟩ := k1At_sent h1
  obtain ⟨_, _, h2⟩ := bind_ok h2
  have e : st₁ (show FirstState from x.2) = d'.st := by rw [← Except.ok.inj h2]; exact e1
  have hsz := decideSend_size _ _ _ _ _ _ hd'
  rw [shapes_of] at hsz
  have hs0 : (show FirstState from a'.2).d.st.oracles.size = 0 := by
    have := congrArg (fun s : (descriptionFromSource X N P).S₁ => (show FirstState from s).d.st.oracles.size) e0
    exact this
  rw [e, hsz]
  show (show FirstState from a'.2).d.st.oracles.size + _ = 1
  rw [hs0]
  rfl

/-- **At border 2 message 1's sample rows are the sending kind's one row at a seed.** -/
theorem msg_seedIs₂ (rad : ℕ → ℕ) (hC : condPort (parMsg X) rad = true) (hk : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (D : OnBytes.Maker.WholeD)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D 2 x) :
    ∃ ρ y, SeedIs X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape (show FirstState from x.2).d.st 1 ρ y := by
  obtain ⟨a', b, rs, cols, hr, hb, hd, hfit⟩ := Reached.last (k := 1) h
  rw [List.getElem?_map] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain rfl : bareOf (sendOwnMessage X.Y.k.oneTime pieces (gMsg X)) = b₀ := Option.some.inj ((msg_at X N P).symm.trans hb₀)
  have hfit' : roundsFit (VerifiableInference.Desc.K1.rounds (parMsg X)) rs = true := (rounds_msg X) ▸ hfit
  obtain ⟨r₁, r₂, rfl⟩ := two_of_fit _ _ rs hfit'
  have hview := held_below _ a' x _ _ hd
  have hdec := (held_decide _ a' _ _ x hd).2
  obtain ⟨m, h1, h2⟩ := ebind_ok hdec
  obtain ⟨ids, d', hd', e1, _⟩ := k1At_sent h1
  have hyes : decideSend (parMsg X) (show FirstState from a'.2).debt (withLoc (show FirstState from a'.2).d (#[] : Array ℕ)) [noDigest r₁, noDigest r₂] = .ok (ids, d') := hd'
  have hs : SameMsgs d'.st (st₁ (show FirstState from x.2)) := by rw [← e1]; exact wfGroup_same h2
  have hlen : ((noDigest r₁).drawn.elems.map E.ofTriple).length = (parMsg X).seeds * ((parMsg X).coordinates + 1) := draw_len (parMsg X) r₁ r₂ hfit'
  obtain ⟨ρ, hρ⟩ := readsAs_of_yes (parMsg X) _ _ _ _ _ _ hyes hlen (fun y hy => okE_of_view hview (noDigest r₁) (by simp) y hy)
  obtain ⟨tl, htl⟩ := msgOf_head X.Y.k.oneTime.ranges
  have hsh : shapesOf (parMsg X) = X.Y.k.oneTime.ranges.message.shape :: tl.map (·.shape) := by
    unfold parMsg
    rw [shapes_of, htl]
    rfl
  have h0 : 0 < (shapesOf (parMsg X)).length := by rw [hsh]; exact Nat.succ_pos _
  have hat : shapeAt (parMsg X) ⟨0, h0⟩ = X.Y.k.oneTime.ranges.message.shape := by
    show (shapesOf (parMsg X))[0] = _
    simp [hsh]
  have hk' : sampledAt (parMsg X) ⟨0, h0⟩ := by
    show (shapesOf (parMsg X))[0].answers ≠ 0
    have : (shapesOf (parMsg X))[0] = X.Y.k.oneTime.ranges.message.shape := hat
    rw [this]
    exact hk
  obtain ⟨y, hy⟩ := seedIs_behind_len (parMsg X) rad _ _ _ _ _ _ hC hlen hyes ρ hρ ⟨0, h0⟩ hk'
  have h1' : (withLoc (show FirstState from a'.2).d (#[] : Array ℕ)).st.oracles.size + (⟨0, h0⟩ : Fin (shapesOf (parMsg X)).length).val = 1 := size_at₁ D a' hr
  rw [h1'] at hy
  have hall : ∃ ρ y, SeedIs X.Y.k.oneTime.codes (shapeAt (parMsg X) ⟨0, h0⟩) (show FirstState from x.2).d.st 1 ρ y := ⟨_, y, hy.travels hs⟩
  rw [hat] at hall
  exact hall

/-- **At every later border.** -/
theorem msg_seedIs (rad : ℕ → ℕ) (hC : condPort (parMsg X) rad = true) (hk : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) :
    ∃ ρ y, SeedIs X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape (show FirstState from x.2).d.st 1 ρ y := by
  obtain ⟨x0, h0, _, hs⟩ := Johnson.RunOne.KeyWalk.seedIs_later D 2 j x h
  obtain ⟨ρ, y, hy⟩ := msg_seedIs₂ rad hC hk D x0 h0
  exact ⟨ρ, y, hs _ _ _ _ _ hy⟩

/-- The own message's shape and the plan's codes meet the sending kind's Tie. -/
theorem msg_tie (rad : ℕ → ℕ) (hC : condPort (parMsg X) rad = true) (hk : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) : Tie X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape := by
  obtain ⟨tl, htl⟩ := msgOf_head X.Y.k.oneTime.ranges
  have hsh : shapesOf (parMsg X) = X.Y.k.oneTime.ranges.message.shape :: tl.map (·.shape) := by
    unfold parMsg
    rw [shapes_of, htl]
    rfl
  have h0 : 0 < (shapesOf (parMsg X)).length := by rw [hsh]; exact Nat.succ_pos _
  have hat : shapeAt (parMsg X) ⟨0, h0⟩ = X.Y.k.oneTime.ranges.message.shape := by
    show (shapesOf (parMsg X))[0] = _
    simp [hsh]
  have hk' : sampledAt (parMsg X) ⟨0, h0⟩ := by
    show (shapesOf (parMsg X))[0].answers ≠ 0
    have : (shapesOf (parMsg X))[0] = X.Y.k.oneTime.ranges.message.shape := hat
    rw [this]
    exact hk
  have t := cond_tie (parMsg X) rad hC ⟨0, h0⟩ hk'
  rw [hat] at t
  exact t

/-- **The one member of the ranges' group, in the program's words, at every border from 2 on.** -/
theorem member_one (rad : ℕ → ℕ) (hC : condPort (parMsg X) rad = true) (hk : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) :
    ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ), (show FirstState from x.2).d.st.oracles[1]? = some o ∧ o.shape = X.Y.k.oneTime.ranges.message.shape ∧
      Send.form X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape 1 seed 0 = some row0 ∧ o.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape ≤ seed.z.length ∧ (β : GE) = readE seed.beta := by
  obtain ⟨ρ, y, hy⟩ := msg_seedIs rad hC hk D j x h
  exact seedIs_form (msg_tie rad hC hk) hy

end Johnson.RunOne.KeyMsg
