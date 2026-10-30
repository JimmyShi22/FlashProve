-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMsgAll.lean: THEOREMS. **THE SENDING KIND's ROW AT A SEED (SeedIs), DRAWN OFF THE HISTORY, AT ALL THREE SENDINGS OF Key.descriptionFromSource's CHAIN 1, GIVEN THE LAW's CONDITION ON THE PLAN (condPort) AND THAT THE MESSAGE IS SAMPLED**: behind idx.1.send message 0; behind w.1.send
W's message; at every later border of the same history; and W's across the seam into chain 3. (msg.1.send's message 1: KeyMsgOne.lean.)
OBJECT. LPFD.Hist₁ | Hist₃ (Key.descriptionFromSource X N P) D · the blocks at first.blocksInOrder[0] and at w_at's index · parIdx X · parW X msg. USER. The tables' files' member's premise hrec (SeedIs cs sh a.2.d.st o ρ y), through another file's join. LETTERS. X · N · P · D · m · j · k · x · x0; Q : K1.Par; rad.
  Named Q b          a yes of b at two rounds IS a yes of the sending's decision AT THE RECORD IN FRONT (d := withLoc s.d #[]), and behind it the messages are as the decision leaves them: IsSend with its d named: that gives the message's NUMBER
  idx_named · w_named     the two blocks are so (KeySendIs.lean's proofs, kept one step longer)
  send_seedIs        **GENERAL IN THE PLACE: Named Q b₀ · b₀ at blocksInOrder[m] · its rounds are K1's · condPort · sampledAt Q k: Hist₁ (m + 1) x → ∃ x0, Hist₁ m x0 ∧ x0.1 = x.1 ∧ ∃ ρ y, SeedIs Q.codes (shapeAt Q k) x.2.d.st (x0.2.d.st.oracles.size + k) ρ y**
  idx_seedIs         **message 0 at every border ≥ 1**
  w_seedIs · w_seedIs_into₃    **W's message at every border behind w.1.send, and at every record of chain 3**: ITS NUMBER IS «how many messages stand at the border in front of w.1.send, on the same history» (+ k): NO NUMERAL: at a free X that count hangs on the ranges' test's stages
  idx_seedIs_at · msg_seedIs_at     the same at codes and a shape given by name
  seedIs_reads       **SeedIs in the program's words, WITH ITS ρ AND y KEPT**: KeyMsgOne.lean's seedIs_form threw away how the seed, the factor and the target READ: here: ReadsOne cs s seed.z seed.beta ρ (long · readL seed.z t = ρ.1 t · readE seed.beta = ρ.2) · readP (bitsZ cs s) seed.z = ρ.1 · readE tt = y: the food of a reading's half
  member_one_reads   message 1 so, ρ and y named outside the facts
  cond_idx_plan | cond_msg_plan · idx_seedIs_scope | msg_seedIs_scope | member_one_scope     **THE TWO PREMISES PAID, SCOPE's EQUATIONS AS PREMISES**: from planOk and X.Y.k.oneTime.codes = keyFull.codes · .ranges = keyFull.ranges.x (· .indexMasks = keyFull.once.input): condPort at the planner's radii (KeySendFull.lean's asks_msg | asks_idx; the lengths and «sampled» by the kernel)
What is not claimed. Which ρ. W's number as a numeral. W's two premises (condPort at parW · sampledAt) are NOT paid here (KeySendCond.lean's cond_w gives the first from a run's yes and meetsB; KeySendFull.lean's asks_w meetsB under scope's equations); idx's and msg's are: the …_plan | …_scope laws. Nothing on soundness.

-/
import Johnson.RunOne.KeyMsgOne
import Johnson.RunOne.KeySendFull

set_option autoImplicit false

namespace Johnson.RunOne.KeyMsg

open OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps Johnson.RunOne.KeySendGood
open VerifiableInference.Desc (Block noDigest viewWordsBelowPrime roundsFit)
open VerifiableInference.Desc.Sound (held)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Keeps (ebind_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K1 (Par SeedIs Tie Seeds ReadsAs decideSend shapesOf shapeAt sampledAt condPort seedIs_behind_len draw_len SameMsgs)
open LPFD (Reached Hist₁ Hist₃)
open Johnson.Pack (bitsZ)

/-- A yes of the block at two rounds is a yes of the sending's decision at the record in front. -/
def Named (Q : Par) (b : Block FirstState Claim) : Prop :=
  ∀ (s s' : FirstState) (r₁ r₂ : Fmt.RoundView) (gs : List (List (ℕ × List UInt64))), b.decide s [r₁, r₂] gs = .ok s' →
    ∃ ids d', decideSend Q s.debt (withLoc s.d (#[] : Array ℕ)) [r₁, r₂] = .ok (ids, d') ∧ SameMsgs d'.st (st₁ s')

theorem idx_named (one : OneTime) (N : Pieces) (groups : List (List ℕ)) : Named (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) (bareOf (sendIndexMasks one N groups)) := by
  intro s s' r₁ r₂ gs h
  obtain ⟨m, h1, h2⟩ := ebind_ok h
  obtain ⟨ids, d', hd, e1, _⟩ := k1At_sent h1
  obtain ⟨_, _, h2⟩ := bind_ok h2
  have e : st₁ s' = d'.st := by rw [← Except.ok.inj h2]; exact e1
  exact ⟨ids, d', hd, by rw [e]; exact same_refl _⟩

theorem w_named {one : OneTime} {N : Pieces} {sent : ℕ} {groups : List (List ℕ)} {bw : Block FirstState Claim} {msg : Array OracleNotice} (hm : linMessageW one.lin = some msg)
    (hb : sendW one N sent groups = some bw) : Named (sendingPar one N.w "W and what rides with it" msg groups) (bareOf bw) := by
  unfold sendW at hb
  rw [hm] at hb
  have hb' := Option.some.inj hb
  subst hb'
  intro s s' r₁ r₂ gs h
  obtain ⟨m₃, h₃, hr⟩ := ebind_ok h
  obtain ⟨m₂, h₂, hq₂⟩ := ebind_ok h₃
  obtain ⟨m₁, hq₁, hk⟩ := ebind_ok h₂
  obtain ⟨_, _, hq₁⟩ := bind_ok hq₁
  obtain rfl : s = m₁ := Except.ok.inj hq₁
  obtain ⟨ids, d', hd, e1, _⟩ := k1At_sent hk
  have e₃ := Except.ok.inj hq₂
  obtain ⟨p, hp, hr⟩ := bind_ok hr
  obtain ⟨l, _, hr⟩ := bind_ok hr
  obtain ⟨o, ho, hr⟩ := bind_ok hr
  have hpd : p.d.st = st₁ m₃ := lens_lensSt.get _ _ (VerifiableInference.Desc.K13.part_ok hp)
  have hs' : st₁ s' = o.2.st := by rw [← Except.ok.inj hr]; rfl
  refine ⟨ids, d', hd, ?_⟩
  rw [hs', ← e1]
  have : st₁ m₃ = m₂.d.st := by rw [← e₃]; rfl
  rw [← this, ← hpd]
  exact rows13_same ho

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **Behind a sending of chain 1, general in the place.** -/
theorem send_seedIs (Q : Par) (rad : ℕ → ℕ) (hC : condPort Q rad = true) (b₀ : Block FirstState Claim) (m : ℕ) (hb : (descriptionFromSource X N P).first.blocksInOrder[m]? = some b₀)
    (hr : b₀.rounds = VerifiableInference.Desc.K1.rounds Q) (hS : Named Q b₀) (k : Fin (shapesOf Q).length) (hk : sampledAt Q k) (D : OnBytes.Maker.WholeD)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + 1) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧
      ∃ ρ y, SeedIs Q.codes (shapeAt Q k) (show FirstState from x.2).d.st ((show FirstState from x0.2).d.st.oracles.size + k.val) ρ y := by
  obtain ⟨a', b, rs, cols, hre, hb', hd, hfit⟩ := Reached.last (k := m) h
  rw [List.getElem?_map] at hb'
  obtain ⟨b₁, hb₁, rfl⟩ := Option.map_eq_some_iff.1 hb'
  obtain rfl : b₀ = b₁ := Option.some.inj (hb.symm.trans hb₁)
  have hfit' : roundsFit (VerifiableInference.Desc.K1.rounds Q) rs = true := hr ▸ hfit
  obtain ⟨r₁, r₂, rfl⟩ := two_of_fit _ _ rs hfit'
  have hview := held_below _ a' x _ _ hd
  have hh := held_decide _ a' _ _ x hd
  obtain ⟨ids, d', hyes, hs⟩ := hS _ _ _ _ _ hh.2
  have hlen : ((noDigest r₁).drawn.elems.map E.ofTriple).length = Q.seeds * (Q.coordinates + 1) := draw_len Q r₁ r₂ hfit'
  obtain ⟨ρ, hρ⟩ := readsAs_of_yes Q _ _ _ _ _ _ hyes hlen (fun y hy => okE_of_view hview (noDigest r₁) (by simp) y hy)
  obtain ⟨y, hy⟩ := seedIs_behind_len Q rad _ _ _ _ _ _ hC hlen hyes ρ hρ k hk
  exact ⟨a', hre, hh.1.symm, _, y, hy.travels hs⟩

/-- **Message 0 at every border from 1 on.** -/
theorem idx_seedIs (rad : ℕ → ℕ) (hC : condPort (parIdx X) rad = true) (hk : X.Y.k.oneTime.indexMasks.shape.answers ≠ 0) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (1 + j) x) :
    ∃ ρ y, SeedIs X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape (show FirstState from x.2).d.st 0 ρ y := by
  obtain ⟨x1, h1, _, hs⟩ := Johnson.RunOne.KeyWalk.seedIs_later D 1 j x h
  have hsh : shapesOf (parIdx X) = [X.Y.k.oneTime.indexMasks.shape] := by
    unfold parIdx
    rw [shapes_of]
    rfl
  have h0 : 0 < (shapesOf (parIdx X)).length := by rw [hsh]; exact Nat.succ_pos _
  have hat : shapeAt (parIdx X) ⟨0, h0⟩ = X.Y.k.oneTime.indexMasks.shape := by
    show (shapesOf (parIdx X))[0] = _
    simp [hsh]
  have hk' : sampledAt (parIdx X) ⟨0, h0⟩ := by
    show (shapesOf (parIdx X))[0].answers ≠ 0
    have : (shapesOf (parIdx X))[0] = X.Y.k.oneTime.indexMasks.shape := hat
    rw [this]
    exact hk
  obtain ⟨x0, hx0, _, hall⟩ := send_seedIs (parIdx X) rad hC _ 0 (idx_at X N P) (rounds_idx X) (idx_named _ _ _) ⟨0, h0⟩ hk' D x1 (by rw [Nat.zero_add]; exact h1)
  have e0 : x0.2 = (descriptionFromSource X N P).start₁ x0.1 := hx0
  have hs0 : (show FirstState from x0.2).d.st.oracles.size = 0 := congrArg (fun s : (descriptionFromSource X N P).S₁ => (show FirstState from s).d.st.oracles.size) e0
  rw [hs0, hat] at hall
  obtain ⟨ρ, y, hy⟩ := hall
  exact ⟨ρ, y, hs _ _ _ _ _ hy⟩

/-- The index of w.1.send in the flat list (KeySendAtDesc.lean's w_at). -/
def bW (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) : ℕ := (descriptionFromSource X N P).first.front.length + ((descriptionFromSource X N P).first.links.flatMap VerifiableInference.Desc.Link.blocksInOrder).length + 3 + 1

/-- **W's message at every border behind w.1.send.** -/
theorem w_seedIs {bw : Block FirstState Claim} {msg : Array OracleNotice} (hb : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw)
    (hm : linMessageW X.Y.k.oneTime.lin = some msg) (rad : ℕ → ℕ) (hC : condPort (parW X msg) rad = true) (k : Fin (shapesOf (parW X msg)).length) (hk : sampledAt (parW X msg) k)
    (D : OnBytes.Maker.WholeD) (j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (bW X N P + 1 + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D (bW X N P) x0 ∧ x0.1 = x.1 ∧
      ∃ ρ y, SeedIs X.Y.k.oneTime.codes (shapeAt (parW X msg) k) (show FirstState from x.2).d.st ((show FirstState from x0.2).d.st.oracles.size + k.val) ρ y := by
  obtain ⟨x1, h1, e1, hs⟩ := Johnson.RunOne.KeyWalk.seedIs_later D (bW X N P + 1) j x h
  obtain ⟨x0, hx0, e0, ρ, y, hy⟩ := send_seedIs (parW X msg) rad hC _ (bW X N P) (w_at X N P hb) (rounds_w hm hb) (w_named hm hb) k hk D x1 h1
  exact ⟨x0, hx0, e0.trans e1, ρ, y, hs _ _ _ _ _ hy⟩

/-- **… and at every record that chain 3 reaches.** -/
theorem w_seedIs_into₃ {bw : Block FirstState Claim} {msg : Array OracleNotice} (hb : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw)
    (hm : linMessageW X.Y.k.oneTime.lin = some msg) (rad : ℕ → ℕ) (hC : condPort (parW X msg) rad = true) (k : Fin (shapesOf (parW X msg)).length) (hk : sampledAt (parW X msg) k)
    (D : OnBytes.Maker.WholeD) (j : ℕ) (hj : bW X N P + 1 + j = (descriptionFromSource X N P).first.blocksInOrder.length) (n : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D n a) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D (bW X N P) x0 ∧ x0.1 = a.1.1 ∧
      ∃ ρ y, SeedIs X.Y.k.oneTime.codes (shapeAt (parW X msg) k) (show S₃ from a.2).st ((show FirstState from x0.2).d.st.oracles.size + k.val) ρ y := by
  obtain ⟨x1, h1, e1, hs⟩ := Johnson.RunOne.KeyWalk.seedIs_into D (bW X N P + 1) j hj n a h
  obtain ⟨x0, hx0, e0, ρ, y, hy⟩ := send_seedIs (parW X msg) rad hC _ (bW X N P) (w_at X N P hb) (rounds_w hm hb) (w_named hm hb) k hk D x1 h1
  exact ⟨x0, hx0, e0.trans e1, ρ, y, hs _ _ _ _ _ hy⟩

/-- At codes and a shape given by name. -/
theorem idx_seedIs_at {cs : Codes} {sh : OracleShape} (hc : X.Y.k.oneTime.codes = cs) (hs : X.Y.k.oneTime.indexMasks.shape = sh) (rad : ℕ → ℕ) (hC : condPort (parIdx X) rad = true) (hk : sh.answers ≠ 0)
    (D : OnBytes.Maker.WholeD) (j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (1 + j) x) : ∃ ρ y, SeedIs cs sh (show FirstState from x.2).d.st 0 ρ y := by
  subst hc hs
  exact idx_seedIs rad hC hk D j x h

theorem msg_seedIs_at {cs : Codes} {sh : OracleShape} (hc : X.Y.k.oneTime.codes = cs) (hs : X.Y.k.oneTime.ranges.message.shape = sh) (rad : ℕ → ℕ) (hC : condPort (parMsg X) rad = true) (hk : sh.answers ≠ 0)
    (D : OnBytes.Maker.WholeD) (j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) : ∃ ρ y, SeedIs cs sh (show FirstState from x.2).d.st 1 ρ y := by
  subst hc hs
  exact msg_seedIs rad hC hk D j x h

/-- **SeedIs in the program's words, with its ρ and y kept.** -/
theorem seedIs_reads {cs : Codes} {s : OracleShape} {St : Statement} {o : ℕ} {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (hT : Tie cs s) (h : SeedIs cs s St o ρ y) :
    ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E), St.oracles[o]? = some x ∧ x.shape = s ∧ x.sampled = true ∧ Send.form cs s o seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧ VerifiableInference.Desc.K1.ReadsOne cs s seed.z seed.beta ρ ∧ readP (bitsZ cs s) seed.z = ρ.1 ∧ readE tt = y := by
  obtain ⟨_, x, z, β, t, hx, hs, hsm, hr, hread, hy⟩ := h
  obtain ⟨row0, h0, h1⟩ := Option.map_eq_some_iff.1 (VerifiableInference.Desc.K1.form_eq cs s o z β 0 t hT.lengths hT.shape hT.fits)
  exact ⟨x, ⟨z, β⟩, row0, t, hx, hs, hsm, h0, by rw [hr, ← h1], hread, funext fun u => hread.point u, hy⟩

/-- **Message 1 so, at every border from 2 on.** -/
theorem member_one_reads (rad : ℕ → ℕ) (hC : condPort (parMsg X) rad = true) (hk : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) :
    ∃ (ρ : (Fin (bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) → GE) × GEˣ) (y : GE),
      SeedIs X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape (show FirstState from x.2).d.st 1 ρ y ∧
      ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E), (show FirstState from x.2).d.st.oracles[1]? = some o ∧ o.shape = X.Y.k.oneTime.ranges.message.shape ∧ o.sampled = true ∧
        Send.form X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape 1 seed 0 = some row0 ∧ o.sampleRows.toList = [{ row0 with target := tt }] ∧
        VerifiableInference.Desc.K1.ReadsOne X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape seed.z seed.beta ρ ∧
        readP (bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) seed.z = ρ.1 ∧ readE tt = y := by
  obtain ⟨ρ, y, hy⟩ := msg_seedIs rad hC hk D j x h
  exact ⟨ρ, y, hy, seedIs_reads (msg_tie rad hC hk) hy⟩

/-! ## The two premises paid, scope's equations as premises -/

open Lk6.AtPlan (keyFull)

theorem lengths_full : keyFull.codes.lengthsOk = true := by decide +kernel
theorem msg_sampled_full : keyFull.ranges.x.message.shape.answers ≠ 0 := by decide +kernel
theorem idx_sampled_full : keyFull.once.input.shape.answers ≠ 0 := by decide +kernel

theorem cond_msg_plan (hp : (descriptionFromSource X N P).planOk = true) (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) : condPort (parMsg X) (fun _ => 3131959) = true :=
  cond_of _ _ (pays_bare _ st₁ _ (msg_pays _ _ _) ((((descriptionFromSource X N P).planOk_ok).1 hp).blocks₁ _ (List.mem_of_getElem? (msg_at X N P))).1).plan
    (show X.Y.k.oneTime.codes.lengthsOk = true from hc ▸ lengths_full) (asks_msg hc hr).meets

theorem cond_idx_plan (hp : (descriptionFromSource X N P).planOk = true) (hc : X.Y.k.oneTime.codes = keyFull.codes) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) : condPort (parIdx X) (fun _ => 6130) = true :=
  cond_of _ _ (pays_bare _ st₁ _ (idx_pays _ _ _) ((((descriptionFromSource X N P).planOk_ok).1 hp).blocks₁ _ (List.mem_of_getElem? (idx_at X N P))).1).plan
    (show X.Y.k.oneTime.codes.lengthsOk = true from hc ▸ lengths_full) (asks_idx hc hi).meets

/-- **Message 1, in scope's spelling.** -/
theorem msg_seedIs_scope (hp : (descriptionFromSource X N P).planOk = true) (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) : ∃ ρ y, SeedIs keyFull.codes keyFull.ranges.x.message.shape (show FirstState from x.2).d.st 1 ρ y :=
  msg_seedIs_at hc (by rw [hr]) _ (cond_msg_plan hp hc hr) msg_sampled_full D j x h

/-- **Message 0, in scope's spelling.** -/
theorem idx_seedIs_scope (hp : (descriptionFromSource X N P).planOk = true) (hc : X.Y.k.oneTime.codes = keyFull.codes) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (1 + j) x) : ∃ ρ y, SeedIs keyFull.codes keyFull.once.input.shape (show FirstState from x.2).d.st 0 ρ y :=
  idx_seedIs_at hc (by rw [hi]) _ (cond_idx_plan hp hc hi) idx_sampled_full D j x h

theorem member_one_scope (hp : (descriptionFromSource X N P).planOk = true) (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) :
    ∃ (ρ : (Fin (bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) → GE) × GEˣ) (y : GE),
      SeedIs X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape (show FirstState from x.2).d.st 1 ρ y ∧
      ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E), (show FirstState from x.2).d.st.oracles[1]? = some o ∧ o.shape = X.Y.k.oneTime.ranges.message.shape ∧ o.sampled = true ∧
        Send.form X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape 1 seed 0 = some row0 ∧ o.sampleRows.toList = [{ row0 with target := tt }] ∧
        VerifiableInference.Desc.K1.ReadsOne X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape seed.z seed.beta ρ ∧
        readP (bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) seed.z = ρ.1 ∧ readE tt = y :=
  member_one_reads _ (cond_msg_plan hp hc hr) (by rw [hr]; exact msg_sampled_full) D j x h

end Johnson.RunOne.KeyMsg
