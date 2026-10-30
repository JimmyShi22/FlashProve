-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeedOk.lean: THEOREMS. **THE SENDING KIND's ROW AT A SEED, WITH THE SEED's COORDINATES CANONICAL (every word below the field's prime: okE), DRAWN OFF THE HISTORY OF Key.descriptionFromSource's CHAIN 1: OF THE SAME SEED.** SeedIs (Johnson/Desc/K1/Law/SeedIs.lean) binds the seed's point z in an ∃
and says of it its length and how it READS: nothing on its words. So okE is earned where the row is laid (z is a stretch of the drawn elements; a held block's yes has every word below the prime) and carried (K1.SmpStay keeps the sample rows to the letter). («State» := what the verifier carries between two blocks.)
OBJECT. LPFD.Hist₁ | Hist₃ (Key.descriptionFromSource X N P) D · the three sendings of chain 1. USER. sampleL_of_seed₂ (a shape with rows of both kinds), which asks okE of the seed's last coordinate that the message's cube uses; MemberFacts, clause (2). LETTERS. cs · s · St · o · ρ · y; Q · rad; X · N · P · D · m · j · k · x.
  SeedOk             SeedIs's text with one conjunct more inside its ∃: ∀ c ∈ z, okE c = true
  SeedOk.seedIs | .stays | .travels      it gives SeedIs; it stays along SmpStay and along SameMsgs
  cut_fst_mem · seedOk_behind      **behind a yes of the sending's decision at drawn words below the prime**: seedIs_behind_len (Johnson/Desc/K1/Law/GoodSend3.lean), ITS PROOF GONE THROUGH ONCE MORE WITH z KEPT (over the sending kind's files' own lemmas): a stronger statement; if that theorem is strengthened, this yields
  send_seedOk · msg_seedOk · w_seedOk | w_seedOk_into₃      KeyMsgOne.lean's and KeyMsgAll.lean's laws at SeedOk
  seedOk_reads · seed_last_ok      **in the program's words, of ONE seed: KeyMsgAll.lean's seedIs_reads' facts ∧ ∀ c ∈ seed.z, okE c = true** · okE (seed.z.getD (bitsZ cs s − 1) zeroE) = true
  member_one_ok | member_one_ok_scope      message 1 so, at every border from 2 on
What is not claimed. okE of the factor or of the target (not asked). Which ρ. Nothing on soundness.

-/
import Johnson.RunOne.KeyMsgAll

set_option autoImplicit false

namespace Johnson.RunOne.KeyMsg

open OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps Johnson.RunOne.KeySendGood
open VerifiableInference.Desc (Block noDigest viewWordsBelowPrime roundsFit)
open VerifiableInference.Desc.Sound (held)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K1
open LPFD (Reached Hist₁ Hist₃)
open Johnson.Pack (bitsZ)
open Lk6.AtPlan (keyFull)

/-- **SeedIs, with the seed's coordinates canonical.** -/
def SeedOk (cs : Codes) (s : OracleShape) (St : Statement) (o : ℕ) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (y : GE) : Prop :=
  St.codes = cs ∧ ∃ x z β t, St.oracles[o]? = some x ∧ x.shape = s ∧ x.sampled = true ∧
    x.sampleRows = #[sampleRow (Msg.of cs s) o z β 0 t] ∧ ReadsOne cs s z β ρ ∧ readE t = y ∧ ∀ c ∈ z, okE c = true

section
variable {cs : Codes} {s : OracleShape} {A B : Statement} {o : ℕ} {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}

theorem SeedOk.seedIs (h : SeedOk cs s A o ρ y) : SeedIs cs s A o ρ y := by
  obtain ⟨hc, x, z, β, t, hx, h1, h2, h3, h4, h5, _⟩ := h
  exact ⟨hc, x, z, β, t, hx, h1, h2, h3, h4, h5⟩

theorem SeedOk.stays (h : SeedOk cs s A o ρ y) (hs : SmpStay A B) : SeedOk cs s B o ρ y := by
  obtain ⟨hc, x, z, β, t, hx, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨x', hx', e1, e2, e3⟩ := hs.2 o x hx h2
  exact ⟨hs.1.trans hc, x', z, β, t, hx', e1.trans h1, e2, e3.trans h3, h4, h5, h6⟩

theorem SeedOk.travels (h : SeedOk cs s A o ρ y) (hs : SameMsgs A B) : SeedOk cs s B o ρ y := by
  obtain ⟨hc, x, z, β, t, hx, h1, h2, h3, h4, h5, h6⟩ := h
  have e := hs.2 o
  rw [hx] at e
  obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨e1, e23⟩ := Prod.mk.inj e
  obtain ⟨e2, e3⟩ := Prod.mk.inj e23
  exact ⟨hs.1.trans hc, x', z, β, t, hx', e1.trans h1, e2.trans h2, e3.trans h3, h4, h5, h6⟩

/-- **In the program's words, of one seed.** -/
theorem seedOk_reads (hT : Tie cs s) (h : SeedOk cs s A o ρ y) :
    ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E), A.oracles[o]? = some x ∧ x.shape = s ∧ x.sampled = true ∧ Send.form cs s o seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧ ReadsOne cs s seed.z seed.beta ρ ∧ readP (bitsZ cs s) seed.z = ρ.1 ∧ readE tt = y ∧ ∀ c ∈ seed.z, okE c = true := by
  obtain ⟨_, x, z, β, t, hx, hs, hsm, hr, hread, hy, hok⟩ := h
  obtain ⟨row0, h0, h1⟩ := Option.map_eq_some_iff.1 (form_eq cs s o z β 0 t hT.lengths hT.shape hT.fits)
  exact ⟨x, ⟨z, β⟩, row0, t, hx, hs, hsm, h0, by rw [hr, ← h1], hread, funext fun u => hread.point u, hy, hok⟩

end

/-- The last coordinate that the message's cube uses is canonical. -/
theorem seed_last_ok (cs : Codes) (s : OracleShape) (z : List E) (h0 : 0 < bitsZ cs s) (hl : bitsZ cs s ≤ z.length) (hok : ∀ c ∈ z, okE c = true) : okE (z.getD (bitsZ cs s - 1) zeroE) = true := by
  have hlt : bitsZ cs s - 1 < z.length := by omega
  rw [List.getD_eq_getElem _ _ hlt]
  exact hok _ (List.getElem_mem hlt)

/-- The point of a seed that is cut off a list is a stretch of the list. -/
theorem cut_fst_mem (v : ℕ) : ∀ (n : ℕ) (l : List E) (sd : List E × E), sd ∈ cutSeeds v n l → ∀ c ∈ sd.1, c ∈ l
  | 0, _, _, h => by simp [cutSeeds] at h
  | n + 1, l, sd, h => by
    simp only [cutSeeds, List.mem_cons] at h
    rcases h with rfl | h
    · exact fun c hc => List.mem_of_mem_take hc
    · exact fun c hc => List.mem_of_mem_drop (cut_fst_mem v n (l.drop (v + 1)) sd h c hc)

variable {L : Type}

/-- **Behind a yes of the sending's decision, at drawn words below the prime.** seedIs_behind_len (Johnson/Desc/K1/Law/GoodSend3.lean), its proof gone through with z kept. -/
theorem seedOk_behind (P : Par) (rad : ℕ → ℕ) (owed : Option ℕ) (d d' : _root_.Desc.Plain.DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array ℕ) (hC : condPort P rad = true)
    (hlen : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1)) (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (hok : ∀ x ∈ r₁.drawn.elems, okE (E.ofTriple x) = true) (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ y, SeedOk P.codes (shapeAt P k) d'.st (d.st.oracles.size + k.val) (VerifiableInference.Desc.K1.seedAt P (bitsZ P.codes (shapeAt P k)) ρ) y := by
  have hT := cond_tie P rad hC k hk
  have h1 : 0 < P.seeds := one_le_seeds P k hk
  obtain ⟨sd, hsd, hz, hβ⟩ := hρ ⟨0, h1⟩
  obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k.val k.isLt
  have hk' : (shapesOf P)[k.val].answers ≠ 0 := hk
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + k.val]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val] ys') := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k.val]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  obtain ⟨t, ht⟩ : ∃ t, ys'[0]? = some t :=
    ⟨ys'[0]'(Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hk') hy), List.getElem?_eq_getElem _⟩
  have hlen' : sd.1.length = P.coordinates := cutSeeds_get _ _ _ _ sd hlen hsd
  have hb := bits_le_coordinates P k hk
  have e3 : VerifiableInference.Desc.K1.seedAt P (bitsZ P.codes (shapeAt P k)) ρ =
      (fun t => pointOf (ρ ⟨0, h1⟩).1 t.val, (ρ ⟨0, h1⟩).2) := by
    unfold VerifiableInference.Desc.K1.seedAt ownSeeds
    exact dif_pos h1
  refine ⟨readE t, hc, _, sd.1, sd.2, t, hx, ?_, by simp [wr, hk'], ?_, ?_, rfl, ?_⟩
  · unfold wr
    split <;> rfl
  · have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k.val)
          (shapesOf P)[k.val] ys' := by simp [wr, hk']
    rw [hrows]
    exact rowsOf_one _ _ _ _ _ hT.one sd t hsd ht
  · rw [e3]
    refine ⟨by rw [hlen']; exact hb, fun u => ?_, hβ⟩
    have hu : u.val < P.coordinates := Nat.lt_of_lt_of_le u.isLt hb
    show readL sd.1 u.val = pointOf (ρ ⟨0, h1⟩).1 u.val
    unfold pointOf
    rw [dif_pos hu]
    exact hz ⟨u.val, hu⟩
  · intro c hcm
    obtain ⟨x, hx', e⟩ := List.mem_map.1 (cut_fst_mem _ _ _ sd (List.mem_of_getElem? hsd) c hcm)
    exact e ▸ hok x hx'

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **Behind a sending of chain 1, general in the place.** -/
theorem send_seedOk (Q : Par) (rad : ℕ → ℕ) (hC : condPort Q rad = true) (b₀ : Block FirstState Claim) (m : ℕ) (hb : (descriptionFromSource X N P).first.blocksInOrder[m]? = some b₀)
    (hr : b₀.rounds = VerifiableInference.Desc.K1.rounds Q) (hS : Named Q b₀) (k : Fin (shapesOf Q).length) (hk : sampledAt Q k) (D : OnBytes.Maker.WholeD)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + 1) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧
      ∃ ρ y, SeedOk Q.codes (shapeAt Q k) (show FirstState from x.2).d.st ((show FirstState from x0.2).d.st.oracles.size + k.val) ρ y := by
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
  have hokd : ∀ y ∈ (noDigest r₁).drawn.elems, okE (E.ofTriple y) = true := fun y hy => okE_of_view hview (noDigest r₁) (by simp) y hy
  obtain ⟨ρ, hρ⟩ := readsAs_of_yes Q _ _ _ _ _ _ hyes hlen hokd
  obtain ⟨y, hy⟩ := seedOk_behind Q rad _ _ _ _ _ _ hC hlen hyes ρ hρ hokd k hk
  exact ⟨a', hre, hh.1.symm, _, y, hy.travels hs⟩

/-- It is carried from border to border of one history. -/
theorem seedOk_later (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧
      ∀ cs s o ρ y, SeedOk cs s (show FirstState from x0.2).d.st o ρ y → SeedOk cs s (show FirstState from x.2).d.st o ρ y := by
  obtain ⟨x0, h0, e0, hs⟩ := Johnson.RunOne.KeyWalk.hist₁_rel groundKeeps_smpStay Johnson.RunOne.KeyWalk.begin_smp D m j x h
  exact ⟨x0, h0, e0, fun _ _ _ _ _ k => k.stays hs⟩

theorem msg_named (one : OneTime) (N' : Pieces) (groups : List (List ℕ)) :
    Named (sendingPar one N'.msg "the lookups' own message and what rides with it" (Wf.messageOf one.ranges) groups) (bareOf (sendOwnMessage one N' groups)) := by
  intro s s' r₁ r₂ gs h
  obtain ⟨m, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok h
  obtain ⟨ids, d', hd, e1, _⟩ := k1At_sent h1
  exact ⟨ids, d', hd, by rw [← e1]; exact wfGroup_same h2⟩

/-- **Message 1 at every border from 2 on.** -/
theorem msg_seedOk (rad : ℕ → ℕ) (hC : condPort (parMsg X) rad = true) (hk : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) :
    ∃ ρ y, SeedOk X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape (show FirstState from x.2).d.st 1 ρ y := by
  obtain ⟨x2, h2, _, hs⟩ := seedOk_later D 2 j x h
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
  obtain ⟨x1, hx1, _, hall⟩ := send_seedOk (parMsg X) rad hC _ 1 (msg_at X N P) (rounds_msg X) (msg_named _ _ _) ⟨0, h0⟩ hk' D x2 h2
  have hs1 : (show FirstState from x1.2).d.st.oracles.size = 1 := size_at₁ D x1 hx1
  rw [hs1, hat] at hall
  obtain ⟨ρ, y, hy⟩ := hall
  exact ⟨ρ, y, hs _ _ _ _ _ hy⟩

/-- **W's message at every border behind w.1.send.** -/
theorem w_seedOk {bw : Block FirstState Claim} {msg : Array OracleNotice} (hb : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw)
    (hm : linMessageW X.Y.k.oneTime.lin = some msg) (rad : ℕ → ℕ) (hC : condPort (parW X msg) rad = true) (k : Fin (shapesOf (parW X msg)).length) (hk : sampledAt (parW X msg) k)
    (D : OnBytes.Maker.WholeD) (j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (bW X N P + 1 + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D (bW X N P) x0 ∧ x0.1 = x.1 ∧
      ∃ ρ y, SeedOk X.Y.k.oneTime.codes (shapeAt (parW X msg) k) (show FirstState from x.2).d.st ((show FirstState from x0.2).d.st.oracles.size + k.val) ρ y := by
  obtain ⟨x1, h1, e1, hs⟩ := seedOk_later D (bW X N P + 1) j x h
  obtain ⟨x0, hx0, e0, ρ, y, hy⟩ := send_seedOk (parW X msg) rad hC _ (bW X N P) (w_at X N P hb) (rounds_w hm hb) (w_named hm hb) k hk D x1 h1
  exact ⟨x0, hx0, e0.trans e1, ρ, y, hs _ _ _ _ _ hy⟩

/-- **… and at every state that chain 3 reaches.** -/
theorem w_seedOk_into₃ {bw : Block FirstState Claim} {msg : Array OracleNotice} (hb : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw)
    (hm : linMessageW X.Y.k.oneTime.lin = some msg) (rad : ℕ → ℕ) (hC : condPort (parW X msg) rad = true) (k : Fin (shapesOf (parW X msg)).length) (hk : sampledAt (parW X msg) k)
    (D : OnBytes.Maker.WholeD) (j : ℕ) (hj : bW X N P + 1 + j = (descriptionFromSource X N P).first.blocksInOrder.length) (n : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D n a) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D (bW X N P) x0 ∧ x0.1 = a.1.1 ∧
      ∃ ρ y, SeedOk X.Y.k.oneTime.codes (shapeAt (parW X msg) k) (show S₃ from a.2).st ((show FirstState from x0.2).d.st.oracles.size + k.val) ρ y := by
  obtain ⟨x1, h1, e1, hs⟩ := Johnson.RunOne.KeyWalk.hist₃_from_border_rel groundKeeps_smpStay Johnson.RunOne.KeyWalk.begin_smp D (bW X N P + 1) j hj n a h
  obtain ⟨x0, hx0, e0, ρ, y, hy⟩ := send_seedOk (parW X msg) rad hC _ (bW X N P) (w_at X N P hb) (rounds_w hm hb) (w_named hm hb) k hk D x1 h1
  exact ⟨x0, hx0, e0.trans e1, ρ, y, hy.stays hs⟩

/-- **Message 1 in the program's words, of one seed, its coordinates canonical.** -/
theorem member_one_ok (rad : ℕ → ℕ) (hC : condPort (parMsg X) rad = true) (hk : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) :
    ∃ (ρ : (Fin (bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) → GE) × GEˣ) (y : GE),
      SeedIs X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape (show FirstState from x.2).d.st 1 ρ y ∧
      ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E), (show FirstState from x.2).d.st.oracles[1]? = some o ∧ o.shape = X.Y.k.oneTime.ranges.message.shape ∧ o.sampled = true ∧
        Send.form X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape 1 seed 0 = some row0 ∧ o.sampleRows.toList = [{ row0 with target := tt }] ∧
        ReadsOne X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape seed.z seed.beta ρ ∧
        readP (bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) seed.z = ρ.1 ∧ readE tt = y ∧ ∀ c ∈ seed.z, okE c = true := by
  obtain ⟨ρ, y, hy⟩ := msg_seedOk rad hC hk D j x h
  exact ⟨ρ, y, hy.seedIs, seedOk_reads (msg_tie rad hC hk) hy⟩

theorem member_one_ok_scope (hp : (descriptionFromSource X N P).planOk = true) (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (D : OnBytes.Maker.WholeD) (j : ℕ)
    (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (2 + j) x) :
    ∃ (ρ : (Fin (bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) → GE) × GEˣ) (y : GE),
      SeedIs X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape (show FirstState from x.2).d.st 1 ρ y ∧
      ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E), (show FirstState from x.2).d.st.oracles[1]? = some o ∧ o.shape = X.Y.k.oneTime.ranges.message.shape ∧ o.sampled = true ∧
        Send.form X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape 1 seed 0 = some row0 ∧ o.sampleRows.toList = [{ row0 with target := tt }] ∧
        ReadsOne X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape seed.z seed.beta ρ ∧
        readP (bitsZ X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape) seed.z = ρ.1 ∧ readE tt = y ∧ ∀ c ∈ seed.z, okE c = true :=
  member_one_ok _ (cond_msg_plan hp hc hr) (by rw [hr]; exact msg_sampled_full) D j x h

end Johnson.RunOne.KeyMsg
