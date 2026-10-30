-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ExchangeAtMade.lean: the kind "the code switch" (K2): THE
KIND's SHARE OF "THE EXCHANGE" AT THE TWO ITEMS ON THE ROWS THAT THE SWITCH ITSELF MAKES, "row seg
carried" AND "row seg position", under the record at a switch (`K2SeatedL`, Honest/K2/SeatedL.lean),
two premises on the verifier's book alone, asked at every reached state, AND A SECOND RECORD OF
PREMISES (`MadeAsks`, here), ASKED AT THE YES THAT THE STEP HOLDS: AT THE ROUNDS PLAYED, THE COLUMNS
SHOWN, THE ROWS LAID AND WHAT THE LOT's CLOSING RETURNS. THE FIRST RECORD's TIE `pads` IS NOT SPENT.
One definition: that second record. Five statements with their proofs: calls.

  `MadeAsks` WHAT IS ASKED AT A YES OF THE KIND's OWN DECISION, 21 FIELDS: what the place's step
                    behind keeps (2) · five on the target and the table's numbers · the eight public
                    premises of `SwitchRowsHold` at S3 · two public ties between the verifier's
                    front and the part's sending · AND FOUR ON VALUES, a field each: `honest`,
                    `claim`, `stored`, `symbols`: that law's four, at the rows V that the part lays
                    and at Wl
  `sentId_get` a sending's number i, as an entry of the list of numbers
  `msg_behind` behind the member's step the statement's codes are the part's, and the sending's
                    message n stands at its number with the shape that the part's sending gives it
  `made_behind` behind the member's step, at every continuation of the challenges heard: both items,
                    of the words that the Script's witness gives
  `exchange_carried_switch` `ExchangeAtS L.thread Said b (.row seg .carried)`
  `exchange_position_switch` `ExchangeAtS L.thread Said b (.row seg .position)`

How. `yes_shown_at_switch` (Honest/K2/Law/YesShown.lean) unpacks the step down to `AtYes` at the
kind's own decision, at the rounds played and the columns shown; `rowsLaid_inv`
(Honest/K2/Law/SenderOwn.lean, our second author's) draws Wl with its equation out of the rows'
return; the library's `AtYes.behind` (Johnson/Top/H0/Tw/K2C/TieThreeRows.lean) carries the yes
across the place's step behind; `items_in_tables_of_values` (Honest/K2/Law/ItemsInTables.lean) gives
the two items, where `newWords` and the witness's words are one at the carrying message and the
copies, INSIDE THEIR TABLES AND OFF THE NEW PADS' PLACES. THAT LAST: on the one side `newWords_g`,
`newWords_copy` (Johnson/Desc/K2/Honest/Inner/NewWordsAt.lean); on the other `padB_no_in_table`
(Inner/NoAtPadB.lean) carries such an index to one at which `padB` says no, and there
`words_off_pad` (Honest/K2/Law/WordsOffPad.lean) and the library's `held_new`
(Johnson/Prover/Send/Held.lean) give the word. What `padB_no_in_table` asks of a shape: by the
target's test (`AtSwitch.target`, Inner/Words.lean; `g_bare`, `kept_shape`, Inner/PadsProof.lean),
`pad_at_copy`, and, for a copy's answers, the first record's `noWord`. The numbers by `ids_at`
(Johnson/Top/H0/K2Hands/AtYes.lean) and `extract_get` (Johnson/Desc/K2/Honest/Returns/SentOwn.lean).
THE SHAPES ARE DERIVED, NOT ASKED: the library's `yes_new_shape`
(Johnson/Top/H0/Tw/K2C/NewAtYes.lean), `notices_zero`, `notices_kept` (K2Hands/AtYes.lean) against
`msg_behind`.

Limits. AN IMPLICATION: THE FIRST RECORD's THIRTY PREMISES, THE TWO ON THE BOOK, AND H: NONE SHOWN
AT ANY LETTERS. ALL THIRTY: R IS BOUND WHOLE: whoever calls these laws still hands over a record
with its field `pads` filled: `pads` HAS LEFT THE PROOFS, NOT THE PREMISES. TEN OF THE THIRTY ARE
PROJECTED NOWHERE ON THIS ROAD (this file, WordsOffPad.lean, YesShown.lean, SeatsBehind.lean,
StepAtSwitch.lean; by a program over their code): `firstNo`, `port`, `pads`, `seats`, `ans`,
`numbered`, `sits`, `later`, `asks`, `carryM`. A record of the other twenty, and the laws beneath
over it: not typed. WHAT H RUNS OVER: at each step under the pair, `MadeAsks` AT THE ROUNDS THAT THE
HALF PLAYED (r₁, r₂: pinned by an equation to y.1) AND AT THE GROUPS OF THE COLUMNS SHOWN
(`shownGroups` of y.1 and cols: written out): NOT at whatever rounds and columns the verifier would
accept; four returns fix c, V, Wl and s₁; of the other letters `AtYes`' own fields fix x, z, Y, cd,
and, S3 given, rows and G, each as a return; FOR S3 AND FOR t THERE IS NO SUCH RETURN: S3 lies
between two `SameTables`, t under `AtYes.kept`, `AtYes.tables` and the return of `after` (by our
reader's look the fields of `MadeAsks` read of S3 its codes and, of its messages, shapes, sample
rows and their number: what `SameTables` carries): no law here says so. THE FOUR ON VALUES ARE THE
WEIGHT: that off the pads the rows laid are the main rows of what the closing returns, that the
carried claim is true of it, that the kept members' stored sample rows say true of it, that the
opened symbols are its own: proved of no run here. `symbols` alone speaks of what is shown.
`honest`: the second half of `rowsLaid_inv` (V is `rowsAll` of `mainRows p.sizes Wl`) is dropped in
the proof: a road to it, not walked. `claim`: the first record's `asks` and `carryM`, meant for it,
are not spent. `fresh`: the library pays the like on its own side (`Gg.rows = #[]` of a front's
group without open rows: Johnson/Top/H0/Tw/K2C/TieThreeAt.lean): a road, not
walked. `first` is owed of the free letter `before` (x comes of `frontAt q s₁`, s₁ of `before s`);
`tables` and `groupRows` are laws owed of `after`, whichever t it is given. `msgs`: a tie to a
Script that is not laid; at a kept copy it wants a law of its own. SPEAKS OF THE MESSAGES' ENTRIES
OFF THE PADS, AT ONE RUN's COINS. Under `Stepped`: it holds of nothing at a book of coins that lends
the part nothing. From one member to a binder by kind: not typed. Nothing on any property.

Two elder forms. The first asked H at every r₁, r₂, gs that the verifier accepts: no honest side



-/
import Johnson.Desc.ProofFile.Honest.K2.Law.YesShown
import Johnson.Desc.ProofFile.Honest.K2.Law.WordsOffPad
import Johnson.Desc.ProofFile.Honest.K2.Law.ItemsInTables
import Johnson.Desc.ProofFile.Honest.K2.Law.SenderOwn
import Johnson.Desc.K2.Honest.Inner.NewWordsAt
import Johnson.Desc.K2.Honest.Inner.NoAtPadB
import Johnson.Desc.K2.Honest.Returns.SentOwn
import Johnson.Top.H0.Tw.K2C.NewAtYes
import Johnson.Top.H0.Tw.K2C.TieThreeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc.First (S Numbers rowSays wordsAtFirst)
open VerifiableInference.Desc.First.K2 (P2 AtYes KeptPos SameTables SentOk frameAt keptSamples
  targetRows ids_at notices_size notices_zero notices_kept yes_new_shape)
open VerifiableInference.Desc.K2.Honest (Left OldFits SeatedAt sizesAt HonestMain ClaimTrue oldWords
  SymbolsAre atPublic newWords_g newWords_copy g_bare kept_shape pad_at_copy padB_no_in_table)
open VerifiableInference.Desc.K2.Honest.Returns (extract_get)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)
open _root_.Desc.K14.Law (shownGroups)

/-- **WHAT IS ASKED AT A YES OF THE KIND's OWN DECISION.** A record of premises. N: the table's
numbers. Pr: the part's sending. s, t, s': the states in front of the member, behind the kind's own
decision, behind the member. V: the rows that the part lays. Wl: what the lot's closing returns: a
letter here; the laws below bind it with its equation in front. The other letters: the library's at
a yes. The last four fields speak of values: proved of no run. Nothing here proves that it can be
met. NOT IN FRONT OF A LAW OVER COINS. -/
structure MadeAsks (N : Numbers) (seg : Nat) (Pr : K1.Par) (q : P2) (s t s' : S)
    (V : Nat → Johnson.Prover.Send.Rows) (Wl : Left) (r₂ : Fmt.RoundView) (x : _root_.Tw.K2.Front)
    (z : _root_.Tw.K2.Sent)
    (S3 : Statement) (Y : Array E) (G : Group) : Prop where
  /-- the place's step behind keeps the tables -/
  tables : SameTables t.st s'.st
  /-- and the open rows of the switch's group -/
  groupRows : (s'.st.groups[x.f.group]?).map (·.rows) = (t.st.groups[x.f.group]?).map (·.rows)
  /-- public, on the target -/
  keptPos : KeptPos x.T
  /-- the group had no open row in front -/
  fresh : G.rows = #[]
  /-- public, on the table's numbers -/
  groupNo : N.groupAt seg = x.f.group
  carriedNo : ∀ W₀, frameAt x = some W₀ → N.rowsAt seg .carried = (0, 1 + keptSamples x W₀)
  positionNo : ∀ W₀, frameAt x = some W₀ → N.rowsAt seg .position =
    (1 + keptSamples x W₀, r₂.drawn.poss.length * (1 + targetRows x.T + 2))
  /-- the eight public premises of `SwitchRowsHold` at the statement behind the joins -/
  check : switchTargetCheck S3 x.f.rows x.T = true
  restMain : x.T.rest.part = .main
  fits : OldFits S3 x.f.rows
  seated : SeatedAt S3 x.f.rows x.T (z.ids.getD 0 noId) (z.ids.extract 1 (1 + x.T.kept.size))
  lengths : S3.codes.lengthsOk = true
  logC : (S3.codes.base.getD x.f.rows.code default).logN ≤ 32
  logZ : (S3.codes.mask.getD x.f.rows.maskCode default).logN ≤ 32
  inRange : ∀ v ∈ (Positions.ofDraws q.logN r₂.drawn.poss).all.toList,
    v < 2 ^ (S3.codes.base.getD x.f.rows.code default).logN
  /-- public: the front has as many oracle messages as the state in front of the member -/
  first : x.st.oracles.size = s.st.oracles.size
  /-- public: the part's sending holds the carrying message and a copy for each kept target -/
  count : 1 + x.T.kept.size ≤ Pr.sent.size
  /-- ON VALUES: off the pads the rows laid are the main rows of what the closing returns -/
  honest : HonestMain (sizesAt S3 x.f.rows x.T) Wl V
  /-- ON VALUES: the carried claim is true of it -/
  claim : ClaimTrue (sizesAt S3 x.f.rows x.T) x.f.rows Wl
  /-- ON VALUES: the kept members' stored sample rows say true of it -/
  stored : ∀ o ∈ (switchKept x.f.rows).toList,
    ∀ r ∈ (S3.oracles.getD o default).sampleRows.toList,
      Says rdE S3 r (oldWords (sizesAt S3 x.f.rows x.T) x.f.rows Wl)
  /-- ON VALUES, AND ON THE COLUMNS: what these open at the positions drawn is its own -/
  symbols : SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl
    (Positions.ofDraws q.logN r₂.drawn.poss) Y

/-- A sending's number i, as an entry of the list of numbers. -/
theorem sentId_get {St St' : Statement} {notices : Array OracleNotice} {ids : Array Nat}
    (h : SentOk St notices ids St') (i : Nat) (hi : i < notices.size) :
    ids[i]? = some (St.oracles.size + i) := by
  rw [h.ids]
  simp [hi]
  omega

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : S → Except String S}
  {after : S → S → Except String S} {seg first : Nat} {Zp : ProofFile.Pub} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- Behind the member's step the statement's codes are the part's, and the sending's message n
stands at its number with the shape that the part's sending gives it. hA: the thread's invariant in
front of the member (`ThrS`). hS: `Thread.Stepped`: the half has moved, and the member's own step
returns s' at what was played. NOT IN FRONT OF A LAW OVER COINS. -/
theorem msg_behind
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (n : ℕ) (hn : n < (switchPar p).sent.size) :
    s'.st.codes = p.sizes.codes ∧ ∃ o, s'.st.oracles[s.st.oracles.size + n]? = some o ∧
      o.shape = shapeAt (switchPar p) n := by
  obtain ⟨-, -, r₁, r₂, gs, -, -, hdec, hfit, -, -, -, -⟩ := step_at_switch R Said hA hd hS
  have hB := R.books _ _ _ _ _ _ _ _ hA.1 hdec
  obtain ⟨-, hl⟩ := fit_trimmed (switchPar p) q R.seedsNo R.nonZeroNo R.answersNo hfit
  obtain ⟨b', hS', hd'⟩ := block_at_cut (switchPar p)
    (fun _ _ _ _ h => R.sends _ _ _ _ _ _ _ _ hA.1 h) hdec hl
  obtain ⟨hcodes, o, ho, hos, -⟩ := ProofFile.Honest.K1.msg_at_block (switchPar p) hS' hd' hB n hn
  exact ⟨hcodes, o, ho, hos⟩

/-- **THE TWO ITEMS ON THE MADE ROWS**: behind the member's step, at every continuation of the
challenges heard. hFits, hNum: TWO PREMISES on the verifier's book alone, asked at every reached
state (here: at the state behind the step). H: `MadeAsks` at the rounds played, the columns shown,
the rows laid and what the lot's closing returns. THE TIE `pads` IS NOT SPENT. SPEAKS OF THE
MESSAGES' ENTRIES OFF THE PADS. hA: the thread's invariant in front of the member (`ThrS`). hS:
`Thread.Stepped`: the half has moved, and the member's own step returns s' at what was played.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem made_behind
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s')
    (hFits : VerifiableInference.Desc.Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (H : ∀ c V Wl r₁ r₂ s₁ t x z S3 Y rows G cd, handed 0 p k = some c →
      switchRowsLaid D readers (lotClosingAt lay segs) p c m.st.input m.st.heard = .ok V →
      lotClosingAt lay segs p (D m.st.input.x) (readers m.st.input)
        (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries c.2.2) = .ok Wl →
      (roundsOf y.1).map noDigest = [r₁, r₂] → before s = .ok s₁ →
      AtYes q s₁ t r₁ r₂ (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows G cd →
      after s₁ t = .ok s' → MadeAsks L.N seg (switchPar p) q s t s' V Wl r₂ x z S3 Y G)
    (pp : P) (yy : Strs) (ds' : List Fmt.Drawn) :
    rowSays L.N (wordsAtFirst arr) seg .carried (pp, s') yy
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) ∧
      rowSays L.N (wordsAtFirst arr) seg .position (pp, s') yy
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) := by
  obtain ⟨c, V, r₁, r₂, s₁, t, x, z, S3, Y, rows, G, cd, hc, hV, hrs, -, -, -, -, hb, A, ha,
    -, -⟩ := yes_shown_at_switch R Said hA hd hS
  obtain ⟨Wl, hW, -⟩ := rowsLaid_inv hV
  have M := H c V Wl r₁ r₂ s₁ t x z S3 Y rows G cd hc hV hW hrs hb A ha
  have A' := A.behind M.tables M.groupRows
  have hsz := notices_size x.T x.others
  have AP := atPublic M.check M.restMain M.fits (keptPos_list M.keptPos) M.seated M.lengths
  have hcount := M.count
  have hcS : s'.st.codes = S3.codes := A'.tables.codes
  refine items_in_tables_of_values L.N (wordsAtFirst arr) seg pp yy _ A' M.keptPos M.fresh
    M.groupNo M.carriedNo M.positionNo M.check M.restMain M.fits M.seated M.lengths M.logC M.logZ
    M.inRange Wl V M.honest M.claim M.stored M.symbols ?_ ?_
  · intro part i hi hno
    have h0 : 0 < (switchPar p).sent.size := by omega
    have hg0 : z.ids.getD 0 noId = s.st.oracles.size + 0 := by
      rw [ids_at A.sent 0 (by rw [hsz]; omega), M.first]
    obtain ⟨hcd, x₀, hx₀, hs₀⟩ := msg_behind R Said hA hd hS 0 h0
    have hxT : x₀.shape = x.T.shape := by
      have h1 := yes_new_shape A' 0
      rw [notices_zero, M.first, hx₀] at h1
      exact Option.some.inj h1
    rw [hg0] at hi
    have hb' := padB_no_in_table s'.st _ x₀ hx₀ (by rw [hcS]; exact M.lengths)
      (by rw [hcS, hxT]; exact AP.target.code) (by rw [hxT]; exact g_bare AP)
      (by rw [hcS, hxT, ← _root_.Tw.K2.padFits_eq]; exact AP.target.pad)
      (by rw [hxT]; exact AP.target.sampled) part i hi (by rw [hcS, hxT]; exact hno)
    rw [hcd, hs₀] at hb'
    rw [newWords_g]
    show (V 0).word x.T.shape part i = Sound.wordsFirst arr s'.st s'.book _ _ part i
    rw [hg0, words_off_pad R Said hA hd hS hFits hNum c hc V hV 0 h0 (fun _ _ _ => 0) ds' part i
      hb', Johnson.Prover.Send.held_new _ _ _ _ 0 h0, ← hs₀, hxT]
  · intro a kt hk part i hi hno
    obtain ⟨ha', hke⟩ := Array.getElem?_eq_some_iff.1 hk
    have hn1 : 1 + a < (switchPar p).sent.size := by omega
    have hids : z.ids.size = (_root_.Tw.K2.switchNotices x.T x.others).size := by
      rw [A.sent.ids]
      simp
    have hget : (z.ids.extract 1 (1 + x.T.kept.size))[a]? = some (s.st.oracles.size + (1 + a)) := by
      rw [extract_get z.ids 1 (1 + x.T.kept.size) a (by rw [hids, hsz]; omega) (by omega),
        sentId_get A.sent (1 + a) (by rw [hsz]; omega), M.first]
    have hD : (z.ids.extract 1 (1 + x.T.kept.size)).getD a noId = s.st.oracles.size + (1 + a) := by
      rw [Array.getD_eq_getD_getElem?, hget]
      rfl
    obtain ⟨hcd, x₁, hx₁, hs₁⟩ := msg_behind R Said hA hd hS (1 + a) hn1
    have hxT : x₁.shape = kt.shape := by
      have h1 := yes_new_shape A' (1 + a)
      rw [notices_kept _ _ a ha', hke, M.first, hx₁] at h1
      exact Option.some.inj h1
    obtain ⟨so, -, K⟩ := kept_shape AP a kt hk
    have hans : 1 ≤ kt.shape.answers := by
      have hn' : 1 + a < (switchSent p.sizes p.others).size := by
        rw [← ProofFile.Honest.K2.sendingPar_sent p.sizes.codes (switchSent p.sizes p.others)]
        exact hn1
      have e2 : ((switchSent p.sizes p.others).getD (1 + a) default).shape = kt.shape := by
        rw [← ProofFile.Honest.K2.sendingPar_shape p.sizes.codes (switchSent p.sizes p.others) (1 + a)]
        exact hs₁.symm.trans hxT
      have hw := R.noWord (1 + a) hn'
      rw [e2] at hw
      have hpos := AP.keptPos kt (Array.mem_toList_iff.2 (Array.mem_of_getElem? hk))
      rcases hw with h | h <;> omega
    rw [hD] at hi
    have hb' := padB_no_in_table s'.st _ x₁ hx₁ (by rw [hcS]; exact M.lengths)
      (by rw [hcS, hxT]; exact K.code) (by rw [hxT]; exact K.newBare)
      (by rw [hcS, hxT]; exact pad_at_copy S3.codes so kt.shape K)
      (by rw [hxT]; exact hans) part i hi (by rw [hcS, hxT]; exact hno)
    rw [hcd, hs₁] at hb'
    rw [hD, newWords_copy AP V a kt hk _ (by rw [Array.getElem?_toList]; exact hget) part i]
    show _ = Sound.wordsFirst arr s'.st s'.book _ _ part i
    rw [words_off_pad R Said hA hd hS hFits hNum c hc V hV (1 + a) hn1 (fun _ _ _ => 0) ds' part i
      hb', Johnson.Prover.Send.held_new _ _ _ _ (1 + a) hn1, ← hs₁, hxT]

/-- **AT "row seg carried"**, UNDER THE TWO PREMISES on the verifier's book alone, asked at every
reached state, AND `MadeAsks` AT THE ROUNDS PLAYED, THE COLUMNS SHOWN, THE ROWS LAID AND WHAT THE
LOT's CLOSING RETURNS: at every step under the pair. THE TIE `pads` IS NOT SPENT. FREE LETTERS OF
THE RECORD: D · readers · rad · before · after; and, inside its field `sends`, the type Lt and the
states d, d'. `readers` takes the whole input. Under `Stepped`: where the book of coins lends the
part nothing the ends hold of nothing. NOT IN FRONT OF A LAW OVER COINS. -/
theorem exchange_carried_switch
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (hFits : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      VerifiableInference.Desc.Book.BookFits s'.book)
    (hNum : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (H : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ c V Wl r₁ r₂ s₁ t x z S3 Y rows G cd, handed 0 p k = some c →
        switchRowsLaid D readers (lotClosingAt lay segs) p c m.st.input m.st.heard = .ok V →
        lotClosingAt lay segs p (D m.st.input.x) (readers m.st.input)
          (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries c.2.2) = .ok Wl →
        (roundsOf y.1).map noDigest = [r₁, r₂] → before s = .ok s₁ →
        AtYes q s₁ t r₁ r₂ (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows G cd →
        after s₁ t = .ok s' → MadeAsks L.N seg (switchPar p) q s t s' V Wl r₂ x z S3 Y G) :
    ExchangeAtS L.thread Said b (.row seg .carried) := by
  intro blk' hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk' = blk := Option.some.inj (hblk.symm.trans R.member)
  show (L.Mg y.2.st.input).row seg .carried _ _ _
  rw [R.rowM]
  exact (made_behind R Said hA hd hS (hFits _ _ _ _ _ _ _ _ hA hd hS)
    (hNum _ _ _ _ _ _ _ _ hA hd hS) (H _ _ _ _ _ _ _ _ hA hd hS) _ _ ds').1

/-- **AT "row seg position"**: under the same. FREE LETTERS OF THE RECORD: D · readers · rad ·
before · after; and, inside its field `sends`, the type Lt and the states d, d'. `readers` takes the
whole input. Under `Stepped`: where the book of coins lends the part nothing the ends hold of
nothing. NOT IN FRONT OF A LAW OVER COINS. -/
theorem exchange_position_switch
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (hFits : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      VerifiableInference.Desc.Book.BookFits s'.book)
    (hNum : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (H : ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ c V Wl r₁ r₂ s₁ t x z S3 Y rows G cd, handed 0 p k = some c →
        switchRowsLaid D readers (lotClosingAt lay segs) p c m.st.input m.st.heard = .ok V →
        lotClosingAt lay segs p (D m.st.input.x) (readers m.st.input)
          (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries c.2.2) = .ok Wl →
        (roundsOf y.1).map noDigest = [r₁, r₂] → before s = .ok s₁ →
        AtYes q s₁ t r₁ r₂ (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows G cd →
        after s₁ t = .ok s' → MadeAsks L.N seg (switchPar p) q s t s' V Wl r₂ x z S3 Y G) :
    ExchangeAtS L.thread Said b (.row seg .position) := by
  intro blk' hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk' = blk := Option.some.inj (hblk.symm.trans R.member)
  show (L.Mg y.2.st.input).row seg .position _ _ _
  rw [R.rowM]
  exact (made_behind R Said hA hd hS (hFits _ _ _ _ _ _ _ _ hA hd hS)
    (hNum _ _ _ _ _ _ _ _ hA hd hS) (H _ _ _ _ _ _ _ _ hA hd hS) _ _ ds').2

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.MadeAsks
#print axioms ProofFile.Honest.K2.Law.sentId_get
#print axioms ProofFile.Honest.K2.Law.msg_behind
#print axioms ProofFile.Honest.K2.Law.made_behind
#print axioms ProofFile.Honest.K2.Law.exchange_carried_switch
#print axioms ProofFile.Honest.K2.Law.exchange_position_switch
