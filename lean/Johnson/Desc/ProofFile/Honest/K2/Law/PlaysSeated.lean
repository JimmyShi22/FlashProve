-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlaysSeated.lean: the kind "the code switch" (K2): THE DEBT "IT
PLAYS" (`Plays`, Honest/Thread/Pays.lean) AT THE SWITCH's OWN MEMBER OF A THREAD, OF THE KIND's ONE
LOT's HALF: from the named premises on the thread's letters (`K2Seated`, Honest/K2/Seated.lean), six
public tests and equations, and TWO PREMISES MORE ON THE THREAD's LETTERS. At every run's coins and
every list of challenges that the member's rounds can draw: `play` returns, the columns that the
second round reads are laid, and the member's new trees are the thread's tables. LAWS ALONE:
statements with their proofs; no definition.

  `play_two_is`     a tool: what `play` returns over two steps whose stops never stop
  `same_self`       a table shows what it shows
  `core_tables_ok`, `core_answers_ok`   the lot's own sender's tables and answers return, with the
                    trees' shapes; as many as the sending has
  `moves_say`       so the part's two moves return, and both messages have the rounds' shapes
  `half_played`     what `play` returns over the half's two rounds: the first round's tables are
                    what the part's first move says
  `lendRow_one`, `lendPart_lift`, `lent_part`   what the book lends the half's row is what it lends
                    the part
  `old_cols`        the columns that the second round reads are laid, where each tree that it opens
                    is at hand with the width that the round states
  `tableAt_is`      `switchTableAt` (Honest/K2/Seated.lean) is the table that the first move says
  `mem_fresh`       a source that is new behind a member is one of the member's own trees
  `rounds_items`    what the kind's two rounds state beside roots
  `switch_plays`    THE DEBT

THE PREMISES OF `switch_plays`. (1) `K2Seated`, at the lot's own sender and closing. Of its fields
NINE are spent: here · place · half · rounds · oracles · roots · opens · table · fixed: the nine
that its head names for this debt. (2) Public, on the place: `Sizes.serves` · `Sizes.roomy` ·
`placeFits` · `closingOk`. (3) Public, the place's numbers q against the honest sending: the oracle
messages that q states have the shapes of the sending's trees; the sending has q.answers answers. At
the plan's own numbers the first is a theorem and the second a named test (`place_shapes`,
`answersFit`: Honest/K2/Law/PlaysAtPlan.lean): not called here. (4) ON THE LETTER `valid`: a valid
input's public instance passes `publicOk`. (5) ON THE LETTER `table`, AT A STAND AT WHICH THE THREAD
HOLDS IN FRONT OF THE MEMBER, AND NOWHERE ELSE: each tree that the second round opens has there, as
the thread's table (`Thread.tableAt`), the width that the numbers' list `read` states for it. (Asked
at every input it would, by the texts, fail at a thread with an earlier switch whose part refuses at
some input: there that switch's table is the one without a word. No theorem says it.)

By: `half_steps`, `treeShapes` (Honest/K2/Law/Plays.lean) · `steps_two`, `lift_moves`, `draws_two`,
`zipIdx_fst`, `rowsAll_returns`, `returnsLaw`, `switchRowsAt_again` (this folder and
Honest/K2/Exact.lean) · `filter_cut` (Johnson/Desc/K2/Honest/Returns/ItemsFit.lean) · the frame's
`stop_none` (Honest/Law/ToyPlay.lean; an elder PlayTwo.lean declared its own, the step an explicit
argument: the two calls here meet both), `steps_one_half` (Honest/Law/Thread.lean), `fillCols_ok`
(Honest/Law/Fill.lean), `Env.add_keeps`, `treesTo_succ` (Honest/Thread/MadeLaw.lean), `play_heard`,
`Thread.heard_length` (Honest/Thread/PaysLaw.lean) · the shared sending's writer's `length_answers`
(Johnson/Prover/Send/Form.lean). Kin: the like debt at the smallness test's member
(Honest/K8/SeatedPlays.lean), whose round sends and opens no tree.

Limits. NO MEMBER: `K2Seated` is shown at no thread, and the premises are shown met together
nowhere. AT ONE SORT OF THREAD IT CANNOT BE MET: its field `table` is an equation at every list of
challenges; where a thread's tables are the frame's `tableBy`, which is one default at all coins as
long as the list is too short for the play to reach the tree, and the switch's table depends on a
coin, that field is false: there `switch_plays` holds and says nothing. This is by reading: Lean has
not checked it. (4) AND (5) ARE NOT FIELDS OF `K2Seated` AND HAVE NO PAYER: (5) says of the prover's
EARLIER tables what the frame's test on a message's shape says of each as it is sent, and of the
numbers' list what the format's test on the plan may say: neither road is typed. ONE DEBT OF FIVE:
nothing on `Accepted`, `Behind`, `Exchange`, `RidesPast`. IT IS ON RETURNING AND ON WHICH TABLES ARE
AT HAND: nothing on what a table holds, nor on whether the verifier's step says yes. That nothing of
the member stops is a premise of the debt and is not spent: the part's stops never stop, by its
text. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Plays
import Johnson.Desc.ProofFile.Honest.K2.Seated
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.Fill
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.K2.Honest.Returns.ItemsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Oracle itemOf Place)
open VerifiableInference.Desc.K2.Honest (Sizes)
open VerifiableInference.Desc.K2.Honest.Returns (filter_cut)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds)

variable {V W X W₀ Rc Xi Tr : Type}

/-- Two steps whose stops never stop, whose moves say messages of the rounds' shapes: what `play`
returns. -/
theorem play_two_is (nm : String) (ad : Addr) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (hb : ∀ f o, bad f o = none)
    (hh : ∀ f o, hid f o = none) (mv₁ mv₂ : Move Unit W X) (x₁ x₂ : Fmt.Drawn) (m : Mid W X)
    (a₁ a₂ : Sending) (h₁ : mv₁.say () ⟨m.seen, m.opened⟩ m.st = .ok a₁) (f₁ : a₁.fits d₁ o₁ = true)
    (h₂ : mv₂.say () ⟨m.seen ++ [⟨a₁.vals.map Said.got, x₁⟩], m.opened⟩
      { m.st.hears x₁ with own := mv₁.hand (m.st.hears x₁) } = .ok a₂)
    (f₂ : a₂.fits d₂ o₂ = true) :
    ∃ m' : Mid W X, play [⟨nm, ad, d₁, o₁, bad, hid, 0, false, some mv₁⟩,
        ⟨nm, ad, d₂, o₂, bad, hid, 1, true, some mv₂⟩] [x₁, x₂] [] m =
      .ok ([⟨nm, ad.place, ad.part, true, a₁.vals.map Said.got, a₁.tables.map some, x₁⟩,
        ⟨nm, ad.place, ad.part, true, a₂.vals.map Said.got, a₂.tables.map some, x₂⟩], m') ∧
      m'.st.input = m.st.input := by
  have s₁ := stop_none (s := (⟨nm, ad, d₁, o₁, bad, hid, 0, false, some mv₁⟩ : Step W X)) hb hh
  have s₂ := stop_none (s := (⟨nm, ad, d₂, o₂, bad, hid, 1, true, some mv₂⟩ : Step W X)) hb hh
  refine ⟨⟨{ (({ m.st.hears x₁ with own := mv₁.hand (m.st.hears x₁) } : State W X).hears x₂) with
      own := mv₂.hand (({ m.st.hears x₁ with own := mv₁.hand (m.st.hears x₁) } :
        State W X).hears x₂) }, m.loc ++ [x₁] ++ [x₂],
    m.seen ++ [⟨a₁.vals.map Said.got, x₁⟩] ++ [⟨a₂.vals.map Said.got, x₂⟩], m.opened⟩, ?_, rfl⟩
  simp [play, Step.tell, Step.hear, Mid.shown, s₁, s₂, h₁, h₂, f₁, f₂, Except.bind, Except.map]

/-- A table shows what it shows. -/
theorem same_self (t : Table) : t.same t = true := by
  simp [Table.same]

/-- The lot's own sender's tables return, with the trees' shapes. -/
theorem core_tables_ok (table : FreshTable) (codes : OnBytes.Codes)
    (sent : Array OnBytes.OracleNotice) (fresh : Option (Nat × Nat))
    (D : Nat → Nat → Nat → Cb.Gl.E) (c : Cs (sendingDue codes sent fresh))
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) :
    ∃ Tb, (coreSender table).tables codes sent fresh D c = .ok Tb ∧
      Tb.map (fun t => (t.logLength, t.words)) = treeShapes codes sent := by
  obtain ⟨R, hR⟩ := rowsAll_returns hf table D c
  unfold coreSender
  dsimp only
  rw [hR]
  refine ⟨_, rfl, ?_⟩
  rw [List.map_map]
  exact zipIdx_fst (fun t : OnBytes.TreeShape => (t.logN, t.mainWidth + t.maskWidth)) _ 0

/-- Its answers return, as many as the sending has. -/
theorem core_answers_ok (table : FreshTable) (codes : OnBytes.Codes)
    (sent : Array OnBytes.OracleNotice) (fresh : Option (Nat × Nat))
    (D : Nat → Nat → Nat → Cb.Gl.E) (c : Cs (sendingDue codes sent fresh))
    (drawn : List Fmt.Ext3)
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) :
    ∃ A, (coreSender table).answers codes sent fresh D c drawn = .ok A ∧
      A.length = (sendingPar codes sent).answers := by
  obtain ⟨R, hR⟩ := rowsAll_returns hf table D c
  unfold coreSender
  dsimp only
  rw [hR]
  refine ⟨_, rfl, ?_⟩
  rw [List.length_map, Johnson.Prover.Send.length_answers]

/-- **The part's two moves at the lot's own sender return.** t: the state in front; t': behind the
first challenge. -/
theorem moves_say (table : FreshTable) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (c : SwitchCoins Z others k carries) (t t' : State SwitchAsk Unit) (x₁ : Fmt.Drawn)
    (hi : t'.input = t.input) (hh : t'.heard = t.heard ++ [x₁])
    (hs : Z.serves = true) (hr : Z.roomy = true)
    (hf : K1.sendFits (sendingPar Z.codes (switchSent Z others))
      (rideOf (switchSent Z others) (switchFresh Z others k)) = true)
    (h1 : d₁.items.filter (· != .root) = [])
    (h2 : o₁.map (fun o => (o.logLength, o.words)) = treeShapes Z.codes (switchSent Z others))
    (h3 : d₂.items.filter (· != .root) =
      List.replicate (sendingPar Z.codes (switchSent Z others)).answers .answer)
    (h4 : o₂ = [])
    (hl : (t.input.left t.heard (Stretch.carried carries c.2.2)).toOption.isSome = true) :
    ∃ (Tb : List Table) (A : List Cb.Gl.E),
      (∀ s, (moveOne (coreSender table) Z others k carries).say c s t = .ok ⟨[], Tb⟩) ∧
      Tb.map (fun t => (t.logLength, t.words)) = treeShapes Z.codes (switchSent Z others) ∧
      (⟨[], Tb⟩ : Sending).fits d₁ o₁ = true ∧
      (∀ s, (moveTwo (coreSender table) Z others k carries).say c s t' =
        .ok ⟨A.map .answer, []⟩) ∧
      (⟨A.map .answer, []⟩ : Sending).fits d₂ o₂ = true := by
  have hD : ∃ D, switchRowsAt Z carries c.2.2 t 0 = .ok D := by
    unfold switchRowsAt
    simp only [Nat.sub_zero, List.take_length]
    cases e : t.input.left t.heard (Stretch.carried carries c.2.2) with
    | ok L => exact ⟨_, rfl⟩
    | error s =>
      rw [e] at hl
      cases hl
  obtain ⟨D, hD⟩ := hD
  have hD' := (switchRowsAt_again Z carries c.2.2 t t' x₁ hi hh).trans hD
  obtain ⟨Tb, hTb, sTb⟩ := core_tables_ok table Z.codes (switchSent Z others)
    (switchFresh Z others k) D c.1 hf
  obtain ⟨A, hA, lA⟩ := core_answers_ok table Z.codes (switchSent Z others)
    (switchFresh Z others k) D c.1 ((t'.lately 1).flatMap (·.elems)) hf
  refine ⟨Tb, A, fun s => ?_, sTb, ?_, fun s => ?_, ?_⟩
  · show (if !Z.serves then _ else if !Z.roomy then _ else
      (switchRowsAt Z carries c.2.2 t 0).bind _) = _
    rw [hs, hr, hD]
    show ((coreSender table).tables Z.codes (switchSent Z others) (switchFresh Z others k) D
      c.1).map _ = _
    rw [hTb]
    rfl
  · unfold Sending.fits
    rw [h1, h2, sTb]
    simp
  · show (switchRowsAt Z carries c.2.2 t' 1).bind _ = _
    rw [hD']
    show ((coreSender table).answers Z.codes (switchSent Z others) (switchFresh Z others k) D c.1
      _).map _ = _
    rw [hA]
    rfl
  · unfold Sending.fits
    rw [h3, h4, ← lA]
    have : (A.map Said.answer).map (fun v => itemOf v.got) =
        List.replicate A.length Fmt.Item.answer := by
      rw [List.map_map]
      exact List.eq_replicate_iff.2 ⟨by rw [List.length_map], fun b hb => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hb
        rfl⟩
    rw [this]
    simp

variable {S' Cl : Type}

/-- **What `play` returns over the half's two rounds.** Tb: what the part's first move says. -/
theorem half_played (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (b : Block S' Cl) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (hb : b.rounds.zip b.oracles = [(d₁, o₁), (d₂, o₂)]) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (switchHalf (X := X) (coreSender freshTable) D readers closing p).parts)
    (x₁ x₂ : Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (h1 : d₁.items.filter (· != .root) = [])
    (h2 : o₁.map (fun o => (o.logLength, o.words)) =
      treeShapes p.sizes.codes (switchSent p.sizes p.others))
    (h3 : d₂.items.filter (· != .root) =
      List.replicate (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers .answer)
    (h4 : o₂ = [])
    (hl : (closing p (D m.st.input.x) (readers m.st.input) m.st.heard
      (Stretch.carried p.carries c.1.2.2)).toOption.isSome = true) :
    ∃ (Tb : List Table) (g : List Fmt.ItemValue) (m' : Mid (Local W₀ Rc Xi Tr) X),
      play ((switchHalf (X := X) (coreSender freshTable) D readers closing p).steps b v c)
        [x₁, x₂] [] m = .ok ([⟨b.name, b.place, 0, true, [], Tb.map some, x₁⟩,
          ⟨b.name, b.place, 0, true, g, [], x₂⟩], m') ∧
      m'.st.input = m.st.input ∧
      Tb.map (fun t => (t.logLength, t.words)) =
        treeShapes p.sizes.codes (switchSent p.sizes p.others) ∧
      ∀ s, (moveOne (coreSender freshTable) p.sizes p.others p.foldVars p.carries).say c.1 s
        ⟨switchWit D readers closing p m.st.input, m.st.heard, ()⟩ = .ok ⟨[], Tb⟩ := by
  obtain ⟨Tb, A, s₁, sh, f₁, s₂, f₂⟩ := moves_say freshTable p.sizes p.others p.foldVars p.carries
    d₁ d₂ o₁ o₂ c.1 (m.st.narrow (switchWit D readers closing p) fun _ => ())
    (State.narrow (switchWit D readers closing p) (fun _ => ())
      { m.st.hears x₁ with own := (m.st.hears x₁).own }) x₁ rfl rfl hs hr hf h1 h2 h3 h4 hl
  rw [half_steps (coreSender freshTable) D readers closing p b (d₁, o₁) (d₂, o₂) hb v c,
    steps_two _ (lift_moves (coreSender freshTable) p.sizes p.others p.foldVars p.carries
      (fun _ => ()) (switchWit D readers closing p) (fun _ => ()) fun x _ => x)]
  obtain ⟨m', hy, hi⟩ := play_two_is b.name ⟨b.place, 0⟩ d₁ d₂ o₁ o₂ (fun _ _ => none)
    (fun _ _ => v.bind fun _ => none) (fun _ _ => rfl)
    (fun f o => by
      cases v with
      | none => rfl
      | some w => rfl)
    ⟨fun _ => ((moveOne (coreSender freshTable) p.sizes p.others p.foldVars p.carries).lift
      (switchWit D readers closing p) (fun _ => ()) fun x _ => x).say c.1, _⟩
    ⟨fun _ => ((moveTwo (coreSender freshTable) p.sizes p.others p.foldVars p.carries).lift
      (switchWit D readers closing p) (fun _ => ()) fun x _ => x).say c.1, _⟩
    x₁ x₂ m ⟨[], Tb⟩ ⟨A.map .answer, []⟩ (s₁ ⟨m.seen, m.opened⟩) f₁
    (s₂ ⟨m.seen ++ [⟨([] : List Said).map Said.got, x₁⟩], m.opened⟩) f₂
  exact ⟨Tb, _, m', hy, hi, sh, s₁⟩

/-- What the book lends a row of one part is what it lends the part. -/
theorem lendRow_one (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) (P : Part V W X) (c : RowCoins [P])
    (h : lendRow Bk rows look a [P] 0 = .ok c) : lendPart Bk rows look ⟨a, 0⟩ P = .ok c.1 := by
  rw [lendRow] at h
  cases e : lendPart Bk rows look ⟨a, 0⟩ P with
  | error s => simp [e, Except.mapError, Except.bind] at h
  | ok c₀ =>
    simp [e, Except.mapError, Except.bind, lendRow, Except.map] at h
    rw [← h]

/-- The book lends a lifted part what it lends the part: it reads the three counts alone. -/
theorem lendPart_lift {V' W' Y : Type} (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (ad : Addr) (P : Part V' W' Y) (see : V → V') (wit : W → W')
    (get : X → Y) (set : X → Y → X) :
    (lendPart Bk rows look ad (P.lift see wit get set) :
      Except String (Handed P.takes P.spends P.carries)) = lendPart Bk rows look ad P := by
  unfold lendPart
  dsimp only [Part.lift]
  generalize (look ad).2.cut ⟨0, 0⟩ P.takes = z
  cases z <;> rfl

/-- What the book lends the half's row is what it lends the part. -/
theorem lent_part (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace)
    (c : RowCoins (switchHalf (X := X) Sd D readers closing p).parts)
    (h : lendRow Bk rows look a (switchHalf (X := X) Sd D readers closing p).parts 0 = .ok c) :
    lendPart Bk rows look ⟨a, 0⟩ (switchPart Sd p.sizes p.others p.foldVars p.carries) =
      .ok c.1 :=
  (lendPart_lift Bk rows look ⟨a, 0⟩ (switchPart Sd p.sizes p.others p.foldVars p.carries)
    (fun _ => ()) (switchWit D readers closing p) (fun _ => ()) fun (x : X) _ => x).symm.trans
    (lendRow_one Bk rows look a _ c h)

/-- The columns that the kind's second round reads are laid, where each tree that it opens is at
hand with the width that the round states. -/
theorem old_cols (q : P2) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (x₁ x₂ : Fmt.Drawn)
    (h : ∀ r ∈ q.read, ∃ u, tree (.own r.1) = some u ∧ u.2.words = r.2.2) :
    ∃ cols, fillCols (readsOf chain ft stored tree (rounds q) [x₁, x₂]) [] = .ok cols := by
  refine fillCols_ok _ fun r hr => ?_
  simp only [rounds, readsOf, List.flatMap_nil, List.nil_append, List.append_nil,
    List.flatMap_map, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨rr, hrr, x, _, rfl⟩ := hr
  obtain ⟨u, hu, hw⟩ := h rr hrr
  refine ⟨u.2.col x, ?_, ?_⟩
  · show (tree (.own rr.1)).map _ = _
    rw [hu]
    rfl
  · show (List.ofFn _).length = rr.2.2
    rw [List.length_ofFn, hw]

/-- The table number j of the switch's sending, where the book lends the part c₀ and its first move
says the tables Tb. -/
theorem tableAt_is (Bk : ProverCoinCounts) (chain : Nat) (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn)
    (c₀ : SwitchCoins p.sizes p.others p.foldVars p.carries) (Tb : List Table)
    (hc : lendPart Bk (Bk.rowsOf chain) (k.look chain) ⟨p.place, 0⟩
      (switchPart Sd p.sizes p.others p.foldVars p.carries) = .ok c₀)
    (hs : (moveOne Sd p.sizes p.others p.foldVars p.carries).say c₀ ⟨[], none⟩
      ⟨switchWit D readers closing p w, h, ()⟩ = .ok ⟨[], Tb⟩) (j : Nat) :
    switchTableAt Bk chain Sd D readers closing p k w h j = (Tb[j]?).getD noTable := by
  unfold switchTableAt switchSays
  rw [hc]
  show (((moveOne Sd p.sizes p.others p.foldVars p.carries).say c₀ ⟨[], none⟩
    ⟨switchWit D readers closing p w, h, ()⟩).toOption.bind (·.tables[j]?)).getD noTable = _
  rw [hs]
  rfl

/-- A source that is new behind a member is one of the member's own trees. -/
theorem mem_fresh {Bk : ProverCoinCounts} {Pb : Type} (T : Thread Bk S' Cl V W X Pb) {b : Nat}
    {blk : Block S' Cl} (hb : T.bs[b]? = some blk) (σ : Fmt.TreeSource) (h : σ ∈ T.fresh b) :
    ∃ j, j < (blk.oracles.flatMap id).length ∧ σ = .own (treesTo T.bs b + j) := by
  unfold Thread.fresh at h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  have h3 : σ ∉ T.hand b := by simpa using h2
  unfold Thread.hand at h1 h3
  rcases List.mem_append.1 h1 with ht | ho
  · exact absurd (List.mem_append_left _ ht) h3
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 ho
    have hn' := List.mem_range.1 hn
    rw [treesTo_succ hb] at hn'
    have h4 : ¬ n < treesTo T.bs b := fun hlt =>
      h3 (List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 hlt, rfl⟩))
    exact ⟨n - treesTo T.bs b, by omega, by congr 1; omega⟩

/-- What the kind's two rounds state beside roots: nothing; the numbers' answers. -/
theorem rounds_items (q : P2) (d₁ d₂ : Fmt.DeclaredRound) (h : rounds q = [d₁, d₂]) :
    d₁.items.filter (· != .root) = [] ∧
      d₂.items.filter (· != .root) = List.replicate q.answers .answer := by
  simp only [rounds, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  constructor
  · show (Fmt.Entry.cut _).filter (· != .root) = []
    rw [filter_cut]
    show List.replicate 0 Fmt.Item.answer ++
      List.replicate ((32 * q.roots - 24 * 0 - 32 * q.roots) / 24) Fmt.Item.e = []
    have z : (32 * q.roots - 24 * 0 - 32 * q.roots) / 24 = 0 := by omega
    rw [z]
    rfl
  · show (Fmt.Entry.cut _).filter (· != .root) = _
    rw [filter_cut]
    show List.replicate q.answers Fmt.Item.answer ++
      List.replicate ((24 * q.answers - 24 * q.answers - 32 * 0) / 24) Fmt.Item.e = _
    have z : (24 * q.answers - 24 * q.answers - 32 * 0) / 24 = 0 := by omega
    rw [z]
    exact List.append_nil _

/-- **THE DEBT "IT PLAYS" AT THE SWITCH's OWN MEMBER.** -/
theorem switch_plays {Bk : ProverCoinCounts} {Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat) (blk : Block S Cl)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace) (q : P2)
    (before : S → Except String S) (after : S → S → Except String S) (clause : S → S → Prop)
    (seg : Nat) (iCarry iPin iCarried iSample iPosition : T.ι) (toP : T.P → Pp)
    (toW : T.Wt → VerifiableInference.Desc.Wit (VerifiableInference.Desc.Sound.CellsQ rows cols)
      Tok VerifiableInference.Desc.Sound.MsgT)
    (Dof : Local W₀ Rc Xi Tr → VerifiableInference.Desc.Sound.MgData Xi' Pp Tok rows cols nR Xp)
    (Mg₀ : VerifiableInference.Desc.First.Meaning Pp (VerifiableInference.Desc.Wit
      (VerifiableInference.Desc.Sound.CellsQ rows cols) Tok VerifiableInference.Desc.Sound.MsgT))
    (Q : K2Seated T b blk (coreSender freshTable) D readers (lotClosingAt lay segs) p q before
      after clause seg iCarry iPin iCarried iSample iPosition toP toW Dof Mg₀)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (hS : q.sent.map (fun o => (o.logLength, o.words)) =
      treeShapes p.sizes.codes (switchSent p.sizes p.others))
    (hA : (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers = q.answers)
    (hc : closingOk freshTable (segs.take p.link) p = true)
    (hv : ∀ w, T.valid w → publicOk D lay p (segs.take p.link) w.x = true)
    (hW : ∀ r ∈ q.read, ∀ k s m E, Thr T b k s m E →
      (T.tableAt (.own r.1) k m).2.words = r.2.2) :
    Plays T b := by
  intro blk' hblk' k s m E ds l hT hd _ hl
  rw [Q.here] at hblk'
  cases hblk'
  have hT' := hT
  obtain ⟨hHand, hFit, -, -, hMade, -, hval⟩ := hT
  obtain ⟨-, -, hsent, hTight, -⟩ := hMade
  obtain ⟨c, hlend, el⟩ := steps_one_half Q.half hl
  obtain ⟨d₁, d₂, hq⟩ : ∃ d₁ d₂, rounds q = [d₁, d₂] := ⟨_, _, rfl⟩
  rw [Q.rounds, hq] at hd
  obtain ⟨x₁, x₂, rfl, -⟩ := draws_two d₁ d₂ ds hd
  obtain ⟨Tb, g, m', hy, hi, sh, hsay⟩ := half_played D readers (lotClosingAt lay segs) p blk d₁ d₂
    q.sent [] (by rw [Q.rounds, Q.oracles, hq]; rfl) (T.φ.sees m.st.input) c x₁ x₂ m hs hr hf
    (rounds_items q d₁ d₂ hq).1 hS (by rw [hA]; exact (rounds_items q d₁ d₂ hq).2) rfl
    ((returnsLaw D readers lay segs p hc m.st.input m.st.heard c.1.2.2).trans (hv _ hval))
  rw [← el] at hy
  have hlen : Tb.length = q.roots := by
    have := congrArg List.length (sh.trans hS.symm)
    rw [List.length_map, List.length_map] at this
    exact this.trans Q.roots
  obtain ⟨cols', hcols⟩ := old_cols q T.chain T.ft
    (E.add [⟨blk.name, blk.place, 0, true, [], Tb.map some, x₁⟩,
      ⟨blk.name, blk.place, 0, true, g, [], x₂⟩]).stored
    (E.add [⟨blk.name, blk.place, 0, true, [], Tb.map some, x₁⟩,
      ⟨blk.name, blk.place, 0, true, g, [], x₂⟩]).tree x₁ x₂ (fun r hr' => by
      have hin : Fmt.TreeSource.own r.1 ∈ T.hand b :=
        List.mem_append_right _ (List.mem_map.2 ⟨r.1, List.mem_range.2 (Q.opens r hr'), rfl⟩)
      have ha := hHand.2 _ hin
      unfold Thread.handAt at ha
      cases hu : E.tree (.own r.1) with
      | none =>
        rw [hu] at ha
        cases ha
      | some u =>
        rw [hu] at ha
        refine ⟨u, Env.add_keeps hTight _ hu, ?_⟩
        simp only [Option.any_some, Table.same, Bool.and_eq_true, beq_iff_eq] at ha
        exact ha.2.1.2.trans (hW r hr' k s m E hT'))
  refine ⟨_, cols', ⟨⟨l, hl, hy⟩, by rw [Q.rounds]; exact hcols⟩, ?_⟩
  intro σ hσ
  obtain ⟨j, hj, rfl⟩ := mem_fresh T Q.here σ hσ
  have hj' : j < q.roots := by
    rw [Q.oracles] at hj
    simpa [Q.roots] using hj
  have hjT : j < Tb.length := hlen ▸ hj'
  have hheard : m'.st.heard = m.st.heard ++ [x₁, x₂] := play_heard _ _ _ _ _ hy
  have htab : T.tableAt (.own (treesTo T.bs b + j)) k m' = (p.place, Tb[j]) := by
    unfold Thread.tableAt
    rw [Q.table j hj', Q.fixed j hj', hi, hheard, ← T.heard_length hFit, List.take_left,
      tableAt_is Bk T.chain (coreSender freshTable) D readers (lotClosingAt lay segs) p k
        m.st.input m.st.heard c.1 Tb (Q.place ▸ lent_part Bk _ _ blk.place _ D readers _ p c hlend)
        (hsay ⟨[], none⟩) j, List.getElem?_eq_getElem hjT]
    rfl
  unfold Thread.handAt
  rw [htab]
  have htree : (E.add [⟨blk.name, blk.place, 0, true, [], Tb.map some, x₁⟩,
      ⟨blk.name, blk.place, 0, true, g, [], x₂⟩]).tree (.own (treesTo T.bs b + j)) =
      some (blk.place, Tb[j]) := by
    show (if treesTo T.bs b + j < E.sent then _ else
      ((tablesOf _)[treesTo T.bs b + j - E.sent]?).bind id) = _
    rw [hsent, if_neg (by omega), Nat.add_sub_cancel_left]
    simp [tablesOf, hjT]
  show (Option.any _ ((E.add _).tree _)) = true
  rw [htree]
  simp [Q.place, same_self]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.play_two_is
#print axioms ProofFile.Honest.K2.Law.same_self
#print axioms ProofFile.Honest.K2.Law.core_tables_ok
#print axioms ProofFile.Honest.K2.Law.core_answers_ok
#print axioms ProofFile.Honest.K2.Law.moves_say
#print axioms ProofFile.Honest.K2.Law.half_played
#print axioms ProofFile.Honest.K2.Law.lendRow_one
#print axioms ProofFile.Honest.K2.Law.lendPart_lift
#print axioms ProofFile.Honest.K2.Law.lent_part
#print axioms ProofFile.Honest.K2.Law.old_cols
#print axioms ProofFile.Honest.K2.Law.tableAt_is
#print axioms ProofFile.Honest.K2.Law.mem_fresh
#print axioms ProofFile.Honest.K2.Law.rounds_items
#print axioms ProofFile.Honest.K2.Law.switch_plays
