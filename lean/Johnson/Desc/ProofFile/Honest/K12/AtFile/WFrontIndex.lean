-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontIndex.lean: the messages of the first sending at the end
of the first chain's fold, under the head AtMgA at the older hash. One of them is the index masks'
message: the number of it is the premise IndexIs, which WFrontFit.lean spends.

  IndexIs          the record's number of the index masks' message is that of the first sending's last
                   message: a name for what indexMasks_at_end (WFrontEndIs.lean) pays
  MessagesStay     the codes stay, no message goes, its shape stays, and a sampled message keeps mark,
                   pad, rows and the mark of being spent
  groundKeeps_messages, stKeeps_messages   it meets all that the library asks of a relation on the
                   statement
  joinAll_well, decideSend_new   joining the sending's group; the messages behind a sending
  first_sending    behind the first sending: WellSampled, and message k with its shape, sampled where
                   it counts an answer
  sentWell_at_end  a message of the first sending that counts an answer has its count and the public
                   pad at the chain's end

Limits.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontWell
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontMembers
import Johnson.IMR.FirstUnder
import Johnson.IMR.GroupAt
import Johnson.IMR.FoldTools
import Johnson.IMR.KeptJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (GroundKeeps By ok)
open VerifiableInference.Desc.K13.Law (StKeeps)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- **The premise from the thread's letter.** The record's number of the index masks' message is that
of the last message of the first sending. -/
def IndexIs (Zp : ProofFile.Pub) (s : S) : Prop :=
  s.out.indexMasks =
    (VerifiableInference.Desc.K1.firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1

/-- **No message goes, its shape stays, and a sampled message keeps mark, pad and sample rows.** -/
def MessagesStay (A B : Statement) : Prop :=
  B.codes = A.codes ∧ ∀ (o : ℕ) (x : OnBytes.Oracle), A.oracles[o]? = some x →
    ∃ y : OnBytes.Oracle, B.oracles[o]? = some y ∧ y.shape = x.shape ∧
      (x.sampled = true → y.sampled = true ∧ y.pad = x.pad ∧ y.sampleRows = x.sampleRows ∧
        y.spentAsMask = x.spentAsMask)

theorem messages_refl (A : Statement) : MessagesStay A A :=
  ⟨rfl, fun _ x hx => ⟨x, hx, rfl, fun h => ⟨h, rfl, rfl, rfl⟩⟩⟩

theorem messages_trans {A B C : Statement} (h : MessagesStay A B) (k : MessagesStay B C) :
    MessagesStay A C := by
  refine ⟨k.1.trans h.1, fun o x hx => ?_⟩
  obtain ⟨y, hy, e1, e2⟩ := h.2 o x hx
  obtain ⟨z, hz, f1, f2⟩ := k.2 o y hy
  refine ⟨z, hz, f1.trans e1, fun hs => ?_⟩
  obtain ⟨a, b, c, e⟩ := e2 hs
  obtain ⟨a', b', c', e'⟩ := f2 a
  exact ⟨a', b'.trans b, c'.trans c, e'.trans e⟩

/-- One message is turned: it keeps its shape, and what it holds if it is sampled. -/
theorem messages_modify (S : Statement) (o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, S.oracles[o]? = some x → (f x).shape = x.shape ∧
      (x.sampled = true → (f x).sampled = true ∧ (f x).pad = x.pad ∧
        (f x).sampleRows = x.sampleRows ∧ (f x).spentAsMask = x.spentAsMask)) :
    MessagesStay S { S with oracles := S.oracles.modify o f } := by
  refine ⟨rfl, fun j x hx => ?_⟩
  show ∃ y, (S.oracles.modify o f)[j]? = some y ∧ _
  by_cases c : o = j
  · subst c
    exact ⟨f x, by rw [Array.getElem?_modify, if_pos rfl, hx]; rfl, (hf x hx).1, (hf x hx).2⟩
  · exact ⟨x, by rw [Array.getElem?_modify, if_neg c]; exact hx, rfl, fun h => ⟨h, rfl, rfl, rfl⟩⟩

theorem messages_same {A B : Statement} (hc : B.codes = A.codes) (ho : B.oracles = A.oracles) :
    MessagesStay A B :=
  ⟨hc, fun _ x hx => ⟨x, by rw [ho]; exact hx, rfl, fun h => ⟨h, rfl, rfl, rfl⟩⟩⟩

theorem messages_sent (S : Statement) (sent : Array OracleNotice) :
    MessagesStay S (stSent S sent) := by
  refine ⟨rfl, fun o x hx => ⟨x, ?_, rfl, fun h => ⟨h, rfl, rfl, rfl⟩⟩⟩
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 hx
  show (S.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? = some x
  rw [Array.getElem?_append_left hlt]
  exact hx

theorem messages_closeLedgers : ∀ (l : List ℕ) (S : Statement), MessagesStay S (closeLedgers S l)
  | [], S => messages_refl S
  | a :: l, S => by
    have e : closeLedgers S (a :: l) = closeLedgers { S with oracles := S.oracles.modify a fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } l := rfl
    rw [e]
    exact messages_trans (messages_modify S a
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      fun _ _ => ⟨rfl, fun h => ⟨h, rfl, rfl, rfl⟩⟩) (messages_closeLedgers l _)

/-- **The ground's functions keep it.** -/
theorem groundKeeps_messages : GroundKeeps MessagesStay where
  refl := messages_refl
  trans := messages_trans
  newGroup := by
    intro L d d' code maskCode n h
    unfold VerifiableInference.Desc.Ground.newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact messages_same rfl rfl
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold VerifiableInference.Desc.Ground.recvP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact messages_sent _ _
    · cases h
  admit := by
    intro L d d' o rows h
    unfold VerifiableInference.Desc.Ground.admitP at h
    by_cases c : ok (VerifiableInference.Desc.Ground.admitL d.st o rows) = true
    · rw [if_pos c] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, places, _, rfl⟩ := h
      simp only [ok, VerifiableInference.Desc.Ground.admitL, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true] at c
      obtain ⟨_, _, c3, _, _⟩ := c
      rw [hx, OnBytes.Means.has_some] at c3
      exact messages_modify d.st o (fun y => { y with
        sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
        ledger := freshLedger d.st.codes x.shape }) fun y hy => by
        obtain rfl := Option.some.inj (hy.symm.trans hx)
        refine ⟨rfl, fun hs => ?_⟩
        simp [hs] at c3
    · rw [if_neg c] at h
      cases h
  join := by
    intro L d d' g o kept h
    unfold VerifiableInference.Desc.Ground.joinP at h
    split at h
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
      refine ⟨rfl, fun j x hx => ?_⟩
      exact (messages_modify d.st o (fun x => { x with groups := x.groups ++ [g] })
        fun _ _ => ⟨rfl, fun h => ⟨h, rfl, rfl, rfl⟩⟩).2 j x hx
    · cases h
  addRow := by
    intro L d d' g row h
    unfold VerifiableInference.Desc.Ground.addRowP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact messages_same rfl rfl
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold VerifiableInference.Desc.Ground.takeMaskP at h
    split at h
    · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.1 h
      obtain rfl : _ = d' := congrArg Prod.snd e
      exact messages_modify d.st o _ fun _ _ => ⟨rfl, fun h => ⟨h, rfl, rfl, rfl⟩⟩
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact messages_closeLedgers [o] d.st
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold VerifiableInference.Desc.Ground.spendAsMaskP at h
    split at h
    · rename_i c
      obtain rfl := Option.some.inj h
      simp only [ok, VerifiableInference.Desc.Ground.spendAsMaskL, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true] at c
      obtain ⟨_, c2, _⟩ := c
      exact messages_modify d.st o (fun x => { x with spentAsMask := true }) fun x hx => by
        rw [hx, OnBytes.Means.has_some] at c2
        refine ⟨rfl, fun hs => ?_⟩
        simp [hs] at c2
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold VerifiableInference.Desc.Ground.adoptP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact messages_sent _ _
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold VerifiableInference.Desc.Ground.elsewhereP at h
    by_cases c : ok (VerifiableInference.Desc.Ground.elsewhereL d.st mine other theirs) = true
    · rw [if_pos c] at h
      obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [ok, VerifiableInference.Desc.Ground.elsewhereL, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true] at c
      obtain ⟨_, _, _, c4, _⟩ := c
      exact messages_modify d.st mine (fun x => { x with
        sampled := true, sampleRows := y.sampleRows.map (·.renamed mine), pad := y.pad })
        fun x hx => by
        rw [hx, OnBytes.Means.has_some] at c4
        refine ⟨rfl, fun hs => ?_⟩
        simp [hs] at c4
    · rw [if_neg c] at h
      cases h

/-- **The sentence meets all that the library asks of a relation on the statement.** -/
theorem stKeeps_messages : StKeeps MessagesStay where
  ground := groundKeeps_messages
  begun := by
    intro T g G
    exact ⟨(messages_closeLedgers G.members.toList T).1, fun o x hx =>
      (messages_closeLedgers G.members.toList T).2 o x hx⟩
  row := by
    intro lay im o n lin T r os' h
    obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, l, hl, c, l', ht, rfl, rfl⟩ :=
      (VerifiableInference.Desc.First.Pend.pendingRowO_iff lay im o n lin T.oracles _ _).1 h
    exact messages_modify T im (fun x => { x with ledger := some l' })
      fun _ _ => ⟨rfl, fun h => ⟨h, rfl, rfl, rfl⟩⟩

section Sending
open VerifiableInference.Desc.K1
open OnBytes.Params (ReqMessage)

/-- Joining the group of the sending keeps the sentence. -/
theorem joinAll_well {L : Type} (p : _root_.Desc.Plain.GPar) (g : ℕ) :
    ∀ (l : List (ReqMessage × ℕ)) (d d' : _root_.Desc.Plain.DState L),
      VerifiableInference.Desc.First.Send.joinAll VerifiableInference.Desc.Ground.groundG p g l d =
        some d' → WellStays d.st d'.st
  | [], d, d', h => by
    obtain rfl := Option.some.inj h
    exact fun hA => hA
  | x :: l, d, d', h => by
    simp only [VerifiableInference.Desc.First.Send.joinAll, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨d₁, h1, h2⟩ := h
    exact fun hA => joinAll_well p g l d₁ d' h2 (groundQuiet_well.join _ _ _ _ _ h1 hA)

theorem joinAll_messages {L : Type} (p : _root_.Desc.Plain.GPar) (g : ℕ) :
    ∀ (l : List (ReqMessage × ℕ)) (d d' : _root_.Desc.Plain.DState L),
      VerifiableInference.Desc.First.Send.joinAll VerifiableInference.Desc.Ground.groundG p g l d =
        some d' → MessagesStay d.st d'.st
  | [], d, d', h => by
    obtain rfl := Option.some.inj h
    exact messages_refl _
  | x :: l, d, d', h => by
    simp only [VerifiableInference.Desc.First.Send.joinAll, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨d₁, h1, h2⟩ := h
    exact messages_trans (groundKeeps_messages.join _ _ _ _ _ h1) (joinAll_messages p g l d₁ d' h2)

/-- Behind a sending, message number k of the sending is there with its shape, and it is sampled
where it counts an answer. -/
theorem decideSend_new {L : Type} (P : VerifiableInference.Desc.K1.Par) (owed : Option ℕ)
    (d d' : _root_.Desc.Plain.DState L) (rs : List Fmt.RoundView) (ids : Array ℕ)
    (h : decideSend P owed d rs = .ok (ids, d')) (k : ℕ) (hk : k < (shapesOf P).length) :
    ∃ x : OnBytes.Oracle, d'.st.oracles[d.st.oracles.size + k]? = some x ∧
      x.shape = (shapesOf P)[k] ∧ ((shapesOf P)[k].answers ≠ 0 → x.sampled = true) ∧
      x.spentAsMask = false := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨⟨_, _, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    obtain ⟨ys', -, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
      d.st.oracles.size (answersIn r₂) hf k hk
    refine ⟨wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys', ?_, ?_, ?_, ?_⟩
    · show (_ ++ outs _ _ _ _ _).toArray[_]? = _
      rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
      simpa using hget
    · unfold wr
      split <;> rfl
    · intro h0
      simp [wr, h0]
    · unfold wr
      split <;> rfl

end Sending

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Behind the first sending.** -/
theorem first_sending (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {t₃ : S}
    {R R₃ : List Fmt.RoundView} {C C₃ : List OpenedColumn}
    (f₃ : foldBlocks 0 (cF.blocksInOrder.take 3) (ProofFile.startS Zp pI) R C = .ok (t₃, R₃, C₃)) :
    WellSampled t₃.st ∧ ∀ (k : ℕ) (hk : k < (VerifiableInference.Desc.K1.shapesOf
        (VerifiableInference.Desc.K1.firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp))).length),
      ∃ y : OnBytes.Oracle, t₃.st.oracles[k]? = some y ∧
        y.shape = (VerifiableInference.Desc.K1.shapesOf
          (VerifiableInference.Desc.K1.firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)))[k] ∧
        ((VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
          (VerifiableInference.Desc.K1.gpOf Zp)))[k].answers ≠ 0 →
          y.sampled = true ∧ y.spentAsMask = false) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨t₀, R₀, C₀, f₀⟩ := Meaning.K2.fold_back (k := 2) f₃
  have e0s := Meaning.K2.laid_is_start h.scope h.reads O f₀
  obtain ⟨e, nm, X, hfl, hX, hu⟩ := IM.first_under h.scope h.reads O
  obtain ⟨rs, gs, d⟩ := Meaning.K2.fold_next hfl f₀ f₃
  have hy := hu.2 _ _ _ _ d
  obtain ⟨m, y1, y3⟩ := VerifiableInference.Desc.Keeps.ebind_ok
    (x := (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp) :
      Block S ProofFile.Cl).decide t₀ (rs.take (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first
              (VerifiableInference.Desc.K1.gpOf Zp) : Block S ProofFile.Cl).rounds.length)
        (gs.take (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first
        (VerifiableInference.Desc.K1.gpOf Zp) : Block S ProofFile.Cl).openings)) hy
  have eq3 : t₃.st = m.st := (Johnson.Desc.First.Walk.Tied.openedZeroGives X _ _ m t₃ y3).2.2.1.2.2.1
  have hq : Bs.G₀.first = Zp.first := O.first
  rw [hq] at y1
  obtain ⟨c', d', h1, e1, -⟩ := VerifiableInference.Desc.K1.firstAtS_ok _ _ t₀ m _ _ y1
  obtain ⟨g, d₁, ids, d₂, hng, hds, f₁, own, mine, f₂, hjo⟩ :=
    VerifiableInference.Desc.K1.firstOwn_ok _ _ _ c' _ d' _ h1
  have hB : VerifiableInference.Desc.K1.planOkOwn (VerifiableInference.Desc.K1.firstPar Zp.first
      (VerifiableInference.Desc.K1.gpOf Zp)) = true := by
    obtain ⟨b, hb, hi⟩ := IM.k1_first_plan h.scope h.reads O
    have hp := hi (Johnson.AtFull.Shape.plans_at h b hb)
    rw [hq] at hp
    simp only [VerifiableInference.Desc.K1.firstSegmentOpening, Bool.and_eq_true] at hp
    exact hp.1
  have emp : (VerifiableInference.Desc.K1.stateOf t₀ ()).st.oracles = #[] := by
    show t₀.st.oracles = #[]
    rw [e0s]
    exact Meaning.K2.start_msgs O.pub pI
  have hg₁ : d₁.st.oracles = #[] := by
    have k := hng
    unfold VerifiableInference.Desc.Ground.newGroupP at k
    split at k
    · simp only [Option.some.injEq, Prod.mk.injEq] at k
      obtain ⟨-, rfl⟩ := k
      exact emp
    · cases k
  have w₀ : WellSampled (VerifiableInference.Desc.K1.stateOf t₀ ()).st := fun o y hy' _ => by
    rw [emp] at hy'
    simp at hy'
  have w₁ := groundQuiet_well.newGroup _ _ _ _ _ hng w₀
  have w₂ := decideSend_well _ hB _ _ _ _ _ hds w₁
  have hj₂ : WellSampled d'.st ∧ MessagesStay d₂.st d'.st := by
    unfold VerifiableInference.Desc.First.Send.joinOwnP at hjo
    split at hjo
    · obtain ⟨d₃, h3, e3⟩ := Option.map_eq_some_iff.1 hjo
      obtain rfl : d₃ = d' := (Prod.mk.inj e3).2
      exact ⟨joinAll_well _ _ _ _ _ h3 w₂, joinAll_messages _ _ _ _ _ h3⟩
    · cases hjo
  obtain ⟨w₃, hjoin⟩ := hj₂
  have est : t₃.st = d'.st := eq3.trans e1
  refine ⟨by rw [est]; exact w₃, fun k hk => ?_⟩
  obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := decideSend_new _ _ _ _ _ _ hds k hk
  rw [hg₁] at hy₁
  have hy₀ : d₂.st.oracles[k]? = some y := by simpa using hy₁
  obtain ⟨z, hz, a1, a2⟩ := hjoin.2 k y hy₀
  refine ⟨z, by rw [est]; exact hz, a1.trans hy₂, fun ha => ?_⟩
  obtain ⟨b1, -, -, b2⟩ := a2 (hy₃ ha)
  exact ⟨b1, b2.trans hy₄⟩

/-- **A message of the first sending that counts an answer, at the end of the first chain's fold.** -/
theorem sentWell_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) (k : ℕ)
    (hk : k < (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
      (VerifiableInference.Desc.K1.gpOf Zp))).length)
    (hans : (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
      (VerifiableInference.Desc.K1.gpOf Zp)))[k].answers ≠ 0) :
    ∃ y : OnBytes.Oracle, e₁.st.oracles[k]? = some y ∧
      y.shape = (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp)))[k] ∧ y.sampled = true ∧ y.spentAsMask = false ∧
      y.sampleRows.size = y.shape.answers ∧
      ∃ l, VerifiableInference.Desc.Own.padMade e₁.st.codes y.shape = some l ∧
        y.pad = l.map fun p => (p.part, p.index) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rw [← List.take_append_drop 3 cF.blocksInOrder] at hf
  obtain ⟨t, r₁, c₁, f1, f2⟩ := Johnson.Desc.First.Walk.Tied.fold_split 0 _ _ _ _ _ _ hf
  obtain ⟨hw, hm⟩ := first_sending h f1
  obtain ⟨y, hy, e1, e2⟩ := hm k hk
  obtain ⟨hs, hp⟩ := e2 hans
  have hstay : MessagesStay t.st e₁.st :=
    VerifiableInference.Desc.Keeps.foldBlocks_keeps (By MessagesStay fun s : S => s.st)
      (fun s => messages_refl s.st) (fun _ _ _ h k => messages_trans h k) 0 _
      (fun b hb => Meaning.K2.open_flat (Meaning.K2.seatKeeps_by stKeeps_messages)
        (Meaning.K2.seatBack_by stKeeps_messages) O trivial (fun _ _ _ => trivial) b
        (List.mem_of_mem_drop hb) (Johnson.AtFull.Shape.plans_at h b (List.mem_of_mem_drop hb)))
      t r₁ c₁ _ f2
  obtain ⟨z, hz, f₁, f₂⟩ := hstay.2 k y hy
  obtain ⟨a, b, c, e⟩ := f₂ hs
  obtain ⟨g1, l, hl, g2⟩ := hw k y hy hs
  refine ⟨z, hz, f₁.trans e1, a, e.trans hp, ?_, l, ?_, ?_⟩
  · rw [f₁, c]
    exact g1
  · rw [hstay.1, f₁]
    exact hl
  · rw [b]
    exact g2

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.stKeeps_messages
#print axioms ProofFile.Honest.K12.AtFile.first_sending
#print axioms ProofFile.Honest.K12.AtFile.sentWell_at_end
