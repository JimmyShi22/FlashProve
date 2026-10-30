-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHSends.lean: what a yes of one of the key file's three sendings leaves of the statement, and
what the step of the honest part gives of the rows sent. The laws that the library has at the proof
file's state (Johnson/Desc/ProofFile/Honest/K1/Law/SendAtBlock.lean, ExchangeAtPins.lean), at the
key file's state, where the record in front of the sending is the chain's own.

  `SendYes`: a yes of the kind's decision at the chain's record, whose result has the messages of the
    state behind. `idx_yes`, `msg_yes`, `w_yes`: so at the three sub-protocols.
  `stays_of_yes`: the older messages stay.
  `says_at_yes`: every sample row of a new message says its claim of the held words, where the second
    round's values are the answers at these words.
  `rows_hold_at_yes`: the same in the table's sentence, at any reading that agrees at that message.
  `played_vals_send`, `step_send`: the member's step, unpacked.

Limits. `step_send` asks that the chain's count of messages is the job's first number, and that the
job's data read of what stands in front what was heard alone. Nothing on a thread's items.
-/
import E2E.FirstHSendPlays
import E2E.FirstHFill
import Johnson.RunOne.KeySendIs
import Johnson.Desc.Key.KeyRowAgree
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.ProofFile.Honest.K1.Law.SendAtBlock
import Johnson.Desc.ProofFile.Honest.K1.ScriptLendRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc (Block Place OpenedColumn noDigest)
open VerifiableInference.Desc.Key (FirstState Claim ChainState sendingSeat sendingPar withLoc
  sendIndexMasks sendOwnMessage sendW openRangesGroup Pieces RowHolds)
open VerifiableInference.Desc.K1 (SameMsgs decideSend decideSend_iff)
open VerifiableInference.Desc.Keeps (ebind_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open Johnson.RunOne.KeyKeeps (k1At_sent same_refl same_trans same_size wfGroup_same rows13_same
  lens_lensSt st₁)
open Johnson.Prover.Send (answers behind_at behind_rest held send_says)
open ProofFile.Honest
open ProofFile.Honest.K1

section Yes
variable {β Cl : Type}

/-- **A yes of a sending at the chain's record.** -/
def SendYes (P : VerifiableInference.Desc.K1.Par) (s s' : ChainState β) (r₁ r₂ : Fmt.RoundView) : Prop :=
  ∃ (owed : Option Nat) (d' : _root_.Desc.Plain.DState (Array Nat)) (ids : Array Nat),
    decideSend P owed (withLoc s.d (#[] : Array Nat)) [r₁, r₂] = .ok (ids, d') ∧
      SameMsgs d'.st s'.d.st

theorem idx_yes (one : OneTime) (N : Pieces) (groups : List (List Nat)) {s s' : ChainState β}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (sendIndexMasks (Cl := Cl) one N groups).decide s [r₁, r₂] gs = .ok s') :
    SendYes (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) s s' r₁ r₂ := by
  obtain ⟨m, h1, h2⟩ := ebind_ok h
  obtain ⟨ids, d', hd, e1, _⟩ := k1At_sent h1
  obtain ⟨_, _, h2⟩ := bind_ok h2
  have e : st₁ s' = d'.st := by
    rw [← Except.ok.inj h2]
    exact e1
  refine ⟨_, d', ids, hd, ?_⟩
  show SameMsgs d'.st (st₁ s')
  rw [e]
  exact same_refl _

theorem msg_yes (one : OneTime) (N : Pieces) (groups : List (List Nat)) {s s' : ChainState β}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (sendOwnMessage (Cl := Cl) one N groups).decide s [r₁, r₂] gs = .ok s') :
    SendYes (sendingPar one N.msg "the lookups' own message and what rides with it"
      (Wf.messageOf one.ranges) groups) s s' r₁ r₂ := by
  obtain ⟨m, h1, h2⟩ := ebind_ok h
  obtain ⟨ids, d', hd, e1, _⟩ := k1At_sent h1
  refine ⟨_, d', ids, hd, ?_⟩
  show SameMsgs d'.st (st₁ s')
  rw [← e1]
  exact wfGroup_same h2

theorem w_yes {one : OneTime} {N : Pieces} {sent : Nat} {groups : List (List Nat)}
    {bw : Block (ChainState β) Cl} (hb : sendW one N sent groups = some bw) :
    ∃ msg, linMessageW one.lin = some msg ∧
      ∀ {s s' : ChainState β} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))},
        bw.decide s [r₁, r₂] gs = .ok s' →
        SendYes (sendingPar one N.w "W and what rides with it" msg groups) s s' r₁ r₂ := by
  unfold sendW at hb
  cases hm : linMessageW one.lin with
  | none =>
    rw [hm] at hb
    cases hb
  | some msg =>
    rw [hm] at hb
    have hb' := Option.some.inj hb
    subst hb'
    refine ⟨msg, rfl, fun {s s' r₁ r₂ gs} h => ?_⟩
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
    have hpd : p.d.st = st₁ m₃ :=
      lens_lensSt.get _ _ (VerifiableInference.Desc.K13.part_ok hp)
    have hs' : st₁ s' = o.2.st := by
      rw [← Except.ok.inj hr]
      rfl
    refine ⟨_, d', ids, hd, ?_⟩
    show SameMsgs d'.st (st₁ s')
    rw [hs', ← e1]
    have : st₁ m₃ = m₂.d.st := by
      rw [← e₃]
      rfl
    rw [← this, ← hpd]
    exact rows13_same ho

/-- **The older messages stay.** -/
theorem stays_of_yes {P : VerifiableInference.Desc.K1.Par} {s s' : ChainState β} {r₁ r₂ : Fmt.RoundView}
    (h : SendYes P s s' r₁ r₂) : OlderStay s.d.st s'.d.st := by
  obtain ⟨owed, d', ids, hyes, hsame⟩ := h
  obtain ⟨-, -, rfl⟩ := (decideSend_iff P owed _ d' r₁ r₂ ids).1 hyes
  have hr := behind_rest P (withLoc s.d (#[] : Array Nat)) (VerifiableInference.Desc.K1.seedsOf P r₁)
    (VerifiableInference.Desc.K1.answersIn r₂)
  refine ⟨hsame.1.trans hr.1, fun o x hx => ?_⟩
  have ho : o < s.d.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  have e2 := hsame.2 o
  rw [hr.2.2.2.2.2.1 o ho] at e2
  have e3 : (withLoc s.d (#[] : Array Nat)).st.oracles[o]? = some x := hx
  rw [e3, Option.map_some] at e2
  obtain ⟨x', hx', e'⟩ := Option.map_eq_some_iff.1 e2
  have e4 := Prod.mk.inj e'
  have e5 := Prod.mk.inj e4.2
  exact ⟨x', hx', e4.1, e5.1, e5.2⟩

/-- **EVERY SAMPLE ROW OF A NEW MESSAGE SAYS ITS CLAIM OF THE HELD WORDS.** -/
theorem says_at_yes {P : VerifiableInference.Desc.K1.Par} {s s' : ChainState β} {r₁ r₂ : Fmt.RoundView}
    (h : SendYes P s s' r₁ r₂) (V : ℕ → Johnson.Prover.Send.Rows)
    (hans : r₂.vals = (answers P (stAt P s.d.st.oracles.size) s.d.st.oracles.size
      (held (fun _ _ _ => 0) s.d.st.oracles.size P V)
      (VerifiableInference.Desc.K1.seedsOf P r₁)).map .answer)
    (w : Words GE) (k : ℕ) (hk : k < P.sent.size) (x : OnBytes.Oracle)
    (hx : s'.d.st.oracles[s.d.st.oracles.size + k]? = some x) :
    AllSay rdE s'.d.st x.sampleRows.toList (held w s.d.st.oracles.size P V) := by
  obtain ⟨owed, d', ids, hyes, hsame⟩ := h
  obtain ⟨hasks, _, rfl⟩ := (decideSend_iff P owed _ d' r₁ r₂ ids).1 hyes
  have hans' : r₂.vals = (answers P (stSent s.d.st P.sent) s.d.st.oracles.size
      (held w s.d.st.oracles.size P V) (VerifiableInference.Desc.K1.seedsOf P r₁)).map .answer := by
    exact hans.trans (congrArg (List.map Fmt.ItemValue.answer)
      (part_answers P (withLoc s.d (#[] : Array Nat)) hasks.2.1 w V _))
  have e := hsame.2 (s.d.st.oracles.size + k)
  rw [hx, Option.map_some] at e
  obtain ⟨x', hx', e'⟩ := Option.map_eq_some_iff.1 e.symm
  have hrows : x'.sampleRows = x.sampleRows := (Prod.mk.inj (Prod.mk.inj e').2).2
  intro r hr
  have hr' : r ∈ x'.sampleRows.toList := by
    rw [hrows]
    exact hr
  have h1 := send_says P (withLoc s.d (#[] : Array Nat)) r₁ r₂ w V hans' k x' hk hx' r hr'
  exact (says_sameMsgs hsame r _ (names_new P (withLoc s.d (#[] : Array Nat)) _ _ k hk x' hx' r hr')
    _).2 h1

/-- **THE SAME IN THE TABLE's SENTENCE**, at any reading val that reads message number k of the sending
as the held words do; where the statement behind is in order. -/
theorem rows_hold_at_yes {P : VerifiableInference.Desc.K1.Par} {s s' : ChainState β}
    {r₁ r₂ : Fmt.RoundView} (h : SendYes P s s' r₁ r₂) (V : ℕ → Johnson.Prover.Send.Rows)
    (hans : r₂.vals = (answers P (stAt P s.d.st.oracles.size) s.d.st.oracles.size
      (held (fun _ _ _ => 0) s.d.st.oracles.size P V)
      (VerifiableInference.Desc.K1.seedsOf P r₁)).map .answer)
    (k : ℕ) (hk : k < P.sent.size) (x : OnBytes.Oracle)
    (hx : s'.d.st.oracles[s.d.st.oracles.size + k]? = some x) (hin : InOrder s'.d.st)
    (val : Nat → Part → Nat → E)
    (hv : ∀ part i, readE (val (s.d.st.oracles.size + k) part i) =
      held (fun _ _ _ => 0) s.d.st.oracles.size P V (s.d.st.oracles.size + k) part i) :
    ∀ r ∈ x.sampleRows.toList, RowHolds (fun a b => rdE.val a = rdE.val b) s'.d.st val r := by
  intro r hr
  have hon : RowOn s'.d.st (s.d.st.oracles.size + k) r := hin.samples _ x hx r hr
  have hs := says_at_yes h V hans (fun _ _ _ => 0) k hk x hx r hr
  let w := held (fun _ _ _ => 0) s.d.st.oracles.size P V
  let val₀ : Nat → Part → Nat → E := fun o part i => E.ofTriple (ofE (w o part i))
  have h₀ : RowHolds (fun a b => rdE.val a = rdE.val b) s'.d.st val₀ r := by
    refine (VerifiableInference.Desc.Key.rowHolds_iff_says_of_rowIn rdE s'.d.st _ val₀ r hon).2 ?_
    have e : (fun o pt i => rdE.val (val₀ o pt i)) = w := by
      funext o pt i
      exact toE_ofE _
    rw [e]
    exact hs
  refine (VerifiableInference.Desc.Key.rowHolds_agree rdE hon val₀ val ?_).1 h₀
  intro o ho part i
  have ho' : o = s.d.st.oracles.size + k := by simpa using ho
  subst ho'
  exact (toE_ofE _).trans (hv part i).symm

end Yes

section Step
variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- The second round's values as played are the answers at the rows that the part lays. -/
theorem played_vals_send (J : SendJob W X) (own₀ : X)
    (hh : ∀ w fr fr', fr.heard = fr'.heard → J.data w fr = J.data w fr')
    (c : Cs (dueR J.P J.ride)) (t : State W X) (sn : Seen) (d₀ : Fmt.Drawn) :
    ((answers J.P (stAt J.P J.first) J.first
        (held (fun _ _ _ => 0) J.first J.P (J.rows c sn (t.hears d₀) 1))
        (seedsAt J.P [d₀])).map fun a => ProofFile.Honest.Said.got (.answer (toE a))) =
      (answers J.P (stAt J.P J.first) J.first
        (held (fun _ _ _ => 0) J.first J.P (rowsLaid J own₀ c t.input t.heard))
        (seedsAt J.P [d₀])).map .answer := by
  have e1 : J.rows c sn (t.hears d₀) 1 = rowsLaid J own₀ c t.input t.heard := by
    rw [← rowsLaid_part J own₀ hh c sn (t.hears d₀) 1]
    show rowsLaid J own₀ c t.input ((t.heard ++ [d₀]).take ((t.heard ++ [d₀]).length - 1)) = _
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.take_left]
  rw [e1]
  refine List.map_congr_left fun a ha => ?_
  show Fmt.ItemValue.answer (ofE (toE a)) = _
  rw [answers_canon _ _ _ _ _ a ha]

/-- **THE MEMBER's STEP, UNPACKED.** hch: the thread is the first chain's. hf₀: the statement in front
holds as many messages as the job's first number says. -/
theorem step_send {S : Type} (T : Thread Bk S Cl V W X Pb) (blk : Block S Cl) (J : SendJob W X)
    (own₀ : X) (stOf : S → Statement)
    (hsh : blk.place = J.P.place ∧ blk.rounds = VerifiableInference.Desc.K1.rounds J.P ∧
      blk.oracles = VerifiableInference.Desc.K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (proverSideOfSending J))
    (hf : sendFits J.P J.ride = true) (hch : T.chain = 0)
    (hdata : ∀ w fr fr', fr.heard = fr'.heard → J.data w fr = J.data w fr')
    {k : Coins Bk} {s s' : S} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn} (hf₀ : (stOf s).oracles.size = J.first)
    (hd : drawsFit blk.rounds ds = true) (hS : T.Stepped blk k s m E ds y cols s') :
    ∃ (c : Cs (dueR J.P J.ride)) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c ∧
      blk.decide s [r₁, r₂] gs = .ok s' ∧
      r₂.vals = (answers J.P (stAt J.P (stOf s).oracles.size) (stOf s).oracles.size
        (held (fun _ _ _ => 0) (stOf s).oracles.size J.P (rowsLaid J own₀ c m.st.input m.st.heard))
        (VerifiableInference.Desc.K1.seedsOf J.P r₁)).map .answer ∧
      y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  obtain ⟨c', d₀, d₁, hlend, hds, -, hy1, hin, hheard⟩ :=
    send_moved_term T blk J hsh hh hf k m E ds y cols hd hS.1
  have hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c'.1.1 := by
    rw [hch] at hlend
    exact cut_of_lendHalf _ k 0 J.P.place (sendPart J) c' hlend
  obtain ⟨-, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ blk s s' _ _ _ hS.2
  rw [hy1, rounds_send] at hdec
  refine ⟨c'.1.1, _, _, gs, hc, hdec, ?_, hin, hheard⟩
  rw [hf₀]
  exact played_vals_send J own₀ hdata c'.1.1 m.st _ d₀

end Step

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.idx_yes
#print axioms AtPublicFiles.FirstH.msg_yes
#print axioms AtPublicFiles.FirstH.w_yes
#print axioms AtPublicFiles.FirstH.stays_of_yes
#print axioms AtPublicFiles.FirstH.says_at_yes
#print axioms AtPublicFiles.FirstH.rows_hold_at_yes
#print axioms AtPublicFiles.FirstH.step_send
