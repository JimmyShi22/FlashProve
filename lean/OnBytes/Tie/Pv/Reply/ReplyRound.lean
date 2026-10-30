-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Reply/ReplyRound.lean: for an accepted proof file: WHICH round of the file's own view
holds the caller's reply: a number k at which the plan's entry has the name REPLY. Statements and
proofs.

What it is for. `accepted_reply_round` (OnBytes/Tie/Pv/Reply/ReplyAccepted.lean) has a round rv, the
first of the rounds still to come at a context c4 of the run, whose one item is the caller's reply.
It does not say that rv is a round of the file's view, nor which. Every routine that the kit of
OnBytes/Tie/Pv/Keeps/KeepsKit.lean walks takes entries of the plan and rounds of the view off the
front alone, and as many of the one as of the other (`Kept.tail`, `Kept.left`). This file lays that
along the records of the run, from the context made of the file's own view to c4.

Main names:
  `suffix_eq_drop`: a suffix of a list that is as long as the list without its first k members is
    that list.
  `kept_step`, `kept_chain`: a link's call, and a chain of such calls, are `Kept`.
  `kept_four`, `kept_five`: so are the first calls of `ReqFrame.first`.
  `accepted_reply_at`: accepted; every link's routine keeps; the last link is of kind 2. Then,
    beside the records of the run: a number k and an entry e with: the plan's entry number k is e;
    e has the name REPLY; the view's round number k has drawn what rv has drawn; AND, IF NO MESSAGE
    IS OPEN AT c4, the view's round number k IS rv, whose one item is the caller's reply.
Limits: one direction: from the verdict. THAT NO MESSAGE IS OPEN AT c4 IS A PREMISE OF THE LAST
CLAUSE: it is shown nowhere here. That the last link of the program's own list is of kind 2 is a
premise. Nothing is said on what the reply means.
-/
import OnBytes.Tie.Pv.Reply.ReplyAccepted

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Reply
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5 OnBytes.Model.Road OnBytes.PscRun

/-- A suffix as long as the list without its first k members is that list. -/
theorem suffix_eq_drop {α : Type} {l1 l : List α} {k : Nat} (h : l1 <:+ l)
    (hl : l1.length = (l.drop k).length) : l1 = l.drop k := by
  have e := List.suffix_iff_eq_drop.1 h
  rw [List.length_drop] at hl
  by_cases hk : k ≤ l.length
  · have e2 : l.length - l1.length = k := by omega
    rw [e2] at e
    exact e
  · have h0 : l1.length = 0 := by omega
    rw [List.eq_nil_of_length_eq_zero h0, List.drop_eq_nil_of_le (by omega)]

/-- One call of runLinkH is Kept. -/
theorem kept_step {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx}
    {l : Nat} {X : LinkH} [k : KeepsM X.run] {check : ChainCheck} {out : Proof.LinksResult}
    {c : Ctx} {r : ChainCheck × Proof.LinksResult} {c' : Ctx} {chk : ChainCheck}
    {o : Option WsForkOut} {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2) : Kept c c' := by
  have K1 : Kept c c1 := (inferInstance : Keeps check.first).out c chk c1 S.first
  have K2 : Kept c1 c2 :=
    RunsKeep.kept (m := LinkM) (x := X.run)
      (s := ({ check := chk, link := l, arrayOf := X.arrayOf, list := X.Tp }, X.Fp, c1))
      (a := o) (s' := (C', F', c2)) k.out S.run
  by_cases hf : X.fv = true
  · obtain ⟨o', row, -, h3, -⟩ := S.row hf
    exact (K1.trans K2).trans ((inferInstance : Keeps (pendingRowH wsLay r.2.indexMasks o' X.NCL
      p.lin)).out c2 row c' h3)
  · rw [(S.noRow hf).1]
    exact K1.trans K2

/-- A chain of such calls is Kept. -/
theorem kept_chain {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} :
    ∀ {rest : List LinkH} {l : Nat} {check : ChainCheck} {out : Proof.LinksResult} {c : Ctx}
      {r : ChainCheck × Proof.LinksResult} {c' : Ctx}, (∀ X ∈ rest, KeepsM X.run) →
      LinksChain links p wsLay cEnd rest l check out c r c' → Kept c c'
  | [], _, _, _, _, _, _, _, h => by
    obtain ⟨-, e⟩ : _ ∧ _ := h
    rw [e]
    exact Kept.refl _
  | Y :: _, _, _, _, _, _, _, hk, h => by
    obtain ⟨_, _, _, _, _, _, _, _, S, _, _, T⟩ := h
    haveI := hk Y List.mem_cons_self
    exact (kept_step S).trans (kept_chain (fun Z hZ => hk Z (List.mem_cons_of_mem _ hZ)) T)

variable {f : ReqFrame} {cEnd c : Ctx} {r : ReqFrame × Array Nat} {c' : Ctx}
  {L : Params.ReqLink} {G : ReqGroup} {g : ReqFrame} {plain : List E} {kept ids : Array Nat}
  {mask : Nat} {j : ReqFrame} {c4 c5 c6 c7 : Ctx}

theorem kept_four (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7) :
    Kept c c4 := (inferInstance : Keeps f.beginLink).out c g c4 P.begin

theorem kept_five (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7) :
    Kept c c5 :=
  (kept_four P).trans ((inferInstance : Keeps (Blk.recvEs L.plain)).out c4 plain c5 P.heard)

/-- What is received leaves as many rounds to come. -/
theorem ate_length {A A' : List Fmt.RoundView} {l : List E} (h : Ate A l A') : A'.length = A.length := by
  rcases h with ⟨-, e⟩ | ⟨rv, t, gs, e1, -, e3⟩
  · rw [e]
  · rw [e1, e3]
    rfl

/-- **Accepted: which round of the file's own view holds the caller's reply.** -/
theorem accepted_reply_at (Z : Array LinkH) (hk : AllKeep Z) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray}
    (h : Proof.check c table copy request words reply (runLinksH Z c.first wsLay) file = .accepted)
    (Xs : List LinkH) (Xh : LinkH) (hZ : Z.toList = Xs ++ [Xh]) (h2 : Xh.kind = 2) :
    ∃ r fin cE check0 ca rN cb cc lin cd checkH outH cH chk o C' F' c1 c2
      fr L G g plain kept ids mask j c4 c5 c6 c7 rv, ∃ (k : Nat) (e : Fmt.Entry),
      FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd ∧
      LinksChain Z c.first wsLay cE Xs 0 check0 {} ca (checkH, outH) cH ∧
      LinkStep Z c.first wsLay cE Xs.length Xh checkH outH cH rN cb chk o C' F' c1 c2 ∧
      FirstParts checkH.frame cE cH fr c1 L G g plain kept ids mask j c4 c5 c6 c7 ∧
      c4.ch.pending = rv :: c6.ch.pending ∧ rv.vals = [Fmt.ItemValue.e reply.triple] ∧
      (Proof.firstStart c.first).entries[k]? = some e ∧ Fmt.Entry.name e = "REPLY" ∧
      (r.first.view.rounds[k]?).map Fmt.RoundView.drawn = some rv.drawn ∧
      (c4.ch.cur = none → r.first.view.rounds[k]? = some rv) := by
  obtain ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkH, outH, cH, chk, o, C', F', c1, c2,
    fr, L, G, g, plain, kept, ids, mask, j, c4, c5, c6, c7, rv, R, A, S, P, a1, a2⟩ :=
    accepted_reply_round Z hk h Xs Xh hZ h2
  have hXs : ∀ X ∈ Xs, KeepsM X.run := fun X hX =>
    hk X (Array.mem_toList_iff.1 (by rw [hZ]; exact List.mem_append_left _ hX))
  have K0 : Kept (startOf (Proof.firstStart c.first) r.first.view) ca :=
    (inferInstance : Keeps (ChainCheck.start c.first.shape c.first.layout)).out _ check0 ca R.start
  have KH : Kept (startOf (Proof.firstStart c.first) r.first.view) cH :=
    K0.trans (kept_chain hXs A)
  have K4 := KH.trans (kept_four P)
  have K5 := KH.trans (kept_five P)
  obtain ⟨k, e5, p5⟩ := K5.tail rfl
  have hne : (L.plain != 0) = true := by
    by_contra hn
    have e := (noReply_view P hn).1
    have a3 : rv.vals = plain.map fun x => Fmt.ItemValue.e x.triple := by
      have hh := (noReply_view P hn).2
      rw [a1] at hh
      exact absurd (congrArg List.length hh) (by simp)
    rw [a2, e] at a3
    cases a3
  have h1 : (Blk.recvEs L.plain).Yields c4 plain c5 := (Blk.yields_iff _ _ _ _).2 P.heard
  obtain ⟨d, hc⟩ := closeEmpty_close (P.reply hne)
  obtain ⟨e, es, r5, rest, q1, q2, -, q4, -, -, -, -, -, q10, -⟩ :=
    Blk.close_inv "REPLY" .nothing 0 d c5 c6 P.v5 hc
  have hA := (recvEs_view P.v4 h1).2.1
  -- the entry
  have x1 : ((Proof.firstStart c.first).entries.drop k)[0]? = some e := by
    have e5' : c5.ch.entries = (Proof.firstStart c.first).entries.drop k := e5
    rw [← e5', q1]
    rfl
  rw [List.getElem?_drop, Nat.add_zero] at x1
  -- what the round has drawn
  have p5' : c5.ch.pending.map Fmt.RoundView.drawn = (r.first.view.rounds.drop k).map Fmt.RoundView.drawn := p5
  have hd5 : r5.drawn = rv.drawn := by
    rcases hA with ⟨-, e⟩ | ⟨rr, tt, gs, e1, -, e3⟩
    · rw [e, a1] at q4
      exact congrArg Fmt.RoundView.drawn (List.cons.inj q4).1.symm
    · rw [a1] at e1
      rw [e3] at q4
      rw [← (List.cons.inj q4).1, (List.cons.inj e1).1]
  have x2 : ((r.first.view.rounds.drop k).map Fmt.RoundView.drawn)[0]? = some rv.drawn := by
    rw [← p5', q4, ← hd5]
    rfl
  rw [List.getElem?_map, List.getElem?_drop, Nat.add_zero] at x2
  refine ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkH, outH, cH, chk, o, C', F', c1, c2,
    fr, L, G, g, plain, kept, ids, mask, j, c4, c5, c6, c7, rv, k, e, R, A, S, P, a1, a2, x1, q2,
    x2, fun hcur => ?_⟩
  have hp4 : c4.ch.pending = c4.ch.left := by
    unfold Chan.pending
    rw [hcur]
  have hl : c4.ch.left <:+ r.first.view.rounds := K4.left
  have hlen : c4.ch.left.length = (r.first.view.rounds.drop k).length := by
    rw [← hp4, ← ate_length hA, ← List.length_map (f := Fmt.RoundView.drawn), p5', List.length_map]
  have hdrop := suffix_eq_drop hl hlen
  have x3 : (r.first.view.rounds.drop k)[0]? = some rv := by
    rw [← hdrop, ← hp4, a1]
    rfl
  rw [List.getElem?_drop, Nat.add_zero] at x3
  exact x3

#print axioms kept_chain
#print axioms accepted_reply_at

end OnBytes.Tie.Pv.Reply
