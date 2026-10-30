-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindMg.lean: «LINK l: BEHIND THE BATCHING»: THE RECORD
`NoHouse`, SECOND FORM: WHERE THE PROMISE's MEANING IS THE LIBRARY's COMPOSED ONE. `noHouse_behind`
(Honest/Law/NoHouse/BehindBatch.lean) takes the library's `LettersRide` as a premise, which is paid
at no filling. Here that premise, and those on the shape, the book and what a yes leaves, give way
to what the library itself can pay: `form_next_behind` (FormBehind.lean) is called. WHAT STAYS, BY
NAME: the runs' share (hstate); the plan's two counts (ht, hm); the item's tie (hafter, which now
hands over «the one sum can be taken» too); the fall's two ties (hg, htest); the threads' letters
(hctx, hkeeps, hrides, said, rides).

WHAT THIS IS. A conditional lemma on definitions of ours: an assembly, as `noHouse_behind`. None of
the library's goals.

  `noHouse_behind_mg`

WHOSE EACH PREMISE IS. seat, hr, ho, hd: at the library's head the member is the term `L.behindB`
(`P5J.sits_at`, Johnson/P5J/K09List.lean): by unfolding. hn: `noHalf_of_kind`. hMg: by unfolding at
the thread's letters at the head. hfit, hpf: `P5J.linkFit_links`, `pubFit9_links` (the
kernel). hp, hp', hl, hpc: the written list of places. ht, hm: the plan's two counts: at the head
`behind_counts` (Honest/Law/NoHouse/BehindHead.lean). hstate: THE RUNS' SHARE: the library's
`rb_behind`, `rest_behind`, `ledger_behind` under `LinkShare`
(Johnson/Desc/First/Link/Law/RidesAtMg.lean), whose ties of the link's entries to the known runs are
in Johnson/LPFK9R/K8Ties.lean and K4Ties.lean. hafter: the library's `after_at`
(TieThreeFour.lean) with `totalBQ`'s text (Johnson/Desc/Sound/FormsQ.lean), at the thread's
letters. hg: not shown here. htest: whoever lays the thread's fall and the item's test from
one text. hctx, hkeeps, hrides, said, rides: the thread's letters.

MET FOR NOTHING. As `NoHouse`. Limits. NOT ONE OF THE PREMISES IS SHOWN HERE AT THE PROTOCOL.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Fill
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Guards
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FormBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Place Strs Wit Link)
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers Meaning)
open VerifiableInference.Desc.Sound (MgData mgAll mgBase MsgT CellsQ moreAll)
open VerifiableInference.Desc.LinkJoin (Rb rest9 ledgerOk linkFit pubFit9 hearN)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X : Type}
variable {Xi' P Tok : Type} {rows cols nR : Nat} {X' : OnBytes.Model.Verify.Public}

/-- **«Behind the batching»: the record, at the library's composed meaning.** b: the member's
number; m: its segment's; Lk: its link; p, p': its place and the next; ctx: what its row reads and
leaves. -/
theorem noHouse_behind_mg (𝔇 : MgData Xi' P Tok rows cols nR X')
    (L : Letters Bk Cl W₀ Rc Xi Tr X P (CellsQ rows cols) Tok MsgT)
    (hMg : L.MgP = mgAll 𝔇 mgBase)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) {b m : Nat} {blk : Block S Cl}
    {Lk : Link S Cl} {p p' : Place} {ctx : List Item}
    (seat : L.bs[b]? = some blk) (hr : blk.rounds = [])
    (ho : blk.oracles.length = blk.rounds.length)
    (hn : (L.hs.find? fun g => g.place == blk.place) = none)
    (hd : ∀ s rs gs, blk.decide s rs gs = Lk.runBehind s)
    (hfit : linkFit L.links L.ps = true) (hpf : pubFit9 true moreAll L.links L.ps = true)
    (hp : L.ps[b]? = some p) (hp' : L.ps[b + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN L.links m + 2)
    (ht : L.N.treesAt L.ps[b + 1]? = L.N.treesAt L.ps[b]?)
    (hm : L.N.msgsAt L.ps[b + 1]? = L.N.msgsAt L.ps[b]?)
    (howes : (L.thread.row b).owes = Item.total m :: ctx)
    (hopen : Item.totalB m ∈ L.thread.opened b) (hctxO : ∀ i ∈ ctx, i ∈ L.thread.opened b)
    (hstate : ∀ s s', Lk.runBehind s = .ok s' → Rb s s' ∧
      (∃ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) ∧
      (ledgerOk s = true → ledgerOk s' = true))
    (hafter : ∀ w a y v, (L.Mg w).totalB m a y v → ∃ s', Lk.runBehind a.2 = .ok s' ∧
      VerifiableInference.Desc.K9.totalIn (𝔇.pubD.N.group m) s' = true ∧
      (L.Mg w).total m (a.1, s') y v)
    (hg : FallGuards 0 blk (fall b)) (htest : ∀ s, fall b s [] = none → L.test m s = none)
    (hctx : ∀ w i a s' y v, i ∈ ctx → Lk.runBehind a.2 = .ok s' →
      Item.holds L.N (L.mg w) i a y v → Item.holds L.N (L.mg w) i (a.1, s') y v)
    (hkeeps : ∀ s s', s.failed = none → Lk.runBehind s = .ok s' → L.keeps b s s')
    (hrides : ∀ w s s', L.rides b w s → Lk.runBehind s = .ok s' → L.rides (b + 1) w s')
    (said : ∀ k m', Said b k m' → Said (b + 1) k m')
    (rides : RidesPastS L.thread Said b) : NoHouse L.thread Said fall b blk := by
  -- what the open item gives at a yes of the member, at any continuation of the challenges heard
  have item : ∀ k s μ E s' ds, ThrS L.thread Said b k s μ E → Lk.runBehind s = .ok s' →
      VerifiableInference.Desc.K9.totalIn (𝔇.pubD.N.group m) s' = true ∧
      (L.Mg μ.st.input).total m (L.pubOf μ.st.input.x, s') (L.thread.strs E)
        (L.thread.wit k μ.st.input (μ.st.heard ++ ds)) := by
    intro k s μ E s' ds hA hs
    have hdec : blk.decide s [] [] = .ok s' := by rw [hd]; exact hs
    have hf : fall b s [] = none := hg s [] [] s' 0 ((step_noRound (0 : Nat) blk hr s s').2 hdec)
    have hit := thr_item_at L.thread hA.1 hopen ds
    have hit' : L.test m s = none → (L.Mg μ.st.input).totalB m (L.pubOf μ.st.input.x, s)
        (L.thread.strs E) (L.thread.wit k μ.st.input (μ.st.heard ++ ds)) := hit
    obtain ⟨s'', h1, h2, h3⟩ := hafter _ _ _ _ (hit' (htest s hf))
    have h1' : Lk.runBehind s = .ok s'' := h1
    rw [hs] at h1'
    cases h1'
    exact ⟨h2, h3⟩
  refine NoHouse.ofDecide (T := L.thread) seat hr ho hn said ?_ ?_ ?_ rides
  · intro k s μ E s' hA hs
    rw [hd] at hs
    obtain ⟨R, r9, led⟩ := hstate s s' hs
    exact ⟨form_next_behind 𝔇 L hMg hfit hpf hp hp' hl hpc ht hm hA.1.2.2.1 R r9 led
        (item k s μ E s' [] hA hs).1,
      hrides _ s s' hA.1.2.2.2.2.2.1 hs,
      hkeeps s s' (Option.isNone_iff_eq_none.1 hA.1.2.2.1.1) hs⟩
  · intro k s μ E s' hA hs ds i hi
    rw [hd] at hs
    have hi' : i ∈ Item.total m :: ctx := by
      rw [← howes]
      exact hi
    rcases List.mem_cons.1 hi' with rfl | hc
    · exact (item k s μ E s' ds hA hs).2
    · exact hctx _ i (L.pubOf μ.st.input.x, s) s' _ _ hc hs
        (thr_item_at L.thread hA.1 (hctxO i hc) ds)
  · intro k s μ E hA hf
    have hit := thr_item_at L.thread hA.1 hopen []
    have hit' : L.test m s = none → (L.Mg μ.st.input).totalB m (L.pubOf μ.st.input.x, s)
        (L.thread.strs E) (L.thread.wit k μ.st.input (μ.st.heard ++ [])) := hit
    obtain ⟨s', h1, -, -⟩ := hafter _ _ _ _ (hit' (htest s hf))
    exact ⟨s', by rw [hd]; exact h1⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.noHouse_behind_mg
