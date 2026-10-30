-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/OwnAt.lean: THE LOOKUPS' TIE OwnIs AT THE PLACE (l, i): in the goals' scope, at
the second hash function, at every link l < 24 and every i from 1 to 6: at the record in front of
hearing block number i of link l the record's own five are the public part's, AT THE NUMBER l.

Compiled with the whole library.


HOW. Johnson/IMR/OwnSeat.lean has the tie at the number that the record bears. That this number is l
is local
to the link. (1) The link's first hearing block is a lot's block with "opened" OF LINK l's OWN ROW
of the frames joined behind it (Johnson/IMR/FirstSeats.lean: first_sits, Joined.yes); which function
that
row's "opened" is: Johnson/IMR/FrameSeat.lean: frames_arms; what it lays: openAtt_ctx, openLay_ctx,
openLayZero_ctx (Johnson/Goal/Meaning/OwnInv.lean). (2) Hearing blocks number 1 to 5 each leave what
ctxOf reads: by the seats (k3_of, k4_of, k5_of, k1_later, k8_of_layers, k8_of_attention: each block
is a maker's, alone) and the makers' laws (Quiet, or commitAtS_ctx).

  row_opens   a yes of "opened" in link l's own row, where the link is not of the head's kind:
    (ctxOf t).2 = some (0, r, l, ar).
  kind_not_head   in scope a link in front of the head's is not of the head's kind.
  ctx_behind_first   so behind hearing block number 0.
  alone_same, k1Reads_same, k1_at_same, hear_same   hearing blocks number 1 to 5 are Decides
    SameCtx.
  ctx_at   in front of hearing block number n + 1, n ≤ 5: (ctxOf t).2 = some (0, r, l, ar).
  both_open   RecAll and the invariant at an opening's own chain (at every o).
  ownIs_at   THE TOP: InScope P, readFiles P = ok pp, Open secondHashFunction P.pol lay P.KL F Z Bs base c A B,
    okBy … x = true, l < 24, 1 ≤ i ≤ 6, and foldBlocks 0 (c.blocksInOrder.take (14 l + 2 + i)) (startS Z
    x.pub) R C = ok (t, R', C') give OwnIs (sentAt Z) l t. NO YES OF THE WHOLE FILE IS ASKED: the
    fold's return alone.

OBJECT: the first chain of ProofFile.onlineDescription's value at the second hash function; OwnIs
(Johnson/Desc/First/Look/K3CallerOwn.lean). USER: Johnson/IMR/AtReach.lean; meant: the first clause
of the lookups' DigOn, AttOn, LayOn at their two places of a link: i = 1 (the calls) and i = 6 (the
digits). LETTERS: the files in scope; the instance x; the rounds and columns R, C: free.

WHAT IS NOT SAID. THE HEAD's LINK (l = 24): there the frame's "opened" hands the record on as it is,
and the link is opened by kind K2's "H.1.quiet" at hearing block number 1: which arm of the seat's
K2Is holds there is shown nowhere yet; headOpenQ_ctx (Johnson/Goal/Meaning/OwnOpen.lean) waits for
it. Nothing at an o other than the second hash function. No soundness.
-/
import Johnson.IMR.OwnSeat
import Johnson.IMR.FoldTools
import Johnson.IMR.OpenWalk
import Johnson.IMR.K1Seat
import Johnson.IMR.FrameSeat
import Johnson.IMR.FirstSeats
import Johnson.IMR.FlatScope
import Johnson.IMR.K3Seat
import Johnson.IMR.K4Seat
import Johnson.IMR.K5Seat
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.First.Look (OwnIs)
open ProofFile (Pub Cl)
open Johnson.Desc.First.Walk

/-! ## What the row of link l opens -/

open Johnson.Desc.First.Walk.Seat in
/-- **A yes of "opened" in link l's own row of the frames, where that link is not the head's, lays
the number l.** -/
theorem row_opens {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) {l : Nat} {f : LinkFrame}
    (hf : fs[l]? = some f) (hk : ∀ X, built[l]? = some X → X.kind ≠ 2) {m t : S}
    (ho : f.opened m = .ok t) : ∃ r ar, (ctxOf t).2 = some (0, r, l, ar) := by
  rcases IM.frames_arms h l f hf with ⟨X, hX, h2, -⟩ | ⟨rfl, P, -, -, e, -⟩ | ⟨P, n, hP, -, e, -⟩ |
    ⟨P, hP, -, e, -⟩
  · exact absurd h2 (hk X hX)
  · rw [e] at ho
    exact ⟨_, _, congrArg Prod.snd (openLayZero_ctx ho)⟩
  · rw [e] at ho
    obtain ⟨X, -, -, e2⟩ := frameAt_arr hP
    have k := congrArg Prod.snd (openAtt_ctx ho)
    rw [e2] at k
    exact ⟨_, _, k⟩
  · rw [e] at ho
    obtain ⟨X, -, -, e2⟩ := frameAt_arr hP
    have k := congrArg Prod.snd (openLay_ctx ho)
    rw [e2] at k
    exact ⟨_, _, k⟩

section Scope
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- In scope a link in front of the head's is not of the head's kind. -/
theorem kind_not_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24) :
    ∀ X, Z.p.built.links[l]? = some X → X.kind ≠ 2 := by
  intro X hX h2
  have k := IM.subs_scope hS hR O l (by omega)
  unfold ProofFile.subsOf at k
  rw [List.getElem?_map, Array.getElem?_toList, hX] at k
  have k' : ProofFile.subOf X.kind = IM.subAt l := Option.some.inj k
  rw [h2] at k'
  unfold IM.subAt at k'
  rw [if_neg (by omega : ¬ l = 24)] at k'
  split at k' <;> cases k'

/-- **Behind the first hearing block of link l < 24 the record's context is open and bears l.** -/
theorem ctx_behind_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {s t₀ t₁ : S} {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) s R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) s R C = .ok (t₁, R₁, C₁)) :
    ∃ r ar, (ctxOf t₁).2 = some (0, r, l, ar) := by
  obtain ⟨k, hk⟩ : ∃ k, (kindsBeforeBatching (IM.subAt l) (l == 0))[0]? = some k := by
    unfold IM.subAt
    rw [if_neg (by omega : ¬ l = 24)]
    by_cases h0 : l = 0
    · subst h0
      exact ⟨_, rfl⟩
    · have e : (l == 0) = false := by simpa using h0
      rw [e]
      split <;> exact ⟨_, rfl⟩
  obtain ⟨Lk, b, eL, e0, L, -, b', -, -, J⟩ := IM.first_sits hS hR O l (by omega) k hk
  have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
    have q := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
      (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at q
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, f, m, hfs, hf, -, -, ho, -⟩ := J.yes d
  exact row_opens hfs hf (kind_not_head hS hR O hl) ho

/-! ## The blocks between leave the context -/

theorem alone_same {b b' : Block S Cl} {a : Place} (hk : a.kind ≠ KindName.K7)
    (la : IM.LaidAlone ProofFile.sameReply b b' b.name a) (W : Decides SameCtx b') : Decides SameCtx b :=
  fun s rs gs t h => W s rs gs t ((IM.yes_alone la hk s t rs gs).1 h).1

theorem k1Reads_same (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH) (pr : Nat)
    (reads : Option (List Nat)) : Decides SameCtx (IM.k1Reads Z G l X pr reads) :=
  fun s rs gs t h => by
    obtain ⟨v, a1, a2⟩ := andThen_yes h
    exact sameCtx_trans _ _ _ ((commitAtS_ctx _ _ _ _).1 s _ _ v a1)
      ((orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2).ctx

theorem k1_at_same (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {i : Nat} (hi : i = 3 ∨ i = 5) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[l]? = some Lk) (e : Lk.hear[i]? = some b) : Decides SameCtx b := by
  have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some KindName.K1 := by
    unfold IM.subAt
    rw [if_neg (by omega : ¬ l = 24)]
    by_cases h0 : l = 0
    · subst h0
      rcases hi with rfl | rfl <;> rfl
    · have e0 : (l == 0) = false := by simpa using h0
      rw [e0]
      rcases hi with rfl | rfl <;> split <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l (by omega)) i hk
      (by rcases hi with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · exact alone_same (by intro k; cases k) la fun s rs gs t h => k1Reads_same _ _ _ _ _ s rs gs t h
  · exact alone_same (by intro k; cases k) la fun s rs gs t h =>
      (commitAtS_ctx (Cl := Unit) _ _ _ _).1 s rs gs t h

/-- **Every hearing block number 1 to 5 of a link in front of the head's leaves what ctxOf
reads.** -/
theorem hear_same (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {j : Nat} (h1 : 1 ≤ j) (h5 : j ≤ 5) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[l]? = some Lk) (e : Lk.hear[j]? = some b) : Decides SameCtx b := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  · obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O l (by omega) false
    have ix : IM.k3Ix l false = 1 := by
      show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
      rw [if_neg (by omega : ¬ l = 24)]
      rfl
    rw [ix] at e'
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact alone_same (by intro k; cases k) la (whole_sameQ (theStated_quiet _ _ _ _ _ _ k3)).1
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b', y, eL', e', -, la, -⟩ := IM.k4_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone_same (by intro k; cases k) la (whole_sameQ (blockAtC_quiet _)).1
    · obtain ⟨Lk', b', x, a, eL', e', k5, la, -⟩ := IM.k5_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone_same (by intro k; cases k) la fun s rs gs t h =>
        (whole_sameQ (k5AtN_quiet _ _ _ _ k5)).1 s rs gs t h
  · exact k1_at_same hS hR O hl (Or.inl rfl) eL e
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b', Xl, hp, eL', e', -, la, -⟩ := IM.k8_of_layers hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone_same (by intro k; cases k) la (whole_sameQ (k8Whole_quiet _)).1
    · obtain ⟨Lk', b', Xl, a, eL', e', -, la, -⟩ := IM.k8_of_attention hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone_same (by intro k; cases k) la (whole_sameQ (k8Whole_quiet _)).1
  · exact k1_at_same hS hR O hl (Or.inr rfl) eL e

/-- **In front of hearing block number n + 1 of link l < 24, n ≤ 5, the record's context is open and
bears l.** -/
theorem ctx_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24) {s : S}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 5, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) s R C = .ok (t, R', C') →
      ∃ r ar, (ctxOf t).2 = some (0, r, l, ar)
  | 0, _, t, R', C', f => by
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f
    exact ctx_behind_first hS hR O hl f₀ f
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + 3 + n) f
    obtain ⟨r, ar, k⟩ := ctx_at hS hR O hl n (by omega) u Ru Cu fu
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr l (by omega)
    rw [if_neg (by omega : ¬ l = 24)] at hlen
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 1]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : n + 1 < Lk.hear.length)⟩
    have ib : c.blocksInOrder[14 * l + 3 + n]? = some b := by
      have q := IM.hear_at_flat eL e
      rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) (n + 1)).trans
        (by omega : 14 * l + (n + 1) + 2 = 14 * l + 3 + n)] at q
    obtain ⟨rs, gs, d⟩ := fold_next ib fu f
    have q : ctxOf t = ctxOf u := hear_same hS hR O hl (by omega) (by omega) eL e u rs gs t d
    exact ⟨r, ar, by rw [q]; exact k⟩

/-- RecAll and the invariant at an opening's own chain. -/
theorem both_open {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray}
    (O : IM.Open o pol ly KL F Z Bs base c A B) {x : ProofFile.Inst}
    (hx : ProofFile.okBy o ProofFile.pureRoad.links Z x = true) {k : Nat} (hk : k ≤ (frontOf c).length)
    {ft : Nat} {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z x.pub) rs cols = .ok r) : BothAt Z r.1 := by
  have H := (seatKeeps_rec (k2Share Z.first.codes Z.first.shape)).and
    (seatKeeps_own (A := arrOf Z) (lay := Z.first.layout))
  have q := open_fold H O ⟨trivial, arrOk_at Z⟩
    (fun l Q hQ => ⟨trivial, letters_arr (IM.base_made O.made).2.2.1 hQ⟩) hk h
  exact ⟨q.1 (recAll_startS O.pub (okBy_reqOk hx)), q.2 (own_startS O.pub (okBy_reqOk hx))⟩

/-- **THE LOOKUPS' TIE AT THE PLACE (l, i)**: in scope, at the second hash function: at every link
l < 24 and every i from 1 to 6: at the record that a fold from the first record over the flat list's
first 14 l + 2 + i entries returns (the record in front of hearing block number i of link l):
OwnIs (sentAt Z) l. -/
theorem ownIs_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {x : ProofFile.Inst}
    (hx : ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z x = true) {l i : Nat} (hl : l < 24)
    (h1 : 1 ≤ i) (h6 : i ≤ 6) {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn}
    {t : S}
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + i)) (ProofFile.startS Z x.pub) R C = .ok (t, R', C')) :
    OwnIs (sentAt Z) l t := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have f' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z x.pub) R C =
      .ok (t, R', C') := by
    rwa [show 14 * l + 3 + n = 14 * l + 2 + (n + 1) by omega]
  obtain ⟨r, ar, k⟩ := ctx_at hS hR O hl n (by omega) t R' C' f'
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 1]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega : n + 1 < Lk.hear.length)⟩
  have hk : 14 * l + 2 + (n + 1) ≤ (frontOf c).length := by
    have q := flatIx_le (chainBy_noFront O.chain) eL e
    rw [IM.flatIx_scope hS hR O (by omega : l ≤ 24) (n + 1)] at q
    omega
  exact ownIs_of_ctx (both_open O hx hk f) k (by decide)

end Scope

#print axioms row_opens
#print axioms kind_not_head
#print axioms ctx_behind_first
#print axioms hear_same
#print axioms ctx_at
#print axioms both_open
#print axioms ownIs_at

end Meaning.K2
