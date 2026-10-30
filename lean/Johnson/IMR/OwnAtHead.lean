-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/OwnAtHead.lean: THE LOOKUPS' TIE OwnIs AT THE HEAD's LINK: in the goals' scope, at
the second hash function, at every i from 2 to 7: at the record in front of hearing block number i
of link 24 the record's own five are the public part's, AT THE NUMBER 24. With
Johnson/IMR/OwnAt.lean: all 25 links.

Compiled with the whole library.


HOW. At the head's link the frame's "opened" hands the record on as it is
(Johnson/IMR/FirstSeats.lean:
k7_sits); the link is opened at hearing block number 1, the place "H:2". (1) Behind "H:1" the record
stands in the head's link (Johnson/IMR/ListsEnds.lean: h1_headFr). (2) The seat says of the block at
"H:2"
that it is one of four (Johnson/IMR/K2Seat.lean: k2_head_of, K2Is): FROM ITS YES THE ARM FOLLOWS:
the mute
refuses; the finish's has no link; the switch at a link asks that the record stand between the links
(link_inv), which it does not: so it is the switch with headOpened behind it, at letters made off
the blank letters at 24; what that lays: headOpenQ_ctx (Johnson/Goal/Meaning/OwnOpen.lean). (3)
Hearing blocks number 2 to 6 each leave what ctxOf reads: k3_of, k6_of, k1_later (twice),
k8_of_head, with the makers' laws.

  h2_ctx   a yes of the block at "H:2" from a record that stands in the head's link: (ctxOf t).2 =
    some (2, r, 24, ar).
  ctx_behind_h2   so behind hearing block number 1.
  k1_head_same, hear_same24   hearing blocks number 2 to 6 are Decides SameCtx.
  ctx_at24   in front of hearing block number n + 2, n ≤ 5.
  ownIs_at24   THE TOP: InScope P, readFiles P = ok pp, Open secondHashFunction P.pol lay P.KL F Z Bs base c A
    B, okBy … x = true, 2 ≤ i ≤ 7, and foldBlocks 0 (c.blocksInOrder.take (338 + i)) (startS Z x.pub) R C =
    ok (t, R', C') give OwnIs (sentAt Z) 24 t. NO YES OF THE WHOLE FILE IS ASKED.
  ownIs_k3   BOTH FILES' TOPS IN ONE, AT KIND K3's OWN PLACES: l < 25, digits : Bool, the fold over
    the first 14 l + 2 + k3Ix l digits entries: OwnIs (sentAt Z) l t.

OBJECT: the first chain of ProofFile.onlineDescription's value at the second hash function; OwnIs
(Johnson/Desc/First/Look/K3CallerOwn.lean). USER: Johnson/IMR/AtReach.lean; meant: the first clause
of the
lookups' conditions at their two places of the head's link: i = 2 (the calls) and i = 7 (the
digits). LETTERS: the files in scope; the instance x; R, C: free.

WHAT IS NOT SAID. WHICH ARM OF K2Is HOLDS AS A FACT OF THE SEAT ALONE: here it is read off a yes.
Nothing at an o other than the second hash function. No soundness.
-/
import Johnson.IMR.OwnAt
import Johnson.IMR.ListsEnds
import Johnson.IMR.K6Seat
import Johnson.IMR.K7Seat
import Johnson.IMR.K2Seat

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

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The place "H:2"**: from a record that stands in the head's link, a yes lays the open context
with the number 24. -/
theorem h2_ctx {G : ProofFile.Ground} {x : Block S Unit}
    (hx : IM.K2Is Z G { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) :
    ∃ r ar, (ctxOf t).2 = some (2, r, 24, ar) := by
  rcases hx with ⟨-, hm⟩ | ⟨P', n, -, -, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, hl', hHP, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      obtain ⟨v, -, a2⟩ := andThen_yes (n := x.name) h
      have a2' : K2.headOpenQ HP v = .ok t := a2
      obtain ⟨r, k⟩ := headOpenQ_ctx a2'
      have e24 : HP.l = 24 := by
        obtain rfl : 24 = l' := Option.some.inj hl'
        unfold P1K2.pureLetters at hHP
        obtain ⟨X, -, rfl⟩ := Option.map_eq_some_iff.1 hHP
        rfl
      rw [e24] at k
      exact ⟨r, _, k⟩
    · rw [e] at h
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ :=
        K2.link_inv (snd := _root_.Tw.K2.sendByL8) (p := IM.k2P Z
          { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n) rfl h
      rw [Lk.hHere] at ha
      cases ha

/-- **Behind hearing block number 1 of the head's link the record's context is open and bears
24.** -/
theorem ctx_behind_h2 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {s t₀ t₁ t₂ : S} {R R₀ R₁ R₂ : List Fmt.RoundView} {C C₀ C₁ C₂ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 338) s R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take 339) s R C = .ok (t₁, R₁, C₁))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 340) s R C = .ok (t₂, R₂, C₂)) :
    ∃ r ar, (ctxOf t₂).2 = some (2, r, 24, ar) := by
  obtain ⟨Lk, b0, eL, e0, J, hid⟩ := IM.k7_sits hS hR O
  obtain ⟨Lk', b1, x, eL', e1, -, la, hx⟩ := IM.k2_head_of hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have q := IM.hear_at_flat eL e0
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 0] at q
  have i1 : c.blocksInOrder[339]? = some b1 := by
    have q := IM.hear_at_flat eL e1
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 1] at q
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, f, m, hfs, hf, dm, -, ho, -⟩ := J.yes d0
  rw [hid fs f hfs hf] at ho
  obtain rfl : m = t₁ := Except.ok.inj ho
  obtain ⟨a, ha, -⟩ := h1_headFr (W := Bs.G₀.W) dm
  obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₁ f₂
  exact h2_ctx hx ((IM.yes_alone la (by intro k; cases k) _ _ rs1 gs1).1 d1).1 ha

theorem k1_head_same (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {i : Nat} (hi : i = 4 ∨ i = 6) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[24]? = some Lk) (e : Lk.hear[i]? = some b) : Decides SameCtx b := by
  have hk : (kindsBeforeBatching (IM.subAt 24) (24 == 0))[i]? = some KindName.K1 := by
    rcases hi with rfl | rfl <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O 24 (IM.subAt 24) (IM.subs_scope hS hR O 24 (by omega)) i hk
      (by rcases hi with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · exact alone_same (by intro k; cases k) la fun s rs gs t h => k1Reads_same _ _ _ _ _ s rs gs t h
  · exact alone_same (by intro k; cases k) la fun s rs gs t h =>
      (commitAtS_ctx (Cl := Unit) _ _ _ _).1 s rs gs t h

/-- **Hearing blocks number 2 to 6 of the head's link leave what ctxOf reads.** -/
theorem hear_same24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {j : Nat} (h2 : 2 ≤ j) (h6 : j ≤ 6) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[24]? = some Lk) (e : Lk.hear[j]? = some b) : Decides SameCtx b := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  · obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O 24 (by omega) false
    have e'' : Lk'.hear[2]? = some b' := e'
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e'')
    exact alone_same (by intro k; cases k) la (whole_sameQ (theStated_quiet _ _ _ _ _ _ k3)).1
  · obtain ⟨Lk', b', x, ms, eL', e', -, k6, la, -⟩ := IM.k6_of hS hR O
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact alone_same (by intro k; cases k) la (whole_sameQ (seatedClaims_quiet k6)).1
  · exact k1_head_same hS hR O (Or.inl rfl) eL e
  · obtain ⟨Lk', b', Xl, eL', e', -, la, -⟩ := IM.k8_of_head hS hR O
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact alone_same (by intro k; cases k) la (whole_sameQ (k8Whole_quiet _)).1
  · exact k1_head_same hS hR O (Or.inr rfl) eL e

/-- **In front of hearing block number n + 2 of the head's link, n ≤ 5, the record's context is open
and bears 24.** -/
theorem ctx_at24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 5, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (340 + n)) s R C = .ok (t, R', C') →
      ∃ r ar, (ctxOf t).2 = some (2, r, 24, ar)
  | 0, _, t, R', C', f => by
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338) f₁
    exact ctx_behind_h2 hS hR O f₀ f₁ f
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 340 + n) f
    obtain ⟨r, ar, k⟩ := ctx_at24 hS hR O n (by omega) u Ru Cu fu
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr 24 (by omega)
    rw [if_pos rfl] at hlen
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 2]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : n + 2 < Lk.hear.length)⟩
    have ib : c.blocksInOrder[340 + n]? = some b := by
      have q := IM.hear_at_flat eL e
      rwa [(IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) (n + 2)).trans
        (by omega : 14 * 24 + (n + 2) + 2 = 340 + n)] at q
    obtain ⟨rs, gs, d⟩ := fold_next ib fu f
    have q : ctxOf t = ctxOf u := hear_same24 hS hR O (by omega) (by omega) eL e u rs gs t d
    exact ⟨r, ar, by rw [q]; exact k⟩

/-- **THE LOOKUPS' TIE AT THE HEAD's LINK**: in scope, at the second hash function: at every i from
2 to 7: at the record that a fold from the first record over the flat list's first 338 + i entries
returns (the record in front of hearing block number i of link 24): OwnIs (sentAt Z) 24. -/
theorem ownIs_at24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {x : ProofFile.Inst}
    (hx : ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z x = true) {i : Nat}
    (h2 : 2 ≤ i) (h7 : i ≤ 7) {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn}
    {t : S}
    (f : foldBlocks 0 (c.blocksInOrder.take (338 + i)) (ProofFile.startS Z x.pub) R C = .ok (t, R', C')) :
    OwnIs (sentAt Z) 24 t := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 2 := ⟨i - 2, by omega⟩
  have f' : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z x.pub) R C = .ok (t, R', C') := by
    rwa [show 340 + n = 338 + (n + 2) by omega]
  obtain ⟨r, ar, k⟩ := ctx_at24 hS hR O n (by omega) t R' C' f'
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 2]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega : n + 2 < Lk.hear.length)⟩
  have hk : 338 + (n + 2) ≤ (frontOf c).length := by
    have q := flatIx_le (chainBy_noFront O.chain) eL e
    rw [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) (n + 2)] at q
    omega
  exact ownIs_of_ctx (both_open O hx hk f) k (by decide)

/-- **THE TIE AT KIND K3's OWN TWO PLACES OF EVERY LINK**: in front of the lookup on the calls
(digits = false) and of the lookup on the digits (digits = true) of link l < 25. -/
theorem ownIs_k3 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {x : ProofFile.Inst}
    (hx : ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z x = true) {l : Nat} (hl : l < 25)
    (digits : Bool) {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + IM.k3Ix l digits)) (ProofFile.startS Z x.pub) R C =
      .ok (t, R', C')) : OwnIs (sentAt Z) l t := by
  have ix : IM.k3Ix l digits = (if digits = true then 6 else 1) + (if l = 24 then 1 else 0) := rfl
  by_cases h24 : l = 24
  · subst h24
    rw [ix, if_pos rfl] at f
    cases digits
    · exact ownIs_at24 hS hR O hx (i := 2) (by omega) (by omega) f
    · exact ownIs_at24 hS hR O hx (i := 7) (by omega) (by omega) f
  · rw [ix, if_neg h24] at f
    cases digits
    · exact ownIs_at hS hR O hx (i := 1) (by omega) (by omega) (by omega) f
    · exact ownIs_at hS hR O hx (i := 6) (by omega) (by omega) (by omega) f

#print axioms h2_ctx
#print axioms ctx_behind_h2
#print axioms hear_same24
#print axioms ctx_at24
#print axioms ownIs_at24
#print axioms ownIs_k3

end Meaning.K2
