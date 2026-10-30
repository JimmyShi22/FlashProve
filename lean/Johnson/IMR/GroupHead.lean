-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupHead.lean: WHERE A LINK IS OPEN, ITS FRAME's GROUP NUMBER IS
THE LINK's NUMBER: PART THREE: THE HEAD's LINK (number 24), from behind the place "H:2" to in front
of "cleared" (the cuts 340 to 352 of the flat list). With Johnson/IMR/GroupRest.lean's group_open:
all 25
links. "The state": the verifier's state, the value that
the fold of the IOP as written in Lean carries from sub-protocol to sub-protocol.
THE HEAD's LINK IN THE FLAT LIST: 337 "laid"; 338 to 346 its nine hearing sub-protocols (kinds K7
"H:1", K2 "H:2", K3, K6, K1, K8, K1, K3, K11); 347 the batching; 348 what runs behind it; 349 to 351
the one equation, the closing, the shutting; 352 "cleared".
  h2_place_group: an accept of the whole place "H:2" (the code switching at the head's link, then
    "opened"): a link is open, and its frame bears the group that the place's numbers name: BY THE
    TEXT's OWN GUARD (HeadIs.hGrp: the group of the frame in the head's own part is the place's);
    "opened" makes the open link's frame of that frame and writes no group (BehindAsks.frame).
  h2_group: so at the seat: FROM AN ACCEPT THE ARM FOLLOWS (the mute rejects; the finish's has no
    link; the switching at a link asks a state between the links); the numbers at 24 bear 24.
  entry_head: behind the flat list's first 340 entries: a link is open, number 24, group 24.
  laid_shut: at the cut 14 l + 2 of every link l < 25 (in front of its first hearing sub-protocol)
    no link is open (Johnson/IMR/FrontPin.lean's laid_at; between_shut).
  head_shut: at the cuts 338 and 339 (in front of "H:1" and of "H:2") no link is open: laid_shut;
    unopened_shut, h1_shut (kind K7's reply_record: the head's link is not opened yet).
  (The seats' tools QuietSeat, head_k3 to head_k2_runs, hear_by24, hear_runs24 and rest_of_runs stand
    in the light file HeadRest.lean.)
  group_head: THE TOP AT THE HEAD's LINK. group_all: it and group_open in one, by the cut.
  group_is: IN THE FORM OF THE FIELD "groupIs": at every cut k from 14 l + 2 to in front of
    "cleared": every L with t.link? = some L has L.check.group = l and L.check.frame.group = l.
NOT HERE, BUT IN Johnson/IMR/GroupField.lean: the cut 14 l + 1 (in front of "laid"; at l ≥ 1: behind
"cleared" of the link in front) and the cut 353; which entries of the written list of places bear
which link; the field's payer. NOWHERE YET: the cuts 354 to 358; that the field's letter groupAt is
the identity.
It counts no groups: nothing is said of the statement's number of groups.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: the list of facts along the fold,
field "groupIs"; kind K1's files (its law's premise on the open link's group, at its last two
places); the link's law's files (the one equation; the closing).
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupRest
import Johnson.IMR.OwnAtHead
import Johnson.IMR.HeadRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- **An accept of the whole place "H:2"**: a link is open and its frame bears the group that the
place's numbers name. -/
theorem h2_place_group {p : K2.P2} {n : String} {HP : K2.HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((K2.codeSwitchKind p : Block S Unit).andThen n (K2.headOpened n p.place HP)).decide s rs gs =
      .ok s') : ∃ L, s'.link? = some L ∧ L.check.frame.group = p.grp := by
  have hp := K2.placeH2_stands h
  obtain ⟨m, h₁, h₂⟩ := andThen_yes h
  have h₁' : K2.decideWith _root_.Tw.K2.sendByL8 p s _ _ = .ok m := h₁
  have h₂' : K2.headOpenQ HP m = .ok s' := h₂
  obtain ⟨r₁, r₂, a, G, w, roots, -, k⟩ := K2.head_inv hp h₁'
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (K2.headOpenQ_iff HP m s').1 h₂'
  obtain ⟨-, ⟨b', hb', ho⟩, -⟩ := K2.headOpenOpens HP m s' h₂'
  have ha2 : a2 = { a with kept := w.out.kept, ids := w.out.others } := by
    have e := q.here
    rw [k.hOut] at e
    injection e with e
    exact e.symm
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 q.behind
  obtain ⟨-, -, hL, -⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L
      F := Johnson.Desc.First.Walk.emptySlots
        (Johnson.Desc.First.Walk.weightsAtZero { trees := HP.X.Fp.trees }) HP.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  refine ⟨L, ?_, ?_⟩
  · unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  · rw [hL]
    show f.group = _
    rw [bA.frame]
    show a2.fr.group = _
    rw [ha2]
    exact k.hGrp

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The place "H:2" at its seat**: from a state that stands in the head's link, an accept opens a
link whose frame bears the group 24. -/
theorem h2_group {G : ProofFile.Ground} {x : Block S Unit}
    (hx : IM.K2Is Z G { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) :
    ∃ L, t.link? = some L ∧ L.check.frame.group = 24 := by
  rcases hx with ⟨-, hm⟩ | ⟨P', n, -, hn, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      have h' : ((K2.codeSwitchKind (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name
                      .head n) : Block S Unit).andThen x.name (K2.headOpened x.name
                      (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n).place
                      HP)).decide s rs gs = .ok t := h
      obtain ⟨L, hL, g⟩ := h2_place_group h'
      exact ⟨L, hL, g.trans (nums_grp hn)⟩
    · rw [e] at h
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ :=
        K2.link_inv (snd := _root_.Tw.K2.sendByL8) (p := IM.k2P Z
          { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n) rfl h
      rw [Lk.hHere] at ha
      cases ha

/-- **Behind the place "H:2" a link is open, with the number 24 and the group 24.** -/
theorem entry_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {s t₀ t₁ t₂ : S} {R R₀ R₁ R₂ : List Fmt.RoundView} {C C₀ C₁ C₂ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 338) s R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take 339) s R C = .ok (t₁, R₁, C₁))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 340) s R C = .ok (t₂, R₂, C₂)) :
    ∃ L, t₂.link? = some L ∧ L.link = 24 ∧ L.check.frame.group = 24 := by
  obtain ⟨r, ar, hc⟩ := ctx_behind_h2 hS hR O f₀ f₁ f₂
  obtain ⟨L, hL, eN, -, -⟩ := link_of_ctx hc (by decide)
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
  obtain ⟨L', hL', g⟩ :=
    h2_group hx ((IM.yes_alone la (by intro k; cases k) _ _ rs1 gs1).1 d1).1 ha
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  exact ⟨L, hL, eN, g⟩

/-- A state between the links has no open link: ListsAtDraw.lean's link_between, said again. -/
theorem between_shut {s : S} (h : s.atBetween = true) : s.link? = none := link_between h

/-- A state in the head's link, not opened yet, has no open link. -/
theorem unopened_shut {s : S} {o : HeadOwn} (h : s.here = .head o) (hc : o.opened = false) :
    s.link? = none := by
  unfold S.link?
  rw [h]
  simp [hc]

/-- Behind the place "H:1" no link is open yet. -/
theorem h1_shut {W : Verify.Public} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k7Block W 24).decide s rs gs = .ok t) :
    t.link? = none := by
  obtain ⟨m, -, a2⟩ := andThen_yes h
  obtain ⟨o, _, ho, hc, -, -, rfl⟩ := Kinds.Head.Law.Came.reply_record 24 W.hS.V a2
  exact unopened_shut ho hc

/-- **AT EVERY LINK l < 25, IN FRONT OF ITS FIRST HEARING SUB-PROTOCOL (the cut 14 l + 2) NO LINK IS
OPEN.** -/
theorem laid_shut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.link? = none := between_shut (laid_at hS hR O hl f₀).1

/-- **AT THE HEAD's LINK, IN FRONT OF THE PLACES "H:1" AND "H:2" (the cuts 338 and 339) NO LINK IS
OPEN.** -/
theorem head_shut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 1, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (338 + n)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      t.link? = none
  | 0, _, t, R', C', f => laid_shut hS hR O (l := 24) (by omega) f
  | 1, _, t, R', C', f => by
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338) f
    obtain ⟨Lk, b0, eL, e0, J, -⟩ := IM.k7_sits hS hR O
    have i0 : c.blocksInOrder[338]? = some b0 := by
      have q := IM.hear_at_flat eL e0
      rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 0] at q
    obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f
    exact h1_shut (IM.k7_sits_yes hS hR O J d0).1
  | n + 2, hn, _, _, _, _ => absurd hn (by omega)

/-- **AT THE HEAD's LINK, AT THE STATE BEHIND THE FIRST 340 + n ENTRIES OF THE FLAT LIST, n ≤ 12
(from behind the place "H:2" to in front of "cleared"): A LINK IS OPEN, WITH THE NUMBER 24, AND ITS
FRAME BEARS THE GROUP 24.** -/
theorem group_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 12, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∃ L, t.link? = some L ∧ L.link = 24 ∧ L.check.frame.group = 24
  | 0, _, t, R', C', f => by
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338) f₁
    exact entry_head hS hR O f₀ f₁ f
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 340 + n) f
    obtain ⟨L, hL, e1, e2⟩ := group_head hS hR O n (by omega) u Ru Cu fu
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    obtain ⟨Lk, -, -, -, bC, eL, hlen, -, -, -, -, -, -, -, -, -, -, -, iC, -⟩ := hfr 24 (by omega)
    rw [if_pos rfl] at hlen
    obtain ⟨b, ib, D⟩ : ∃ b, c.blocksInOrder[340 + n]? = some b ∧ Decides Gk b := by
      by_cases h7 : n + 1 ≤ 7
      · obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 2]? = some b :=
          ⟨_, List.getElem?_eq_getElem (by omega : n + 2 < Lk.hear.length)⟩
        have ib : c.blocksInOrder[340 + n]? = some b := by
          have q := IM.hear_at_flat eL e
          rwa [(IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) (n + 2)).trans
            (by omega : 14 * 24 + (n + 2) + 2 = 340 + n)] at q
        exact ⟨b, ib, hear_by24 gk_trans (fun _ _ => gk_of_quiet)
          (fun _ _ _ _ _ _ _ _ => commit_gk) hS hR O (by omega) (by omega) eL e⟩
      · rw [hlen] at iC
        obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[340 + n]? = some b :=
          ⟨_, List.getElem?_eq_getElem (by
            have := (List.getElem?_eq_some_iff.1 iC).1
            omega)⟩
        have hy : ∀ b₁, Lk.hear[1]? = some b₁ → ∃ s rs gs t, b₁.decide s rs gs = .ok t := by
          intro b₁ e1
          have i1 : c.blocksInOrder[339]? = some b₁ := by
            have q := IM.hear_at_flat eL e1
            rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 1] at q
          obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 340) n fu
          obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f₂
          obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₁ f₂
          exact ⟨_, _, _, _, d1⟩
        have ib' : c.blocksInOrder[14 * 24 + Lk.hear.length + 2 + (n - 7)]? = some b := by
          rw [hlen, show 14 * 24 + 9 + 2 + (n - 7) = 340 + n by omega]
          exact ib
        exact ⟨b, ib, rest_of_runs gk_refl gk_trans (fun p _ hcl => batch_gk p hcl) closeOf_gk
          hS hR O (by omega) eL
          (hear_runs24 gk_refl gk_trans (fun _ _ => gk_of_quiet) hS hR O eL hy) (by omega) ib'⟩
    obtain ⟨rs, gs, d⟩ := fold_next ib fu f
    obtain ⟨L', hL', g1, g2⟩ := D u rs gs t d L hL
    exact ⟨L', hL', g2.trans e1, g1.trans e2⟩

/-- **ALL 25 LINKS IN ONE, BY THE CUT**: at every link l < 25, at the state behind the first k
entries of the flat list, from behind the sub-protocol that opens the link (the first hearing one;
at the head's link the second) to in front of "cleared": a link is open, with the number l, and its
frame bears the group l. -/
theorem group_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    {k : Nat} (h1 : 14 * l + 3 + (if l = 24 then 1 else 0) ≤ k)
    (h2 : k ≤ 14 * l + 14 + (if l = 24 then 2 else 0))
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    ∃ L, t.link? = some L ∧ L.link = l ∧ L.check.frame.group = l := by
  by_cases h : l = 24
  · subst h
    rw [if_pos rfl] at h1 h2
    obtain ⟨n, rfl⟩ : ∃ n, k = 340 + n := ⟨k - 340, by omega⟩
    exact group_head hS hR O n (by omega) t R' C' f
  · rw [if_neg h] at h1 h2
    obtain ⟨n, rfl⟩ : ∃ n, k = 14 * l + 3 + n := ⟨k - (14 * l + 3), by omega⟩
    exact group_open hS hR O (by omega) n (by omega) t R' C' f

/-- **IN THE FORM OF THE FIELD "groupIs"**: at every link l < 25, at the state behind the first k
entries of the flat list, from in front of the link's first hearing sub-protocol to in front of
"cleared": of every open link L: L.check.frame.group = l; L.check.group is that number by
definition. (Where no link is open nothing is said.) -/
theorem group_is (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    {k : Nat} (h1 : 14 * l + 2 ≤ k) (h2 : k ≤ 14 * l + 14 + (if l = 24 then 2 else 0))
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    ∀ L, t.link? = some L → L.check.group = l ∧ L.check.frame.group = l := by
  intro L hL
  by_cases h0 : k = 14 * l + 2
  · subst h0
    rw [laid_shut hS hR O hl f] at hL
    cases hL
  · by_cases h9 : l = 24 ∧ k = 339
    · obtain ⟨rfl, rfl⟩ := h9
      rw [head_shut hS hR O 1 (by omega) t R' C' f] at hL
      cases hL
    · obtain ⟨L', hL', -, g⟩ := group_all hS hR O hl (k := k) (by split <;> omega) h2 f
      obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
      exact ⟨g, g⟩

end

#print axioms h2_place_group
#print axioms entry_head
#print axioms laid_shut
#print axioms head_shut
#print axioms group_head
#print axioms group_all
#print axioms group_is

end Meaning.K2
