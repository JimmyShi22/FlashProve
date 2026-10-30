-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupKept.lean: WHICH OLD MESSAGES THE CODE SWITCHING INTO GROUP
l + 1 KEEPS, IN NUMBERS: at the proof file's seat, in the goals' scope, from the fold's return
alone: 1 ≤ l < 24.
  flags_false: in a lawful request's shape a message with a life is sent at its link's moment 0: so
    at a frame whose moment is at least 1 the moment's flags "kept" are all false.
  MoUp; switch_moment, entry_moment, moment_at: in front of both later sendings of a link the open
    link's frame's moment is at least 1 (the code switching's front lays 1; a Quiet step leaves it;
    a later sending raises it).
  keptOf_none, keptOf_maps, keptOf_three: flags that are all false keep nothing; of a list of pairs;
    of three lists one behind the other.
  kept_next: THE TOP: with x the front that the text makes of the state in front of link l's code
    switching: in front of link l + 1's first sub-protocol:
      switchKept ‹the walk's frame's carried rows› = the numbers of switchGain x ++ ownGain x whose
      flag is true
    (kind K2's files' two lists, Johnson/Top/H0/Tw/K2C/GroupsAtYes.lean: the main message, flag
    false; the kept copies n₀ + 1 + i with the target's "kept again"; the link's own messages of
    moment 0, n₀ + 1 + K + j, with "life > 0"; n₀ the number of messages in front of that
    switching).
NOT HERE: l = 0 (what the switching into group 1 keeps of kind K1's opening); the head's link (what
the finish keeps); n₀ as a term of the list of rounds.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupFill
import Johnson.Goal.Meaning.KeptRowsPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- **At a moment behind the first no message has a life.** -/
theorem flags_false {cs : Codes} {sh : ReqShape} (hok : reqOk cs sh = true) {f : ReqFrame}
    (hs : f.shape = sh) (hm : 1 ≤ f.moment) : ∀ b ∈ K1.flagsAt f, b = false := by
  have hsh : reqShapeOk sh = true := by
    unfold reqOk at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  intro b hb
  unfold K1.flagsAt at hb
  obtain ⟨m, hmm, rfl⟩ := List.mem_map.1 hb
  unfold ReqFrame.atMoment at hmm
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hmm
  rw [hs] at h1
  cases hL : sh.link[f.link]? with
  | none =>
    rw [hL] at h1
    cases h1
  | some Lq =>
    rw [hL] at h1
    have hq := links_ok hsh Lq (List.mem_of_getElem? hL)
    unfold reqLinkOk at hq
    simp only [Bool.and_eq_true] at hq
    have hm1 := List.all_eq_true.1 hq.2 m h1
    unfold reqMessageOk at hm1
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hm1
    have e2 : m.moment = f.moment := by simpa using h2
    rcases hm1.2 with a | a
    · have : m.life = 0 := by simpa using a
      simp [this]
    · have : m.moment = 0 := by simpa using a.2
      omega

theorem keptOf_none {a : Array Nat} {k : Array Bool} (h : ∀ b ∈ k.toList, b = false) :
    keptOf a k = #[] := by
  apply Array.toList_inj.1
  rw [keptOf_toList]
  have e : (a.toList.zip k.toList).filter (·.2) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp [h x.2 (List.of_mem_zip hx).2]
  rw [e]
  rfl

theorem zip_maps : ∀ g : List (Nat × Bool), (g.map (·.1)).zip (g.map (·.2)) = g
  | [] => rfl
  | x :: g => by
    rw [List.map_cons, List.map_cons, List.zip_cons_cons, zip_maps g]

/-- Of a list of pairs. -/
theorem keptOf_maps (g : List (Nat × Bool)) :
    keptOf (g.map (·.1)).toArray (g.map (·.2)).toArray = ((g.filter (·.2)).map (·.1)).toArray := by
  apply Array.toList_inj.1
  rw [keptOf_toList]
  show (((g.map (·.1)).zip (g.map (·.2))).filter (·.2)).map (·.1) = _
  rw [zip_maps]

/-- Three lists one behind the other, the flags of the second and the third all false. -/
theorem keptOf_three {g : List (Nat × Bool)} {i₃ i₅ : List Nat} {f₃ f₅ : List Bool}
    (h3 : i₃.length = f₃.length)
    (F3 : ∀ b ∈ f₃, b = false) (F5 : ∀ b ∈ f₅, b = false) :
    keptOf (g.map (·.1) ++ i₃ ++ i₅).toArray (g.map (·.2) ++ f₃ ++ f₅).toArray =
      ((g.filter (·.2)).map (·.1)).toArray := by
  have a1 : (g.map (·.1) ++ i₃ ++ i₅).toArray =
      ((g.map (·.1)).toArray ++ i₃.toArray) ++ i₅.toArray := by simp
  have a2 : (g.map (·.2) ++ f₃ ++ f₅).toArray =
      ((g.map (·.2)).toArray ++ f₃.toArray) ++ f₅.toArray := by simp
  rw [a1, a2, keptOf_append (by simp [h3]), keptOf_append (by simp),
    keptOf_none (a := i₃.toArray) (k := f₃.toArray) (by simpa using F3),
    keptOf_none (a := i₅.toArray) (k := f₅.toArray) (by simpa using F5), Array.append_empty,
    Array.append_empty, keptOf_maps]

/-- Where a link is open at s one is open at t, and its frame's moment is not less. -/
def MoUp (s t : S) : Prop :=
  ∀ L, s.link? = some L → ∃ L', t.link? = some L' ∧ L.check.frame.moment ≤ L'.check.frame.moment

theorem moUp_trans (a b c : S) (h : MoUp a b) (k : MoUp b c) : MoUp a c := fun L hL => by
  obtain ⟨L₁, h1, e1⟩ := h L hL
  obtain ⟨L₂, h2, e2⟩ := k L₁ h1
  exact ⟨L₂, h2, Nat.le_trans e1 e2⟩

theorem moUp_of_quiet {s t : S} (q : Quiet s t) : MoUp s t := fun L hL => by
  obtain ⟨L', a, c, -, -⟩ := quiet_fwd q hL
  exact ⟨L', a, by rw [c]⟩

theorem moUp_commit {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s v : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v) : MoUp s v := by
  obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two h
  obtain ⟨L, L', a1, a2, e, -⟩ := K1.commitAtS_frame Q link moment arrays s v r₁ r₂ gs h
  intro L₀ h₀
  obtain rfl : L = L₀ := Option.some.inj (a1.symm.trans h₀)
  exact ⟨L', a2, by rw [e]; exact Nat.le_succ _⟩

/-- Behind an accept of the code switching at a link the walk's frame's moment is 1. -/
theorem switch_moment {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {x : Block S Unit}
    (hx : IM.K2Is Z G { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x)
    {s u : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok u) (hB : s.atBetween = true) : u.check.frame.moment = 1 := by
  rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, hn, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      obtain ⟨v, a1, -⟩ := andThen_yes (n := x.name) h
      obtain ⟨r₁, r₂, a, G', w, roots, -, H⟩ := K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
      unfold S.atBetween at hB
      rw [H.hHere] at hB
      cases hB
    · rw [e] at h
      have h' : K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x.name .link n) s rs
          gs = .ok u := h
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ := K2.link_inv rfl h'
      obtain ⟨L0, G0, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 Lk.hFront
      obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 Lk.hBehind
      rw [Lk.hOut]
      show f.moment = 1
      rw [bA.frame]
      show x'.f.moment = 1
      rw [a.out]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem entry_moment (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₀ R₁ : List Fmt.RoundView}
    {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ L, t₁.link? = some L ∧ L.check.frame.moment = 1 := by
  obtain ⟨L, hL, -, -⟩ := entry_group hS hR O h24 f₀ f₁
  refine ⟨L, hL, ?_⟩
  obtain ⟨hB, -⟩ := laid_at hS hR O (by omega : l < 25) f₀
  obtain ⟨Lk, b, x, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O l h1 h24
  have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
    have k := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
      (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, f, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  have mB := switch_between hx (rs := _) (gs := _) y1 hB
  have v := ((framesOf_live hfs f (List.mem_of_getElem? hf)).2.1 m t₁ y3).1
  rw [← live_open hL, v, live_between mB]
  exact switch_moment hx (rs := _) (gs := _) y1 hB

/-- In front of hearing sub-protocol number n + 1 of link l, n ≤ 6: the moment is at least 1. -/
theorem moment_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (hl : l < 24) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 6, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∃ L, t.link? = some L ∧ 1 ≤ L.check.frame.moment
  | 0, _, t, R', C', f => by
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f
    obtain ⟨L, hL, e⟩ := entry_moment hS hR O h1 hl f₀ f
    exact ⟨L, hL, by omega⟩
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + 3 + n) f
    obtain ⟨L, hL, e1⟩ := moment_at hS hR O h1 hl n (by omega) u Ru Cu fu
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
    obtain ⟨L', hL', g1⟩ := hear_by moUp_trans (fun _ _ => moUp_of_quiet)
      (fun _ _ _ _ _ _ _ _ => moUp_commit) hS hR O hl (by omega) (by omega) eL e u rs gs t d L hL
    exact ⟨L', hL', by omega⟩

/-- **WHAT THE CODE SWITCHING INTO GROUP l + 1 KEEPS, 1 ≤ l < 24.** -/
theorem kept_next (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub}
    {R R₀ R₂ : List Fmt.RoundView} {C C₀ C₂ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₂ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ fx : _root_.Tw.K2.Front, _root_.Tw.K2.firstFront t₀.st t₀.check.frame = .ok fx ∧
      switchKept t₂.check.frame.rows =
        (((K2.switchGain fx ++ K2.ownGain fx).filter (·.2)).map (·.1)).toArray := by
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * l + 5) 11
    (by rw [show 14 * l + 5 + 11 = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 14 * l + 7) 9
    (by rw [show 14 * l + 7 + 9 = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut (k := 14 * l + 9) 7
    (by rw [show 14 * l + 9 + 7 = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨fx, L₃, L₅, Q₃, Q₅, hfx, hL₃, hL₅, n3, n5, G, hG, em, ek, -, -, -⟩ :=
    fill_at hS hR O h1 h24 f₀ f₃ f₅ fu
  obtain ⟨L, G', -, -, -, hG', m1, m2, -⟩ := tail_rows hS hR O h24 fu f₂
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  -- the later sendings' flags are false
  have R3 : RecAll Z.first.codes Z.first.shape t₃ := open_recAll hS hR O (by omega)
    (draw_in_front hS hR O (l := l) (i := 3) (by omega) (by omega)) f₃
  have R5 : RecAll Z.first.codes Z.first.shape t₅ := open_recAll hS hR O (by omega)
    (draw_in_front hS hR O (l := l) (i := 5) (by omega) (by omega)) f₅
  obtain ⟨M₃, hM₃, mo3⟩ := moment_at hS hR O h1 h24 2 (by omega) t₃ R₃ C₃ f₃
  obtain ⟨M₅, hM₅, mo5⟩ := moment_at hS hR O h1 h24 4 (by omega) t₅ R₅ C₅ f₅
  obtain rfl : L₃ = M₃ := Option.some.inj (hL₃.symm.trans hM₃)
  obtain rfl : L₅ = M₅ := Option.some.inj (hL₅.symm.trans hM₅)
  have F3 := flags_false R3.ok (link_frame R3 hL₃).shape mo3
  have F5 := flags_false R5.ok (link_frame R5 hL₅).shape mo5
  refine ⟨fx, hfx, ?_⟩
  rw [switchKept_eq, m1, m2, em, ek]
  exact keptOf_three n3 F3 F5

end

#print axioms flags_false
#print axioms moment_at
#print axioms kept_next

end Meaning.K2
