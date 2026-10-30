-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsK2.lean: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre»
(Johnson/Desc/Sound/SmpPlaces.lean): THE DEBT SendsOn (Johnson/IMR/SendsFold.lean) AT KIND K2's 25
PLACES, AT THE TERM snAt (Johnson/Desc/K12/Door/SentAtPlace.lean), UNDER ONE NAMED STRUCTURE OF
THREE SENTENCES ON REACHED STATES: K2Fences: «whatever front the code
switch takes off the state announces just the plan's messages n.sent»: THE FIRST CLAUSE OF THE FENCE K2.Fence (Johnson/Top/H0/Tw/K2C/SendsOn.lean), WHICH IS PROVED AT ALL 25 SWITCHES, IN SCOPE, AT THE FOLD's OWN STATES (fence1_link · fence1_head · fence1_finish, Johnson/IMR/MsgsBehind.lean, NOT CALLED HERE:
SO THE THREE ARE PREMISES HERE, IN ITS THEOREMS' OWN LETTERS WITH Fence1 UNFOLDED; the join is three calls where both stand).
CALLED, ALL K2's FILES' (Johnson/Top/H0/Tw/K2C/): K2.yes_seated · SeatedBut (SeatedAt.lean) · K2.yes_codes · the four …Q_codes (KeepsWhole.lean) · K2.yes_has · the four …Q_size (StillKeeps.lean) · the four …Q_book (BookKept.lean) · firstFront_keeps.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.

  appends_of_seatedBut   the bridge of Johnson/IMR/SendsBridge.lean at SeatedBut (an older tree may turn in its count of lists alone).
  frontOf_codes     the front's statement has the state's code table.
  k2_yes_sends      THE LAW AT THE SWITCH's DECISION: an accepting, the code table in front, the fence's first clause at the state in front ⟹ the code table behind · Appends codes [sent] · in step behind (whatever stood in front).
  K2Fences ft Z G₀ c s₀   the three sentences on reached states.
  sends_K2_link · sends_K2_finish   the lot's own sub-protocol at (1, some l, pc, K2) | (1, none, 1, K2): SendsOn at the reached states in front of it, at snAt.
What is not claimed. K2Fences. The batching and behind it (50) · K12 (1). The plan's side. No soundness.
-/
import Johnson.IMR.SendsLeft
import Johnson.IMR.K2Seat
import Johnson.Top.H0.Tw.K2C.SeatedAt
import Johnson.Top.H0.Tw.K2C.KeepsWhole
import Johnson.Top.H0.Tw.K2C.StillKeeps
import Johnson.Top.H0.Tw.K2C.BookKept

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice TreeBook TreeLay layTrees)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 FrontOf SeatedBut)
open VerifiableInference.Desc.K12.Coin (placesOf Appends)
open VerifiableInference.Desc.K12.Door (snAt)
open ProofFile (Cl)

theorem places_of_seatedBut {B B' : TreeBook} {n n0 : ℕ} {lay : TreeLay} {num : ℕ → ℕ}
    {src : ℕ → Fmt.Src} (h : SeatedBut B B' n n0 lay num src) :
    B'.place.toList = B.place.toList ++ placesOf B.trees.size n lay := by
  apply List.ext_getElem?
  intro j
  rw [Array.getElem?_toList]
  by_cases hj : j < B.place.size
  · rw [h.places j hj, List.getElem?_append_left (by rw [Array.length_toList]; exact hj),
      Array.getElem?_toList]
  · rw [List.getElem?_append_right (by rw [Array.length_toList]; omega), Array.length_toList]
    unfold placesOf
    rw [List.getElem?_map]
    by_cases hi : j - B.place.size < n
    · have e := h.new (j - B.place.size) hi
      rw [h.step, show B.place.size + (j - B.place.size) = j by omega] at e
      rw [e, List.getElem?_range hi]
      rfl
    · rw [Array.getElem?_eq_none (by rw [h.count]; omega),
        List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl

theorem shapes_of_seatedBut {B B' : TreeBook} {n n0 : ℕ} {lay : TreeLay} {num : ℕ → ℕ}
    {src : ℕ → Fmt.Src} (h : SeatedBut B B' n n0 lay num src) :
    B'.trees.toList.map (·.shape) = B.trees.toList.map (·.shape) ++ lay.shapes.toList := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, Array.getElem?_toList]
  by_cases hj : j < B.trees.size
  · obtain ⟨t, t', e1, e2, -, -, e3, -⟩ := h.trees j hj
    rw [e2, List.getElem?_append_left
      (by rw [List.length_map, Array.length_toList]; exact hj), List.getElem?_map,
      Array.getElem?_toList, e1, Option.map_some, Option.map_some, e3]
  · rw [List.getElem?_append_right (by rw [List.length_map, Array.length_toList]; omega),
      List.length_map, Array.length_toList, Array.getElem?_toList]
    by_cases hi : j - B.trees.size < lay.shapes.size
    · obtain ⟨t, e, hs, -⟩ := h.made (j - B.trees.size) hi
      rw [show B.trees.size + (j - B.trees.size) = j by omega] at e
      rw [e, Option.map_some, hs, Array.getElem?_eq_getElem hi, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hi]
      rfl
    · rw [Array.getElem?_eq_none (by rw [h.size]; omega), Array.getElem?_eq_none (by omega)]
      rfl

/-- The bridge at SeatedBut. -/
theorem appends_of_seatedBut {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    {B B' : TreeBook} {n0 : ℕ} {num : ℕ → ℕ} {src : ℕ → Fmt.Src}
    (hl : layTrees codes sent = some lay) (h : SeatedBut B B' sent.size n0 lay num src) :
    Appends codes [sent] B B' := by
  refine ⟨{ places := placesOf B.trees.size sent.size lay ++ [],
            shapes := lay.shapes.toList ++ [] }, ?_, ?_, ?_⟩
  · show ((layTrees codes sent).bind fun lay => _) = _
    rw [hl]
    rfl
  · show _ = _ ++ (placesOf B.trees.size sent.size lay ++ [])
    rw [List.append_nil]
    exact places_of_seatedBut h
  · show _ = _ ++ (lay.shapes.toList ++ [])
    rw [List.append_nil]
    exact shapes_of_seatedBut h

/-- The front's statement has the state's code table. -/
theorem frontOf_codes {p : P2} {s : S} {x : _root_.Tw.K2.Front} (h : FrontOf p s x) :
    x.st.codes = s.st.codes := by
  rcases h with ⟨-, h⟩ | ⟨-, a, G, -, -, rfl⟩ | ⟨-, a, G, -, -, rfl⟩
  · exact (VerifiableInference.Desc.First.K2.firstFront_keeps
      VerifiableInference.Desc.Ground.groundKeeps_grows h).1
  · rfl
  · rfl

/-- **THE LAW AT THE SWITCH's DECISION.** -/
theorem k2_yes_sends {p : P2} {sent : Array OracleNotice} {codes : Codes} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : VerifiableInference.Desc.First.K2.decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s')
    (hc : s.st.codes = codes)
    (hF : ∀ x, FrontOf p s x → _root_.Tw.K2.switchNotices x.T x.others = sent) :
    s'.st.codes = codes ∧ Appends codes [sent] s.book s'.book ∧ InStep s' := by
  obtain ⟨x, lay, hx, hl, -, St⟩ := VerifiableInference.Desc.First.K2.yes_seated h
  rw [hF x hx, frontOf_codes hx, hc] at hl
  rw [hF x hx] at St
  exact ⟨(VerifiableInference.Desc.First.K2.yes_codes h).trans hc, appends_of_seatedBut hl St,
    (VerifiableInference.Desc.First.K2.yes_has h).symm⟩

/-- A step that leaves the code table, the number of oracle messages and the book, behind a sending. -/
theorem sends_then_calm {codes : Codes} {snd : List (Array OracleNotice)} {s m s' : S}
    (h : m.st.codes = codes ∧ Appends codes snd s.book m.book ∧ InStep m) (k : Calm m s') :
    s'.st.codes = codes ∧ Appends codes snd s.book s'.book ∧ InStep s' := by
  obtain ⟨k1, k2, k3⟩ := k
  refine ⟨k1.trans h.1, by rw [k3]; exact h.2.1, ?_⟩
  have := h.2.2
  unfold InStep at this ⊢
  rw [k2, k3]
  exact this

theorem headOpenQ_calm {HP : VerifiableInference.Desc.First.K2.HeadPar} {s s' : S}
    (h : VerifiableInference.Desc.First.K2.headOpenQ HP s = .ok s') : Calm s s' :=
  ⟨VerifiableInference.Desc.First.K2.headOpenQ_codes h,
    VerifiableInference.Desc.First.K2.headOpenQ_size h,
    (VerifiableInference.Desc.First.K2.headOpenQ_book h).1⟩

theorem finishFrontQ_calm {s s' : S}
    (h : VerifiableInference.Desc.First.K2.finishFrontQ s = .ok s') : Calm s s' :=
  ⟨VerifiableInference.Desc.First.K2.finishFrontQ_codes h,
    VerifiableInference.Desc.First.K2.finishFrontQ_size h,
    (VerifiableInference.Desc.First.K2.finishFrontQ_book h).1⟩

theorem finishBehindQ_calm {s s' : S}
    (h : VerifiableInference.Desc.First.K2.finishBehindQ s = .ok s') : Calm s s' :=
  ⟨VerifiableInference.Desc.First.K2.finishBehindQ_codes h,
    VerifiableInference.Desc.First.K2.finishBehindQ_size h,
    (VerifiableInference.Desc.First.K2.finishBehindQ_book h).1⟩

/-- **The three sentences on reached states**: fence1_link · fence1_head · fence1_finish, Fence1 unfolded. -/
structure K2Fences (ft : ℕ) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (s₀ : S) : Prop where
  link : ∀ l < 25, ∀ s, ReachedAt ft c.blocksInOrder s₀ (14 * l + 2) s → ∀ (Pp : P1K2.Prep) (n : P1K2.Nums)
    (a : Place) (nm : String) (st : VerifiableInference.Desc.First.K2.At),
    P1K2.prepOf Z G₀ = some Pp → P1K2.numsAt Pp (some l) = some n → st ≠ .finish →
    ∀ x, FrontOf (k2P Z a nm st n) s x → _root_.Tw.K2.switchNotices x.T x.others = n.sent
  head : ∀ s, ReachedAt ft c.blocksInOrder s₀ 339 s → ∀ (Pp : P1K2.Prep) (n : P1K2.Nums)
    (a : Place) (nm : String) (st : VerifiableInference.Desc.First.K2.At),
    P1K2.prepOf Z G₀ = some Pp → P1K2.numsAt Pp (some 24) = some n → st ≠ .finish →
    ∀ x, FrontOf (k2P Z a nm st n) s x → _root_.Tw.K2.switchNotices x.T x.others = n.sent
  finish : ∀ s, ReachedAt ft c.blocksInOrder s₀ 353 s → ∀ (Pp : P1K2.Prep) (n : P1K2.Nums)
    (a : Place) (nm : String) (m : S),
    P1K2.prepOf Z G₀ = some Pp → P1K2.numsAt Pp none = some n →
    VerifiableInference.Desc.First.K2.finishFrontQ s = .ok m →
    ∀ x, FrontOf (k2P Z a nm .finish n) m x → _root_.Tw.K2.switchNotices x.T x.others = n.sent

/-- **K2's lot's own sub-protocol at a place inside a link.** -/
theorem sends_K2_link {ft : ℕ} {Z : ProofFile.Pub} {G : ProofFile.Ground} {Gd : S → Prop} {l pc j : ℕ}
    {b' : Block S Cl} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G)
    (hp : b'.place = { chain := 1, link := some l, piece := pc, kind := .K2 })
    (hW : placesW[j]? = some { chain := 1, link := some l, piece := pc, kind := .K2 })
    (hF : ∀ s, Gd s → ∀ (Pp : P1K2.Prep) (n : P1K2.Nums) (a : Place) (nm : String)
      (st : VerifiableInference.Desc.First.K2.At), P1K2.prepOf Z G = some Pp →
      P1K2.numsAt Pp (some l) = some n → st ≠ .finish →
      ∀ x, FrontOf (k2P Z a nm st n) s x → _root_.Tw.K2.switchNotices x.T x.others = n.sent) :
    SendsOn ft Z.first.codes Gd (snAt Z G placesW j) b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨x, hx, rfl⟩ := lot_K2 hL hb' (by rw [hp])
  have hp' : x.place = { chain := 1, link := some l, piece := pc, kind := .K2 } := hp
  have hK := k2_mem hx
  rw [hp'] at hK
  intro s s' rs cols n hg hy hc
  obtain ⟨-, gs, hd⟩ := VerifiableInference.Desc.K1.step_ok ft _ s s' rs cols n hy
  have hd' : x.decide s (rs.map VerifiableInference.Desc.noDigest) gs = .ok s' := hd
  rcases hK with ⟨-, hm⟩ | ⟨Pp, nn, hP, hn, harm⟩
  · obtain ⟨e, he⟩ := hm s (rs.map VerifiableInference.Desc.noDigest) gs
    rw [he] at hd'
    cases hd'
  · have hn' : P1K2.numsAt Pp (some l) = some nn := hn
    have esn : snAt Z G placesW j = [nn.sent] := by
      rw [VerifiableInference.Desc.K12.Door.snAt_k2 Z G placesW j pc (some l) hW, hP]
      show ((P1K2.numsAt Pp (some l)).map (·.sent)).toList = _
      rw [hn']
      rfl
    rw [esn]
    rcases harm with ⟨h0, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
    · cases h0
    · rw [ex] at hd'
      obtain ⟨m, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok hd'
      obtain ⟨a1, a2, a3⟩ := sends_then_calm
        (k2_yes_sends h1 hc (hF s hg Pp nn _ _ .head hP hn' (by decide))) (headOpenQ_calm h2)
      exact ⟨a1, a2, fun _ => a3⟩
    · rw [ex] at hd'
      obtain ⟨a1, a2, a3⟩ := k2_yes_sends hd' hc (hF s hg Pp nn _ _ .link hP hn' (by decide))
      exact ⟨a1, a2, fun _ => a3⟩

set_option maxRecDepth 1000000 in
theorem place_353 : placesW[353]? = some { chain := 1, link := none, piece := 1, kind := .K2 } := by
  decide +kernel

/-- **K2's finish (353).** -/
theorem sends_K2_finish {ft : ℕ} {Z : ProofFile.Pub} {G : ProofFile.Ground} {Gd : S → Prop}
    {b' : Block S Cl} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G)
    (hp : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    (hF : ∀ s, Gd s → ∀ (Pp : P1K2.Prep) (n : P1K2.Nums) (a : Place) (nm : String) (m : S),
      P1K2.prepOf Z G = some Pp → P1K2.numsAt Pp none = some n →
      VerifiableInference.Desc.First.K2.finishFrontQ s = .ok m →
      ∀ x, FrontOf (k2P Z a nm .finish n) m x → _root_.Tw.K2.switchNotices x.T x.others = n.sent) :
    SendsOn ft Z.first.codes Gd (snAt Z G placesW 353) b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨x, hx, rfl⟩ := lot_K2 hL hb' (by rw [hp])
  have hp' : x.place = { chain := 1, link := none, piece := 1, kind := .K2 } := hp
  have hK := k2_mem hx
  rw [hp'] at hK
  intro s s' rs cols n hg hy hc
  obtain ⟨-, gs, hd⟩ := VerifiableInference.Desc.K1.step_ok ft _ s s' rs cols n hy
  have hd' : x.decide s (rs.map VerifiableInference.Desc.noDigest) gs = .ok s' := hd
  rcases hK with ⟨-, hm⟩ | ⟨Pp, nn, hP, hn, harm⟩
  · obtain ⟨e, he⟩ := hm s (rs.map VerifiableInference.Desc.noDigest) gs
    rw [he] at hd'
    cases hd'
  · have hn' : P1K2.numsAt Pp none = some nn := hn
    have esn : snAt Z G placesW 353 = [nn.sent] := by
      rw [VerifiableInference.Desc.K12.Door.snAt_k2 Z G placesW 353 1 none place_353, hP]
      show ((P1K2.numsAt Pp none).map (·.sent)).toList = _
      rw [hn']
      rfl
    rw [esn]
    rcases harm with ⟨-, ex⟩ | ⟨l', HP, h0, -, -⟩ | ⟨l', h0, -⟩
    · rw [ex] at hd'
      obtain ⟨m₂, h12, h3⟩ := VerifiableInference.Desc.Keeps.ebind_ok hd'
      obtain ⟨m₁, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok h12
      have c1 : Calm s m₁ := finishFrontQ_calm h1
      obtain ⟨a1, a2, a3⟩ := sends_then_calm
        (k2_yes_sends h2 (c1.1.trans hc) (hF s hg Pp nn _ _ m₁ hP hn' h1)) (finishBehindQ_calm h3)
      rw [c1.2.2] at a2
      exact ⟨a1, a2, fun _ => a3⟩
    · cases h0
    · cases h0

end IM

#print axioms IM.sends_K2_link
#print axioms IM.sends_K2_finish
#print axioms IM.appends_of_seatedBut
#print axioms IM.frontOf_codes
#print axioms IM.k2_yes_sends
