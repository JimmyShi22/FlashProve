-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/MadeSent.lean: BEHIND AN ACCEPT OF THE SEATED SUB-PROTOCOL AT A SEGMENT's FIRST
PLACE (code switching, K2, with the segment's own "opened" joined behind it; segments 1 to 23) THE
PUBLIC TESTS OF "frame.sentIs" AND "ledger.treesAre" OF THAT SEGMENT ACCEPT, AT THE COMPOSED
MEANING's OWN PUBLIC TESTS. One closed fact by Lean's kernel; one statement with its proof: calls.

  `firstFit` · `first_fit`: BY THE KERNEL, at the written lists: the table's first place of segment
    l with piece 1 is entry 14 l + 2 of the written list of places (l from 1 to 23). `first_bent`: A
    NEGATIVE TEST: at entry 14 l + 3 the test rejects.
  `SentFence`: WHAT IS ASKED OF THE STATE IN FRONT BESIDE THE BOOK-KEEPING: TWO EQUATIONS on the
    chain's own state of the calls: its groups are the request's shape's; its shape is the public
    parameters'.
  **`made_sent`**: 1 ≤ l < 24 · b' is of the seat's lots, at the place (1, l, 1, K2) · b is b' with
  the segment's "opened" joined (`IM.Joined`) · the built segment l is no output head's · D₀.dS is
  the made datum (`sentDataAt`) · the fence gives `SentFence` at a state without a mark ⟹ ∀ s s', Fk
  (14 l + 2) s → IM.Yes ft b s s' → no mark in front or behind → IM.XK N linksW placesW E (14 l + 2)
  s = true → both tests accept at (z, s'). GENERAL IN THE LETTER E: of XK two tests of the
  book-keeping alone are spent (the state's shape; the book's counts).

HOW. The code switching's authors' `yes_joined_gives` opens the accept into the switch's and the
"opened"'s; their `around_at` shuts the output head's arm; the frame's authors' `framesOf_arms`
names "opened"; then Rec/MakerAtBorder.lean's four.

Limits. The output head's segment (entry 339) is NOT here. `SentFence` and the three premises on the
plan stand. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.

-/
import Johnson.Road.K4.Rec.MakerAtBorder
import Johnson.Desc.First.PubAllAt
import Johnson.P1K2R.Sits
import Johnson.P1K2R.HandsLinks
import Johnson.Top.H0.Walk.FrameRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec

open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk.Seat (framesOf_arms)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S ModelPart Pub Numbers PubData pubAll shift shapeAt bookAt standOf
  standAt Stand pubAll_more_sentIs pubAll_more_treesAre)
open VerifiableInference.Desc.First.FillSent (sentDataAt)
open VerifiableInference.Desc.Sound (step_ok_iff)
open IM (linksW placesW)
open ProofFile (Cl)

/-- A test on the written lists: the first place of segment l with piece 1 is entry k l. -/
def firstFit (k : ℕ → ℕ) : Bool :=
  (List.range' 1 23).all fun l =>
    decide ((placesW.find? fun q => q.link == some l &&
      q.piece == 1 + ((linksW[l]?).map shift).getD 0) = placesW[k l]?) && (placesW[k l]?).isSome

set_option maxRecDepth 1000000 in
theorem first_fit : firstFit (fun l => 14 * l + 2) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem first_bent : firstFit (fun l => 14 * l + 3) = false := by decide +kernel

theorem first_at {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24) : ∃ pl, placesW[14 * l + 2]? = some pl ∧
    (placesW.find? fun q => q.link == some l &&
      q.piece == 1 + ((linksW[l]?).map shift).getD 0) = some pl := by
  have h := List.all_eq_true.1 first_fit l (List.mem_range'_1.2 ⟨h1, by omega⟩)
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨pl, hp⟩ := Option.isSome_iff_exists.1 h.2
  exact ⟨pl, hp, h.1.trans hp⟩

/-- **What is asked of the state in front beside the book-keeping.** -/
structure SentFence (shape : Params.ReqShape) (s : S) : Prop where
  groups : s.check.frame.groups = reqGroups s.check.frame.shape
  shape : s.check.frame.shape = shape

/-- **The two tests behind an accept at a segment's first place.** -/
theorem made_sent {P : Type} {Fk : ℕ → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : ℕ}
    (h1 : 1 ≤ l) (h24 : l < 24) {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : IM.Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {N : Numbers} {ft : ℕ} (D₀ : PubData) (base : Pub → P × S → Bool) (z : P)
    {E : ℕ → S → Bool} {shape : Params.ReqShape}
    (hk : ∀ X, Z.p.built.links[l]? = some X → X.kind ≠ 2)
    (hdS : D₀.dS = sentDataAt shape N linksW placesW Z.p.built.links)
    (hF : ∀ s, Fk (14 * l + 2) s → s.failed = none → SentFence shape s) :
    ∀ s s', Fk (14 * l + 2) s → IM.Yes ft b s s' → s.failed = none → s'.failed = none →
      IM.XK N linksW placesW E (14 * l + 2) s = true →
      pubAll D₀ base (.more (some l) "frame.sentIs") (z, s') = true ∧
        pubAll D₀ base (.more (some l) "ledger.treesAre") (z, s') = true := by
  intro s s' hf hy h0 _ hx
  obtain ⟨rs, cols, n, e⟩ := hy
  have hd := ((step_ok_iff ft b s s' rs cols n).1 e).2.2.2
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx', rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have his := IM.k2_mem hx'
  have epx : x.place = { chain := 1, link := some l, piece := 1, kind := .K2 } := hpl
  rw [epx] at his
  obtain ⟨fs, f, m, rs', gs', hfs, hff, ⟨_, nn, _, _, arms⟩, _, hop, _, _⟩ :=
    P1K2.yes_joined_gives hJ his hd
  obtain ⟨hsh, _, _, hbk, _⟩ := IM.xk_parts hx
  obtain ⟨pl, hp, hfind⟩ := first_at h1 h24
  rw [hp] at hsh hbk
  have Fc := hF s hf h0
  have hn : s.st.oracles.size = N.msgsAt (some pl) := by
    simp only [bookAt, Bool.and_eq_true, beq_iff_eq] at hbk
    exact hbk.2
  -- the switch's own accept, in the dress of a segment
  have hsw : VerifiableInference.Desc.First.K2.decideWith _root_.Tw.K2.sendByL8
      (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x.name .link nn) s rs'
      gs' = .ok m := by
    rcases arms with ⟨ha, _⟩ | ⟨_, _, _, _, _, hh, _, _, hhere, _⟩ | ⟨_, _, _, hw⟩
    · exact nomatch ha
    · exfalso
      have hFr := (P1K2.around_at h1 h24).1
      unfold P1K2.frontLinkB at hFr
      rw [hp] at hFr
      have a0 : standAt linksW pl = .between := of_decide_eq_true hFr
      unfold shapeAt at hsh
      simp only [Bool.and_eq_true, beq_iff_eq, a0] at hsh
      have hbt : standOf s = .between := hsh.1.1
      unfold standOf at hbt
      rw [hhere] at hbt
      have hb2 : (if s.inLink then Stand.link ModelPart.head else Stand.headFront) = Stand.between :=
        hbt
      split at hb2 <;> cases hb2
    · exact hw
  rw [pubAll_more_sentIs, pubAll_more_treesAre, hdS]
  rcases framesOf_arms hfs hff with ⟨X, hX, hk2, _⟩ | ⟨h0', _⟩ |
      ⟨_, X, p, Pa, hX, _, _, rfl, _, hO, _⟩ | ⟨_, X, hp', Pa, hX, _, _, rfl, _, hO, _⟩
  · exact absurd hk2 (hk X hX)
  · omega
  · rw [hO] at hop
    exact ⟨sentIs_made_att_at rfl hsw hop Fc.groups hfind hn Fc.shape,
      treesAre_made_att_at hop hX rfl⟩
  · rw [hO] at hop
    exact ⟨sentIs_made_lay_at rfl hsw hop Fc.groups hfind hn Fc.shape,
      treesAre_made_lay_at hop hX rfl⟩

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.first_fit
#print axioms OnBytes.Road.K4.Rec.first_bent
#print axioms OnBytes.Road.K4.Rec.made_sent
