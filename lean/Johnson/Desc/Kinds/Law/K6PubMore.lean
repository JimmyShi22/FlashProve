-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PubMore.lean: OF THE PUBLIC TESTS AND SENTENCES THAT ARE OPEN BEHIND THE
SUB-PROTOCOL AT THE OUTPUT HEAD (Law/K6PubKept.lean: open342: fifteen, at the full chain), THREE
PAYMENTS AT THE COMPOSED MEANING OF THE OPEN CLAIMS (Johnson/Desc/Sound/MgAll.lean: mgAll):
lookOut 24 3 is kept; formsInT 24 4 "weights" is true of an empty list; every public SENTENCE that
is open behind holds. Statements and proofs.

WHAT IT IS NOT. Implications. Nothing on soundness. Five of the fifteen tests are not touched here:
lookIn 24 8 and formsInT at "objects", "own", "planes", "join". sentences_behind asks of the
innermost meaning Mg that its own sentences hold everywhere (hPP: at the base meaning of
Johnson/Desc/Sound/MgBase.lean they are True) and that its list of extra public tests is empty
(hMore). No values are shown at which the premises hold together.

  freeB_touch      a stretch of free slots below the slots that a hearing touches stays free.
  k3OnOut_takes    the lookup's test behind its sub-protocol (k3OnOut:
                   Johnson/Desc/First/Look/K3Borders.lean) is kept by every step that leaves what
                   the lookup heard and whose ledger has taken some numbers from the next free one
                   on (Law/Takes.lean: Takes).
  takes_at_piece   an accepting step of the piece takes so.
  kept_lookOut     SO lookOut 24 3 stays true.
  runs_at_head     where segment 24 is the head's in the meaning's list of segments: the five names'
                   lists of runs, written out (Johnson/Desc/Sound/MgAt/Runs.lean: runs_head).
  weights_true     formsInT 24 4 "weights": no run stands under that name.
  sentences_behind MAIN: see its docstring.

LETTERS. No letter stands under "there is" in a conclusion but takes_at_piece's F, G, t: F, G are
pinned by the two states' ledgers; t: by Takes' own first clause (G.next = F.next + t).

-/
import Johnson.Desc.Kinds.Law.K6PubKept
import Johnson.Desc.Kinds.Law.K6Makes
import Johnson.Desc.Kinds.Law.TakesAt
import Johnson.Desc.Sound.MgAt.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First (S)

/-- A stretch of free slots that ends at or below lo stays free where the slots from lo on alone
are touched. -/
theorem freeB_touch {F G : Fork} {lo hi first n : Nat} (T : Touch F G lo hi) (hS : Sized F)
    (hlo : first + n ≤ lo) (h : K3.freeB F first n = true) : K3.freeB G first n = true := by
  unfold K3.freeB at h ⊢
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  refine ⟨by rw [T.ns]; exact h.1, fun j hj => ?_⟩
  have hj' := List.mem_range.1 hj
  have h1 := h.2 j hj
  have hinF : first + j < F.gotF.size := by
    rw [hS.2.2]
    omega
  have hinG : first + j < G.gotF.size := by
    rw [T.sized.2.2, T.ns]
    omega
  have hnF : ¬ OnBytes.PscRun.Filled F (first + j) := by
    unfold OnBytes.PscRun.Filled
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hinF] at h1 ⊢
    simpa using h1
  have hnG : ¬ OnBytes.PscRun.Filled G (first + j) := fun hf =>
    hnF ((T.out (first + j) (Or.inl (by omega))).2.2.1 hf)
  unfold OnBytes.PscRun.Filled at hnG
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hinG] at hnG ⊢
  simpa using hnG

/-- **THE LOOKUP's TEST BEHIND ITS SUB-PROTOCOL IS KEPT** by a step that leaves what the lookup
heard and whose ledger has taken t numbers from the next free one on. -/
theorem k3OnOut_takes (p : First.Look.P) (s s' : S) (F G : Fork) (t : Nat)
    (hF : s.fork? = some F) (hG : s'.fork? = some G)
    (hh : K3.heardAt p.digits s' = K3.heardAt p.digits s) (T : Takes F G t)
    (h : K3.k3OnOut p s = true) : K3.k3OnOut p s' = true := by
  unfold K3.k3OnOut at h ⊢
  rw [hh, hG]
  rw [hF] at h
  cases hs : p.shape with
  | none =>
    rw [hs] at h
    cases h
  | some sh =>
    cases hg : K3.heardAt p.digits s with
    | none =>
      rw [hs, hg] at h
      cases h
    | some g =>
      rw [hs, hg] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩ := h
      have hSF : Sized F := by
        unfold K3.sizedB at c8
        simp only [Bool.and_eq_true, beq_iff_eq] at c8
        exact ⟨c8.1.1, c8.1.2, c8.2⟩
      refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, ?_⟩, ?_⟩, ?_⟩, c10⟩, c11⟩, c12⟩, c13⟩
      · rw [T.next]
        omega
      · unfold K3.sizedB
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨T.touch.sized.1, T.touch.sized.2.1⟩, T.touch.sized.2.2⟩
      · exact freeB_touch T.touch hSF (by omega) c9

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Model (Fork)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning Pub pubOfItems)
open VerifiableInference.Desc.Sound (Piece Frame MsgT MgData mgAll onQ pubQ openQ linksFull)

section Piece

variable {P Cells Tok : Type} {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **An accepting step of the piece takes some numbers from the ledger's next free one on**, where
the ledger in front is well laid. -/
theorem takes_at_piece (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b)
    (hW : WellLaid ((seatAt Wp.hS (readsOf Wp)).ledger a.1.2)) (F : Fork)
    (hF : a.1.2.fork? = some F) :
    ∃ G t, b.1.2.fork? = some G ∧ Takes F G t := by
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ h
  obtain ⟨_, hd'⟩ := canonical_of_below b6 a.1.2 b.1.2 rs gs hd
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp h6
  have hr : readsOf Wp = iU3 := by
    unfold readsOf
    rw [hu]
    rfl
  subst hbb
  obtain ⟨G, hG⟩ := fork_behind H a b τ h
  have e1 : (seatAt Wp.hS iU3).ledger a.1.2 = F := by
    show a.1.2.fork?.getD {} = F
    rw [hF]
    rfl
  have e2 : (seatAt Wp.hS iU3).ledger b.1.2 = G := by
    show b.1.2.fork?.getD {} = G
    rw [hG]
    rfl
  rw [hr, e1] at hW
  obtain ⟨t, _, T⟩ := blockAt_takes Wp.hS iU3 (workOf Wp) l a.1.2 b.1.2 rs gs
    (by rw [e1]; exact ⟨hW.2.1, hW.2.2, hW.1⟩) hd'
  rw [e1, e2] at T
  exact ⟨G, t, hG, T⟩

end Piece

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {l : ℕ} {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **The lookup's test lookOut 24 3 stays true across an accepting step.** -/
theorem kept_lookOut (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b)
    (hW : WellLaid ((seatAt Wp.hS (readsOf Wp)).ledger a.1.2))
    (hsort : First.Look.k3SortAt Wp 24 3 = some false)
    (ht : (mgAll D Mg).pub (.lookOut 24 3) a.1 = true) :
    (mgAll D Mg).pub (.lookOut 24 3) b.1 = true := by
  rw [Sound.mgAll_pub, First.pubAll_lookOut D.pubD Mg.pub 24 3 false hsort] at ht ⊢
  unfold First.Look.lookOutC at ht ⊢
  cases hp : First.Look.placeAt D.pubD.d3.X 24 false with
  | none =>
    rw [hp] at ht
    cases ht
  | some p =>
    rw [hp] at ht
    have ht' : K3.k3OnOut p a.1.2 = true := ht
    show K3.k3OnOut p b.1.2 = true
    cases hF : a.1.2.fork? with
    | none =>
      exfalso
      unfold K3.k3OnOut at ht'
      rw [hF] at ht'
      cases hs : p.shape with
      | none =>
        rw [hs] at ht'
        cases ht'
      | some sh =>
        cases hg : K3.heardAt p.digits a.1.2 with
        | none =>
          rw [hs, hg] at ht'
          cases ht'
        | some g =>
          rw [hs, hg] at ht'
          cases ht'
    | some F =>
      obtain ⟨G, t, hG, T⟩ := takes_at_piece H a b τ h hW F hF
      refine k3OnOut_takes p a.1.2 b.1.2 F G t hF hG ?_ T ht'
      obtain ⟨o, F1, X, Q, ho, _, _, e⟩ := k6_behind H a b τ h
      unfold K3.heardAt
      rw [lookHeard_behind H a b τ h, e]
      unfold First.S.tl?
      rw [ho]

/-- **Where segment 24 is the head's in the meaning's list of segments: the five names' runs.** -/
theorem runs_at_head (hl : D.links[24]? = some .head) :
    D.runs 24 3 "objects" = [(2, "objects"), (2, "guests")] ∧
      D.runs 24 3 "planes" = [(2, "planes")] ∧ D.runs 24 4 "join" = [(3, "join")] ∧
      D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")] ∧
      D.runs 24 4 "weights" = [] := by
  obtain ⟨r1, r2, r3, r4, r5, _⟩ := Sound.runs_head
  exact ⟨(Sound.runsAt_of D.links 24 .head hl 3 "objects").trans r1,
    (Sound.runsAt_of D.links 24 .head hl 3 "planes").trans r2,
    (Sound.runsAt_of D.links 24 .head hl 4 "join").trans r3,
    (Sound.runsAt_of D.links 24 .head hl 4 "own").trans r4,
    (Sound.runsAt_of D.links 24 .head hl 4 "weights").trans r5⟩

/-- **No run stands under "weights": the test is true of the empty list.** -/
theorem weights_true (hw : D.runs 24 4 "weights" = []) (x : P × S) :
    (mgAll D Mg).pub (.formsInT 24 4 "weights") x = true := by
  rw [Sound.mgAll_pub, First.pubAll_formsInT]
  have e : D.pubD.runs 24 4 "weights" = [] := hw
  rw [e]
  rfl

/-- **EVERY PUBLIC SENTENCE THAT IS OPEN BEHIND THE SUB-PROTOCOL AT THE OUTPUT HEAD HOLDS THERE**,
at the full chain. a: in front, inside the promise, without a mark; b: behind an accept. Of the
eight items that are open behind, leftOn 24 has a sentence of the lookup's: it comes from "left 24"
in front by the maker's lemma (Law/K6Makes.lean: leftOn_below); at the other seven the
composed meaning hands the innermost meaning's sentence on (hPP). -/
theorem sentences_behind
    {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
    (H : Seated Wp .two Fr q 24 bef B bS) (hplan : planB Wp = true)
    (hMore : Mg.more = {}) (hPP : ∀ i x, Mg.pubP i x) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (ha : onQ (Fr := Fr) D.N (mgAll D Mg) linksFull (First.flatPlacesOf linksFull true)
      (fun a => a) 341 a)
    (hm : a.1.2.failed = none) (hb : q.ior.red.out a τ = some b) (hL : K6Left Wp a.1.2) :
    ∀ i ∈ pubQ (mgAll D Mg).more linksFull (First.flatPlacesOf linksFull true) (341 + 1),
      (mgAll D Mg).pubP i b.1 := by
  intro i hi
  have A := Sound.onParts_of_on D.N (mgAll D Mg) linksFull _ (fun a => a) 341 a ha hm
  have hi' : i ∈ [First.Pub.ledger 24, .linkFresh 24, .freeAbove 24,
      .more (some 24) "frame.sentIs", .more (some 24) "ledger.treesAre", .lookOut 24 3,
      .lookIn 24 8, .leftOn 24, .indexIs, .indexThere, .formsInT 24 3 "objects",
      .formsInT 24 4 "own", .formsInT 24 3 "planes", .formsInT 24 4 "join",
      .formsInT 24 4 "weights"] := by
    rw [Sound.mgAll_more_closed D Mg hMore] at hi
    exact open342 ▸ List.mem_append_left _ hi
  have other : ∀ j : Pub, (∀ m, j ≠ .left m) → (∀ m, j ≠ .leftOn m) →
      (mgAll D Mg).pubP j b.1 := by
    intro j h1 h2
    rw [Sound.mgAll_pubP, First.Look.fill_pubP_other _ _ _ j b.1 h1 h2]
    show if First.FillP1.p1Item j = true then True else Mg.pubP j b.1
    split
    · trivial
    · exact hPP j b.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  case inr.inr.inr.inr.inr.inr.inr.inl =>
    have hleft : (mgAll D Mg).pubP (.left 24) a.1 := A.pubP _ (by
      rw [Sound.mgAll_more_closed D Mg hMore]
      decide +kernel)
    rw [Sound.mgAll_pubP] at hleft ⊢
    obtain ⟨p, hp, Lf⟩ : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 a.1.2 := hleft
    obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ hb
    exact ⟨p, hp, leftOn_below Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd (k6On_front H hplan a b τ hb hL) p
      Lf⟩
  all_goals exact other _ (fun _ => by simp) (fun _ => by simp)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.freeB_touch
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k3OnOut_takes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.takes_at_piece
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.kept_lookOut
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.runs_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.weights_true
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.sentences_behind
