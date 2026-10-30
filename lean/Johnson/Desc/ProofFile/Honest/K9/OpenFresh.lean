-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/OpenFresh.lean: BEHIND A SEGMENT's OPENING THE BOOK-KEEPING AND THE LEDGER ARE AS THE
BATCHING's DRAW WANTS THEM, BUT FOR THE MOMENTS: in the goals' scope, at each of the 25 segments of the first chain: behind
every accepting decision of the sub-protocol that opens the segment (the code switch; in segment 0 the first sending), if
book-keeping L and a ledger F are open there.

  `Opened L F`     the draw has not run; the list of arrays is a segment's and is closed; one moment has passed; and `Fresh F`
                   (Honest/K9/ReadyOf.lean)
  `empty_of_cr`, `fresh_of_cr`   "the ledger is empty", and `Fresh`, are read off `cr` (Honest/K9/CrAre.lean)
  `fresh_start`    the ledger from which a sub-proof starts is `Fresh`, where the plan's is `Plain` (Honest/K9/PlanFresh.lean)
  `frameAt_pub`, `zeroAt_pub`   a segment's frame's letters are read off the segment's record
  `headOpen_opened`, `yesGives_opened`   the head's opening; what a yes of a code switch gives, in each of its three forms
  **`opened_at`**    THE STATEMENT, at the sub-protocol number `k2Number l` of the flat list

How. Who stands at that number, and what its yes gives, is the library's (Johnson/IMR/WaitsBehindSwitch.lean's road:
`IM.k2_head_of`, `IM.k2_link_sits`, `IM.first_sits`, `P1K2.yes_alone_gives`, `P1K2.yes_joined_gives`, `HashBuild.joined_under`,
`IM.frames_arms`); what the three steps "opened" lay: Johnson/Top/H0/Walk/FrameLaw.lean; the plans' two sentences:
Honest/K9/BuiltFresh.lean.

Limits. In the goals' scope, at the hash function `secondHashFunction`. It shows of no state that it is reached. This file proves no
property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.ReadyOf
import Johnson.Desc.ProofFile.Honest.K9.BuiltFresh
import Johnson.Desc.ProofFile.Honest.K9.CrAre
import Johnson.IMR.WaitsBehindSwitch
import Johnson.IMR.FrameSeat
import Johnson.Desc.First.Link.Law.LooksK2
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Top.H0.Tw.K2C.Reply

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (Closed Plain cr lnk k2_link_kept)
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero)
open Meaning.K2
open ProofFile (Cl)

/-- **What stands open behind a segment's opening.** -/
structure Opened (L : LinkCtx) (F : Fork) : Prop where
  handed : L.handed = false
  list : Closed L.list
  moments : L.moments = 1
  fresh : Fresh F

/-- "The ledger is empty" is read off `cr`. -/
theorem empty_of_cr {F G : Fork} (h : cr G = cr F) : Desc.K9.ledgerEmpty G = Desc.K9.ledgerEmpty F := by
  have key : ∀ H : Fork, (H.trees.all fun X => X.rows.all fun r => r.L.all isZeroE) =
      ((H.trees.map fun X => X.rows.map (·.L)).all fun X => X.all fun L => L.all isZeroE) := by
    intro H
    simp
  have a : (G.trees.map fun X => X.rows.map (·.L)) = F.trees.map fun X => X.rows.map (·.L) :=
    congrArg (·.1) h
  have b : G.LS = F.LS := congrArg (·.2.1) h
  have c : G.c0 = F.c0 := congrArg (·.2.2.1) h
  unfold Desc.K9.ledgerEmpty
  rw [key G, key F, a, b, c]

/-- So is `Fresh`. -/
theorem fresh_of_cr {F G : Fork} (h : cr G = cr F) (f : Fresh F) : Fresh G :=
  ⟨(congrArg (·.2.2.2.2.1) h : G.thetaDrawnF = F.thetaDrawnF).trans f.drawn,
    (congrArg (·.2.2.2.1) h : G.nClaim = F.nClaim).trans f.count,
    (congrArg (·.2.2.2.2.2) h : G.doorShutF = F.doorShutF).trans f.door,
    (empty_of_cr h).trans f.empty⟩

/-- The ledger that is laid with n empty slots over weights at 0. -/
theorem fresh_laid {F : Fork} (h : Plain F) (n : ℕ) : Fresh (emptySlots (weightsAtZero F) n) := by
  refine ⟨h.drawn, h.count, h.door, ?_⟩
  have z : isZeroE zeroE = true := rfl
  simp only [Desc.K9.ledgerEmpty, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  refine ⟨⟨fun X hX r hr v hv => ?_, fun v hv => ?_⟩, ?_⟩
  · have hX' : X ∈ F.trees.map fun X =>
        { X with rows := X.rows.map fun r => { r with L := Array.replicate X.K zeroE } } := hX
    obtain ⟨X0, -, rfl⟩ := Array.mem_map.1 hX'
    obtain ⟨r0, -, rfl⟩ := Array.mem_map.1 hr
    rw [(Array.mem_replicate.1 hv).2]
    exact z
  · have hv' : v ∈ Array.replicate n zeroE := hv
    rw [(Array.mem_replicate.1 hv').2]
    exact z
  · show isZeroE F.c0 = true
    rw [h.const]
    exact z

theorem fresh_start {X : LinkPub} (h : Plain X.Fp) (n : ℕ) : Fresh (startFork X n) := fresh_laid h n

/-- A segment's frame's letters are read off the segment's record. -/
theorem frameAt_pub {built : Array Stages.LinkH} {W : Verify.Public} {l : ℕ}
    {x : Johnson.Desc.First.Walk.Seat.Par} (h : Johnson.Desc.First.Walk.Seat.frameAt built W l = some x) :
    ∃ X, built[l]? = some X ∧
      match x with
      | .att P _ => P.X = Johnson.Desc.First.Walk.Seat.pubOf X
      | .lay P => P.X = Johnson.Desc.First.Walk.Seat.pubOf X := by
  unfold Johnson.Desc.First.Walk.Seat.frameAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨X, hX, ?_⟩
  split at h
  · exact nomatch h
  · split at h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain rfl := Option.some.inj h
      rfl
    · split at h
      · obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
        obtain rfl := Option.some.inj h
        rfl
      · exact nomatch h

theorem zeroAt_pub {built : Array Stages.LinkH} {W : Verify.Public} {P : Johnson.Desc.First.Walk.LayPar}
    (h : Johnson.Desc.First.Walk.Seat.zeroAt built W = some P) :
    ∃ X, built[0]? = some X ∧ P.X = Johnson.Desc.First.Walk.Seat.pubOf X := by
  unfold Johnson.Desc.First.Walk.Seat.zeroAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨X, hX, ?_⟩
  split at h
  · exact nomatch h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rfl

/-- What is laid to the letter, read. -/
theorem opened_of_laid {t : S} {X : LinkPub} {ck : ChainCheck} {l n : ℕ} (hc : Closed X.Tp) (hp : Plain X.Fp)
    (h5 : t.link? = some { check := ck, link := l, arrayOf := X.arrayOf, list := X.Tp })
    (h6 : t.fork? = some (startFork X n)) {L : LinkCtx} {F : Fork} (hL : t.link? = some L)
    (hF : t.fork? = some F) : Opened L F := by
  obtain rfl := Option.some.inj (h5.symm.trans hL)
  obtain rfl := Option.some.inj (h6.symm.trans hF)
  exact ⟨rfl, hc, rfl, fresh_start hp n⟩

/-- **The head's opening.** -/
theorem headOpen_opened {HP : K2.HeadPar} (hc : Closed HP.X.Tp) {m t : S} (h : K2.headOpenQ HP m = .ok t)
    {L : LinkCtx} {F : Fork} (hL : t.link? = some L) (hF : t.fork? = some F) : Opened L F := by
  obtain ⟨a2, st, f, mine, L0, out, y, cov, s₁, b, q⟩ := (K2.headOpenQ_iff HP m t).1 h
  obtain ⟨-, ⟨b', hb', ho⟩, -⟩ := K2.headOpenOpens HP m t h
  obtain ⟨-, -, hL0, -⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L0
      F := emptySlots (weightsAtZero { trees := HP.X.Fp.trees }) HP.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have e1 : t.link? = some b'.L := by
    unfold S.link?
    rw [hb']
    simp only [ho, if_true]
  have e2 : t.fork? = some b'.F := by
    unfold S.fork?
    rw [hb']
    simp only [ho, if_true]
  obtain rfl := Option.some.inj (e1.symm.trans hL)
  obtain rfl := Option.some.inj (e2.symm.trans hF)
  rw [hb2]
  show Opened L0 (emptySlots (weightsAtZero { trees := HP.X.Fp.trees }) HP.hp.ns)
  rw [hL0]
  exact ⟨rfl, hc, rfl, fresh_laid ⟨rfl, rfl, rfl, rfl⟩ _⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The letters that the code switch's lot reads off a segment's record bear a closed list. -/
theorem letters_closed_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {HP : K2.HeadPar} (h : P1K2.pureLetters Bs.G₀ l = some HP) : Closed HP.X.Tp := by
  obtain ⟨b, hb, hc⟩ : ∃ b, Z.p.built.links[l]? = some b ∧ Closed b.Tp := by
    by_cases e : l = 24
    · subst e
      exact (built_fresh hS hR O).2
    · obtain ⟨X, h1, h2, -⟩ := (built_fresh hS hR O).1 l (by omega)
      exact ⟨X, h1, h2⟩
  obtain ⟨ls, -, -, eB, -⟩ := IM.blank_ground O.blank
  unfold P1K2.pureLetters at h
  obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [eB] at hX
  obtain ⟨b', hb', -, t⟩ := zipped_backT hX
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  show Closed X.Tp
  rw [← t]
  exact hc

/-- **What a yes of a code switch at a segment gives**, in each of its three forms. -/
theorem yesGives_opened (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {a : Place}
    (ha : a.link = some l) {nm : String} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : P1K2.YesGives Z Bs.G₀ a nm s t rs gs)
    {L : LinkCtx} {G : Fork} (hL : t.link? = some L) (hG : t.fork? = some G) : Opened L G := by
  obtain ⟨Q, n, -, -, h⟩ := h
  rcases h with ⟨hn, -⟩ | ⟨l', HP, m, rs', gs', hh, hl', hP, -, hd, ho⟩ | ⟨l', -, hb, hd⟩
  · rw [ha] at hn
    cases hn
  · obtain rfl : l = l' := Option.some.inj (ha.symm.trans hl')
    exact headOpen_opened (letters_closed_at hS hR O hl hP) ho hL hG
  · exfalso
    rw [k2_link_kept hd] at hL
    unfold S.link? at hL
    rw [hb] at hL
    cases hL

/-- **BEHIND THE SUB-PROTOCOL THAT OPENS SEGMENT l.** -/
theorem opened_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {b : Block S Cl} (hb : c.blocksInOrder[k2Number l]? = some b) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d : b.decide s rs gs = .ok t) {L : LinkCtx} {G : Fork}
    (hL : t.link? = some L) (hG : t.fork? = some G) : Opened L G := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, b₀, x, e1, e2, -, hla, hi⟩ := IM.k2_head_of hS hR O
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
    have hb' : c.blocksInOrder[14 * 24 + 1 + 2]? = some b := hb
    obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb')
    exact yesGives_opened hS hR O hl rfl (P1K2.yes_alone_gives hla (by decide) hi d).1 hL hG
  · by_cases h0 : l = 0
    · subst h0
      obtain ⟨Lk, b₀, e1, e2, L', hL', b', hb', ep, hJ⟩ :=
        IM.first_sits hS hR O 0 (by omega) KindName.K1 rfl
      have hf := IM.hear_at_flat e1 e2
      rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
      have hb₂ : c.blocksInOrder[14 * 0 + 0 + 2]? = some b := hb
      obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb₂)
      obtain ⟨X, hX, hu⟩ := HashBuild.joined_under hS hR O ⟨L', hL', hb'⟩ ep hJ
      obtain ⟨v, a1, a2⟩ := andThen_yes (hu.2 s rs gs t d)
      have a2' : Johnson.Desc.First.Walk.openLayZero X
          (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol v = .ok t := a2
      obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLayZero_ok a2'
      obtain ⟨X0, hX0, eX⟩ := zeroAt_pub hX
      obtain ⟨X1, g1, g2, g3⟩ := (built_fresh hS hR O).1 0 (by omega)
      obtain rfl : X0 = X1 := Option.some.inj (hX0.symm.trans g1)
      exact opened_of_laid (by rw [eX]; exact g2) (by rw [eX]; exact g3) h5 h6 hL hG
    · obtain ⟨Lk, b₀, x, e1, e2, -, hJ, hi⟩ := IM.k2_link_sits hS hR O l (by omega) (by omega)
      have hf := IM.hear_at_flat e1 e2
      rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
      have hb' : c.blocksInOrder[14 * l + 0 + 2]? = some b := by
        unfold k2Number at hb
        rwa [if_neg h24] at hb
      obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb')
      obtain ⟨fs, f, m, rs', gs', hfs, hf', hY, -, ho, -, -⟩ := P1K2.yes_joined_gives hJ hi d
      obtain ⟨X1, g1, g2, g3⟩ := (built_fresh hS hR O).1 l (by omega)
      rcases IM.frames_arms hfs l f hf' with ⟨X, -, -, rfl⟩ | ⟨e0, -⟩ | ⟨Q, nLin, hQ, -, eo, -⟩ |
        ⟨Q, hQ, -, eo, -⟩
      · obtain rfl : m = t := Except.ok.inj ho
        exact yesGives_opened hS hR O hl rfl hY hL hG
      · exact absurd e0 h0
      · rw [eo] at ho
        obtain ⟨_, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openAtt_ok ho
        obtain ⟨X0, hX0, eX⟩ := frameAt_pub hQ
        obtain rfl : X0 = X1 := Option.some.inj (hX0.symm.trans g1)
        have eX' : Q.X = Johnson.Desc.First.Walk.Seat.pubOf X0 := eX
        exact opened_of_laid (by rw [eX']; exact g2) (by rw [eX']; exact g3) h5 h6 hL hG
      · rw [eo] at ho
        obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLay_ok ho
        obtain ⟨X0, hX0, eX⟩ := frameAt_pub hQ
        obtain rfl : X0 = X1 := Option.some.inj (hX0.symm.trans g1)
        have eX' : Q.X = Johnson.Desc.First.Walk.Seat.pubOf X0 := eX
        exact opened_of_laid (by rw [eX']; exact g2) (by rw [eX']; exact g3) h5 h6 hL hG

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.empty_of_cr
#print axioms ProofFile.Honest.K9.fresh_of_cr
#print axioms ProofFile.Honest.K9.fresh_laid
#print axioms ProofFile.Honest.K9.fresh_start
#print axioms ProofFile.Honest.K9.frameAt_pub
#print axioms ProofFile.Honest.K9.zeroAt_pub
#print axioms ProofFile.Honest.K9.opened_of_laid
#print axioms ProofFile.Honest.K9.headOpen_opened
#print axioms ProofFile.Honest.K9.letters_closed_at
#print axioms ProofFile.Honest.K9.yesGives_opened
#print axioms ProofFile.Honest.K9.opened_at
