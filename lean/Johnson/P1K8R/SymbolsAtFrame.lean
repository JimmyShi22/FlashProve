-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SymbolsAtFrame.lean: THE SMALLNESS TEST's SECOND FALL IN THE HONEST SIDE's FRAME: THE
FIRST OF THE FOUR TESTS OF `ShareLive` (Johnson/P1K8R/ShareLiveOf.lean: every column of the drawn
matrix is live) HOLDS AT THE STATES THAT THE FRAME's FIELD hP' HANDS, WHERE THE MARKS IN FRONT HAVE
BEEN SILENT: THE TIE BETWEEN THE STATE AND THE CHALLENGES IS THE WALK. Lemmas; NONE OF THE LIBRARY's
GOALS. A joining. Nothing on completeness, soundness or hiding.

  **`fold_at_walk`**   general: the state beside a walk is the verifier's own fold's, at the
      walk's rounds, which show the challenges heard: `fold_of_tied`
      (Johnson/P1K8R/CountsAtWalk.lean), front_stand
      (Johnson/Desc/ProofFile/Honest/Law/CoverPay.lean), start_tied, walk_tied (WalkFold.lean),
      walk_shows (CoverLocal.lean)
  `quiet_at_member`   general: the silence at one member of a list: marksQuiet_append
      (CoverJoin.lean)
  `typed_of_fit`   a challenge that the draw's round can draw shows a typed matrix's list:
      listOf_onto (Johnson/Desc/K8/Honest/WindowLawProofs.lean)
  **`symbols_at_handed`**   mark_silent (CoverFit.lean), `state_of_fold`
      (Johnson/P1K8R/LiveOfFold.lean), `draw_there` (DeadMark.lean), P1K8S.sitsAt_open
Kin of `fold_at_walk`, all the frame's authors': ver_reach_all (CoverBelow.lean): at every border up
to the last sub-protocol asked the fold at the walk's rounds and columns returns SOME reached state;
it does not say that at the last it is the walk's own, nor what the rounds show; walk_fold
(WalkFold.lean) and chain_end (RunC.lean) say it once the chain has run through; `ChainProgress.Tied`
(WalkFold.lean) has it border by border: for some list of the members asked so far and some list of
the rounds laid for them, the walk's state equals the fold over these; the proof of ver_reach_below
(CoverBelow.lean) has it inside.
Limits. ONE OF FOUR TESTS. That the walk returns, that its start obeys the frame's law (no field of
`FirstAsks` hands that: its letter for where the walk starts is free; at the frame's authors' own
choice their letter_starts and letter_tree, Johnson/Desc/ProofFile/Honest/Law/CoverLetter.lean, say
it), that the two marks are among those asked and that they have been silent are premises: the
chance that they speak is the marks' own stated numbers' matter, not this file's. It is not laid
into a member of `FirstAsks` here. Nothing says that any state is reached.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.DebtsK8
import Johnson.P1K8R.CountsAtWalk
import Johnson.Desc.K8.Honest.WindowLawProofs
import Johnson.Desc.ProofFile.Honest.Law.CoverBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest (Lay ChainProgress Mid Step walk roundsOf Mark markOf marksQuiet marksQuiet_append
  mark_silent front_stand start_tied walk_tied walk_shows walk_len drawFit drawsFit)
open ProofFile.Honest.K8 (rnds)

section
variable {T Cl W Y : Type}

/-- **THE VERIFIER's STATE BESIDE A WALK THAT STANDS IN FRONT OF A SUB-PROTOCOL WITH A ROUND IS WHAT
THE VERIFIER's OWN FOLD RETURNS OVER THE SUB-PROTOCOLS IN FRONT, AT THE WALK's OWN ROUNDS AND
COLUMNS; AND THESE ROUNDS SHOW THE CHALLENGES HEARD.** The first half is `fold_of_tied`
(Johnson/P1K8R/CountsAtWalk.lean) with its premises had from the walk's start and its return; the
second half is new here. -/
theorem fold_at_walk (L : Lay) (pre t : List (Block T Cl)) (b : Block T Cl)
    {a z : ChainProgress T Cl W Y} {s₀ s' : T} {m₀ : Option (Mid W Y)} {ss : List (Step W Y)}
    {dA : List Fmt.Drawn} (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L (pre ++ b :: t) m₀ (some s₀) front = .ok a) (hpos : 0 < b.rounds.length)
    (hz : walk L ss dA a = .ok z) (hl : ss.length = (pre.flatMap (·.rounds)).length)
    (hv : z.ver = some s') :
    ∃ (r : List Fmt.RoundView) (c : List Desc.OpenedColumn),
      foldBlocks L.firstTree pre s₀ (roundsOf z.laid) z.cols = .ok (s', r, c) ∧
      (roundsOf z.laid).map (·.drawn) = dA := by
  obtain ⟨e1, e2⟩ := front_stand L (pre ++ b :: t) pre t b hm ha rfl hpos hz hl
  obtain ⟨t0, o0, l0⟩ := start_tied L (pre ++ b :: t) m₀ (some s₀) ha
  rw [if_pos hm] at t0
  obtain ⟨t1, -, -⟩ := walk_tied L (pre ++ b :: t) (some s₀) ss dA a z t0 o0 hz
  have hdr : (roundsOf z.laid).map (·.drawn) = dA := by
    have w := walk_shows L ss dA a z hz
    rw [l0, List.map_nil, List.nil_append] at w
    rw [← w]
    unfold roundsOf
    rw [List.map_map]
    rfl
  obtain ⟨r, c, hf⟩ := fold_of_tied L (pre ++ b :: t) s₀ s' z pre.length t1
    (by rw [e1]; exact (List.drop_left' rfl).symm) e2 hv
  rw [List.take_left' rfl] at hf
  exact ⟨r, c, hf, hdr⟩

/-- **Where no mark at a member of a list has spoken, none has at this member**: at the challenges
in front of it and at its own. -/
theorem quiet_at_member (ms : List Mark) (A₁ A₂ : List (Block T Cl)) (d : Block T Cl)
    (f r : List Fmt.Drawn) (h : marksQuiet ms (A₁ ++ d :: A₂) f r = true) :
    (markOf ms d.place (f ++ r.take (A₁.flatMap (·.rounds)).length)
      ((r.drop (A₁.flatMap (·.rounds)).length).take d.rounds.length)).isNone = true := by
  rw [marksQuiet_append, Bool.and_eq_true] at h
  have h2 : ((markOf ms d.place (f ++ r.take (A₁.flatMap (·.rounds)).length)
      ((r.drop (A₁.flatMap (·.rounds)).length).take d.rounds.length)).isNone &&
    marksQuiet ms A₂ (f ++ r.take (A₁.flatMap (·.rounds)).length ++
        (r.drop (A₁.flatMap (·.rounds)).length).take d.rounds.length)
      ((r.drop (A₁.flatMap (·.rounds)).length).drop d.rounds.length)) = true := h.2
  rw [Bool.and_eq_true] at h2
  exact h2.1

end

/-- A challenge that the draw's round can draw shows a typed matrix's list. -/
theorem typed_of_fit {p : K8.Par} {sz : Size} (hF : K8.Fits p sz) {dr : Fmt.Drawn}
    (h : drawFit (K8.round p) dr = true) : ∃ β : Dr sz, dr.trits.toArray = listOf β := by
  unfold drawFit at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, h5⟩, -⟩, -⟩, -⟩ := h
  refine listOf_onto sz dr.trits ?_ fun t ht => ?_
  · rw [h3, K8.columns_eq hF, hF.tau]
    rfl
  · rcases h5 t ht with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W Y : Type}

/-- **THE FIRST OF `ShareLive`'s FOUR TESTS AT THE STATES THAT THE FRAME's FIELD hP' HANDS, FROM THE
MARKS' SILENCE.** ms: the marks asked; among them the mark "a column of the drawn matrix is all 0"
at this segment (hdead) and the fit's marks at A's members (hfit). A: the sub-protocols in front of
the batching b. L: the walk's lay, at first tree 0 (hft); a: where the walk starts, under the
frame's own law on its start (hm, ha). Where the marks at A's members have been silent at the
challenges fr (hq), the walk over A's rounds returns z (hz) and z's verifier's state is s': every
column of the matrix that s' holds is live. -/
theorem symbols_at_handed (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {X : LinkH} (hX : Bs.G₀.built[l]? = some X) (ms : List Mark) {sz : Size}
    (hsz : K8.Fits (ProofFile.k8ParW Z Bs.G₀ X l).toPar sz)
    (hdead : deadMark l (if l = 24 then 1 else 0) sz ∈ ms)
    {A t : List (Block S Claim)} {b : Block S Claim} (hall : c.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * l + (if l = 24 then 11 else 9)) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress S Claim W Y} {s₀ s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn} {front : List Desc.OpenedColumn}
    (hm : m₀.isSome = true) (ha : ChainProgress.start L c.blocksInOrder m₀ (some s₀) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ tl, s'.tl? = some tl ∧ symbolsLive tl = true := by
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨-, b8, Xl, -, -, hf8, hXl, hL, -⟩ := P1K8S.sitsAt_open hS hR O _ hp
  obtain rfl : Xl = X := Option.some.inj (hXl.symm.trans hX)
  have hr8 : b8.rounds = [K8.round (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar] := by
    rw [IM.alone_rounds hL]
    rfl
  have hlt : 14 * l + (if l = 24 then 5 else 4) + 2 < A.length := by
    rw [hA]
    split_ifs <;> omega
  -- the draw's member stands in A
  have hA8 : A[14 * l + (if l = 24 then 5 else 4) + 2]? = some b8 := by
    rw [hall, List.getElem?_append_left hlt] at hf8
    exact hf8
  obtain ⟨hi, e8⟩ := List.getElem?_eq_some_iff.1 hA8
  have hsp : A = A.take (14 * l + (if l = 24 then 5 else 4) + 2) ++
      b8 :: A.drop (14 * l + (if l = 24 then 5 else 4) + 2 + 1) := by
    rw [← e8, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have htk : A.take (14 * l + (if l = 24 then 5 else 4) + 2) =
      c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2) := by
    rw [hall, List.take_append_of_le_length (Nat.le_of_lt hlt)]
  have hAk : c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)) = A := by
    rw [hall, ← hA]
    exact List.take_left' rfl
  -- the silence at that member
  have hq' := hq
  rw [hsp] at hq'
  have hs := quiet_at_member ms _ _ b8 [] fr hq'
  rw [htk, hr8, List.nil_append] at hs
  -- its own challenge
  have hnn : rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2)) < fr.length := by
    rw [hn]
    conv_rhs => rw [hsp]
    rw [List.flatMap_append, List.length_append, List.flatMap_cons, List.length_append, htk, hr8]
    show rnds _ < rnds _ + (1 + _)
    omega
  obtain ⟨dr, hdr⟩ : ∃ dr, fr[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? =
      some dr := ⟨_, List.getElem?_eq_getElem hnn⟩
  have hown : (fr.drop (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2)))).take
      [K8.round (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar].length = [dr] := by
    obtain ⟨hi', e'⟩ := List.getElem?_eq_some_iff.1 hdr
    rw [List.drop_eq_getElem_cons hi', e']
    rfl
  have hs' : (markOf ms b8.place
      (fr.take (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2)))) [dr]).isSome =
      false := by
    have h0 : (markOf ms b8.place
      (fr.take (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2)))) [dr]).isNone =
      true := by
      rw [← hown]
      exact hs
    cases hc : markOf ms b8.place
      (fr.take (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2)))) [dr] with
    | none => rfl
    | some _ =>
      rw [hc] at h0
      cases h0
  have hpl : b8.place = drawPlace l (if l = 24 then 1 else 0) := by
    have h := draw_there hS hR O hl
    rw [hf8] at h
    exact Option.some.inj h
  -- the mark "a column is all 0" is silent
  have hd0 : deadT sz [dr] = false := by
    have h := mark_silent hdead (fr := fr.take
      (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2)))) (own := [dr])
      (by rw [show (deadMark l (if l = 24 then 1 else 0) sz).place = b8.place from hpl.symm]
          exact hs')
    have h' : (if deadT sz [dr] = true then
      some "the smallness test: a column of the drawn matrix is all 0" else none) = none := h
    by_cases hb : deadT sz [dr] = true
    · rw [if_pos hb] at h'
      cases h'
    · exact Bool.eq_false_iff.2 hb
  -- the fit's mark is silent
  have hf0 : drawFit (K8.round (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar) dr = true := by
    have h := mark_silent (hfit b8 (List.mem_of_getElem? hA8)) (fr := fr.take
      (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2)))) (own := [dr]) hs'
    have h' : (if drawsFit b8.rounds [dr] = true then none
      else some "its rounds cannot draw these") = none := h
    by_cases hb : drawsFit b8.rounds [dr] = true
    · rw [hr8] at hb
      have hb' : (drawFit (K8.round (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar) dr &&
        drawsFit [] []) = true := hb
      exact (Bool.and_eq_true _ _ ▸ hb').1
    · rw [if_neg hb] at h'
      cases h'
  -- the fold at the walk's own rounds
  have hl' : ss.length = (A.flatMap (·.rounds)).length := by
    rw [← walk_len L ss fr a z hz]
    exact hn
  rw [hall] at ha
  obtain ⟨r, c', hfold, hshow⟩ := fold_at_walk L A t b hm ha hpos hz hl' hv
  rw [hft, ← hAk] at hfold
  obtain ⟨r₀, hr₀, hr₀d⟩ : ∃ r₀, (roundsOf z.laid)[rnds
      (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? = some r₀ ∧ r₀.drawn = dr := by
    rw [← hshow, List.getElem?_map] at hdr
    obtain ⟨r₀, h1, h2⟩ := Option.map_eq_some_iff.1 hdr
    exact ⟨r₀, h1, h2⟩
  obtain ⟨Xl', hXl', H⟩ := state_of_fold hS hR O hl
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  obtain ⟨tl, h1, h2, -, -⟩ := H s₀ s' _ r _ c' sz r₀ hfold hsz hr₀
    (by rw [hr₀d]; exact typed_of_fit hsz hf0) (by rw [hr₀d]; exact hd0)
  exact ⟨tl, h1, h2⟩

end

end P1K8

#print axioms P1K8.fold_at_walk
#print axioms P1K8.quiet_at_member
#print axioms P1K8.typed_of_fit
#print axioms P1K8.symbols_at_handed
