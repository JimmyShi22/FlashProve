-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Law/PromiseAtStep.lean: CONDITIONAL: BEHIND A YES OF THE MEMBER THAT HOLDS
THE PROXIMITY TEST AT THE FIRST CHAIN's FINISH (kind K12) THE TABLE OF JOINTS' PROMISE HOLDS AT THE
NEXT BORDER: at a member's step, and at every meaning at which "decodes" and the pair "shown", "no
collision" ride. On the verifier's own text; no prover in it. IT IMPORTS A FILE OF THE LIBRARY
ALONE. Statements with their proofs; no definition.

Why. The library has that tie (`H2K12.t2_at`, Johnson/Loose/H2K12/Hands354.lean) at a piece of the
IOP as written, whose accept is the piece's own way out, and under two equations: the meaning's
"shown" and "no collision" are the library's notions. A thread of an honest run has a member's step,
and letters at which these two sentences are "True" by their text: there the two equations are not
had. Here the accept is a member's step, and the two sentences are asked only to ride.

How. Nothing new is shown of the protocol. `index_stays` follows the proof of `H2K12.across_of_sits`
(Johnson/Loose/H2K12/AcrossOfSits.lean) from the member's step on, for the two of that lemma's facts
that are spent here. `promise_behind` follows the proof of `t2_at`, clause by clause: the four tests
on the state and the plan's numbers by `k12_grownAt` (Johnson/Desc/K12/Coin/K12Grows.lean) with
`goOn_of_B` (GoOnTest.lean); "held" by `H2K12.held_stays`; the two public items tied to the index
masks' pin by `index_stays`; "in order", "decodes" and the pair by premises; behind the member no
public item is open.

Main names:
  `index_stays`   past the member's yes the number of the index masks' message stays, and that
      message keeps its shape
  `promise_behind`   **the promise at border k + 1 from the promise at border k and the member's
      step**

Premises of `promise_behind`. hS, hl: the member sits over the test, and its way out lays the
statement, the book and the count of roots alone. he, ha, hp, ho: four tests on the test's own
numbers. hpinI, hk, hk', hp', hOb, hQb: lines on the table's lists; hOb: behind the member just four
items are open; hQb: and no public item. hII, hIT, hheld, hin: on the meaning's letters. hL, hB: on
the plan's numbers. hpub, h1: the public part rides; the member's step. hon, hm0: the promise in
front; no mark. F, hcod: four facts on the state in front, of which two are spent, and its codes.
hDec, hSN: "decodes" rides; the pair rides at the index masks' seat. What falls against `t2_at`: the
piece; the two equations; the premises on the reader of samples, on the first tree's number and on
the piece's base.

Limits. A JOINING OVER LETTERS: it pays no law of the kind. Whether all premises can be met together
is not proved here; under the library's hypothesis on the public input
Johnson/Desc/ProofFile/Honest/K12/Law/FormBehind.lean pays them, at the member number 354, FROM TWO
PREMISES OF ITS OWN, THE THREAD IN FRONT AND THE STEP: out of the thread it takes the promise in
front, no mark (hm0) and that the state in front is reached, by which it pays F and hcod; those on
the meaning's letters (hII, hIT, hheld, hin, hDec, hSN) it pays at the honest letters alone. Through
its import the file stands above Cb/Bridge/CodeListRSProved.lean, and so above the files under
ThirdParty/ (a limit that Johnson/Loose/H2K12/K12AtHead.lean states of itself).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Loose.H2K12.Hands354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12.AtStep

open VerifiableInference.Desc (Place Block OpenedColumn)
open VerifiableInference.Desc.Sound (strsOf)
open VerifiableInference.Desc.First (ModelPart Item Numbers)

section
variable {P W Cl : Type} {Fr : VerifiableInference.Desc.Sound.Frame}
  (π : VerifiableInference.Desc.K12.P12) (d : VerifiableInference.Desc.First.FoldData)
  (N : Numbers) (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart)
  (ps : List Place)

/-- **Past a yes of the proximity test's member the number of the index masks' message stays, and
that message keeps its shape.** After `H2K12.across_of_sits`, from the member's step on.
CONDITIONAL: the seat (hS, hl); he, ha; hpinI; hII, hIT, hheld; hL; the step h1; the promise in
front hon; no mark hm; the facts F. -/
theorem index_stays (k : ℕ) (B : Block VerifiableInference.Desc.First.S Cl)
    (leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.K12.T12 →
      Except String VerifiableInference.Desc.First.S)
    (hS : H2K.JointK.Sits B (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      π : Block VerifiableInference.Desc.K12.T12 Unit) VerifiableInference.Desc.K12.enterFinish
      leave)
    (hl : VerifiableInference.Desc.K12.Coin.LaysOnly leave) (he : π.early = true)
    (ha : π.answers = 1)
    (hpinI : Item.pinI ∈ VerifiableInference.Desc.K13.Law.openAt links ps k)
    (hII : ∀ x, Mg.pub .indexIs x = VerifiableInference.Desc.K13.indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = VerifiableInference.Desc.K13.indexThereC x.2)
    (hheld : Mg.held = fun j t x => VerifiableInference.Desc.smpHeld x.2.st x.2.book j t)
    (hL : d.L.places[N.indexNo]? = some N.index)
    (a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str) (s' : VerifiableInference.Desc.First.S)
    {ft n : ℕ} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (h1 : B.step ft a.1.2 rs cols = .ok (s', n))
    (hon : VerifiableInference.Desc.Sound.onQ N Mg links ps
      (fun x : P × VerifiableInference.Desc.First.S => x) k a)
    (hm : a.1.2.failed = none) (F : FactsF d a.1.2) :
    s'.out.indexMasks = a.1.2.out.indexMasks ∧
      (s'.st.oracles[a.1.2.out.indexMasks]?).map (·.shape) =
        (a.1.2.st.oracles[a.1.2.out.indexMasks]?).map (·.shape) := by
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft _ _ _ _ n h1
  obtain ⟨gs, hd⟩ := VerifiableInference.Desc.K12.Coin.step_decide _ ft t t' _ _ n e2
  have eb := hl _ _ _ e3
  obtain ⟨o, _, _, _, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok a.1.2 t e1
  -- where the index masks' message sits, by the promise
  obtain ⟨hii, hit, hbk, _⟩ := VerifiableInference.Desc.K13.Law.promise_index N Mg links ps
    (fun x : P × VerifiableInference.Desc.First.S => x) k hpinI a hon hm
  have hI : VerifiableInference.Desc.K1.indexIsB N.indexNo a.1.2 = true := by
    rw [← VerifiableInference.Desc.K13.Law.indexIsC_eq, ← hII]
    exact hii
  have hT : VerifiableInference.Desc.K1.indexThereB a.1.2 = true := by
    rw [← VerifiableInference.Desc.K13.Law.indexThereC_eq, ← hIT]
    exact hit
  have hbk' := hbk
  unfold VerifiableInference.Desc.First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have hseat : a.1.2.book.place[a.1.2.out.indexMasks]? = some N.index :=
    eq_of_beq (VerifiableInference.Desc.K1.indexSeat_of_carried
      ((VerifiableInference.Desc.K12.Coin.seatsPrefix_iff
        (VerifiableInference.Desc.K12.Door.toTree d.L) _).1 F.seats) hbk'.1.2 hT hI hL)
  have hthere : a.1.2.out.indexMasks < a.1.2.st.oracles.size := by
    have e : (a.1.2.st.oracles[a.1.2.out.indexMasks]?).isSome = true := hT
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 e
    exact (Array.getElem?_eq_some_iff.1 hx).1
  have hBF := (VerifiableInference.Desc.Sound.bookFitsB_iff a.1.2.book).1 F.fits
  -- the index masks' message is not the message that holds the first fold's mask
  have hmk : o.mask ≠ some a.1.2.out.indexMasks := by
    intro hmask
    have hSH : VerifiableInference.Desc.First.samplesHeld N Mg
        (VerifiableInference.Desc.K13.Law.openAt links ps k) a.1 = true :=
      ((hon.2.resolve_left fun h => h hm).2).1
    have h2 := List.all_eq_true.1 hSH N.index (List.mem_flatMap.2 ⟨.pinI, hpinI, by simp⟩)
    rw [hheld] at h2
    obtain ⟨x, hx, hs⟩ := sampled_of_held hBF h2 hseat
    exact sampled_no_mask
      (VerifiableInference.Desc.K12.Seat.block_front_holds π _ t' _ gs hd).2.1 hx hs hmask
  have hsp : (s'.st.oracles[a.1.2.out.indexMasks]?).map
      VerifiableInference.Desc.K12.Coin.smpPart =
      (a.1.2.st.oracles[a.1.2.out.indexMasks]?).map VerifiableInference.Desc.K12.Coin.smpPart := by
    rw [eb]
    exact VerifiableInference.Desc.K12.Coin.k12_smp π he ha _ t' _ gs hd _ hthere hmk
  refine ⟨by rw [eb], ?_⟩
  have := congrArg (Option.map fun x : OnBytes.OracleShape × Bool × Array OnBytes.Row => x.1) hsp
  rwa [Option.map_map, Option.map_map] at this

/-- **BEHIND A YES OF THE PROXIMITY TEST's MEMBER THE TABLE's PROMISE HOLDS AT THE NEXT BORDER, AT
EVERY MEANING AT WHICH "decodes" AND THE PAIR "shown", "no collision" RIDE.** After `H2K12.t2_at`,
at the member's step. CONDITIONAL: every binder from hS to hSN; the head of this file says what each
is. -/
theorem promise_behind (k : ℕ) (B : Block VerifiableInference.Desc.First.S Cl)
    (leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.K12.T12 →
      Except String VerifiableInference.Desc.First.S)
    (hS : H2K.JointK.Sits B (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      π : Block VerifiableInference.Desc.K12.T12 Unit) VerifiableInference.Desc.K12.enterFinish
      leave)
    (hl : VerifiableInference.Desc.K12.Coin.LaysOnly leave) (he : π.early = true)
    (ha : π.answers = 1)
    (hpinI : Item.pinI ∈ VerifiableInference.Desc.K13.Law.openAt links ps k)
    (hII : ∀ x, Mg.pub .indexIs x = VerifiableInference.Desc.K13.indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = VerifiableInference.Desc.K13.indexThereC x.2)
    (hheld : Mg.held = fun j t x => VerifiableInference.Desc.smpHeld x.2.st x.2.book j t)
    (hL : d.L.places[N.indexNo]? = some N.index)
    (hp : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts π :
      Block VerifiableInference.Desc.K12.T12 Unit).planOk = true)
    (ho : π.nums.ownMask = false) (p p' : Place) (hk : ps[k]? = some p)
    (hk' : ps[k + 1]? = some p')
    (hp' : VerifiableInference.Desc.First.standAt links p' = .fin)
    (hOb : (VerifiableInference.Desc.First.openSets links ps
      (VerifiableInference.Desc.First.start links))[k + 1]?.getD [] =
      [.unmarked, .pinW, .pile, .pinI])
    (hQb : (VerifiableInference.Desc.First.pubSets Mg.more links ps)[k + 1]?.getD [] = [])
    (hB : VerifiableInference.Desc.K12.Coin.goOnB N p p' π
      (VerifiableInference.Desc.K12.Door.toTree d.L) d.sent.codes = true)
    (hin : ∀ x y : P × VerifiableInference.Desc.First.S, y.1 = x.1 → Mg.inOrder x = true →
      Mg.inOrder y = true)
    (a b : (P × VerifiableInference.Desc.First.S) × Fr.E.Str) (hpub : b.1.1 = a.1.1)
    {ft n : ℕ} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (h1 : B.step ft a.1.2 rs cols = .ok (b.1.2, n))
    (hon : VerifiableInference.Desc.Sound.onQ N Mg links ps
      (fun x : P × VerifiableInference.Desc.First.S => x) k a)
    (hm0 : a.1.2.failed = none) (F : FactsF d a.1.2) (hcod : a.1.2.st.codes = d.sent.codes)
    (hDec : Mg.decodes a.1 (strsOf Fr a.2) → Mg.decodes b.1 (strsOf Fr b.2))
    (hSN : Mg.shown N.index.1 N.index.2 (strsOf Fr a.2) ∧
        Mg.noColl N.index.1 N.index.2 a.1 (strsOf Fr a.2) →
      Mg.shown N.index.1 N.index.2 (strsOf Fr b.2) ∧
        Mg.noColl N.index.1 N.index.2 b.1 (strsOf Fr b.2)) :
    VerifiableInference.Desc.Sound.onQ N Mg links ps
      (fun x : P × VerifiableInference.Desc.First.S => x) (k + 1) b := by
  obtain ⟨Aidx, Ashape⟩ := index_stays π d N Mg links ps k B leave hS hl he ha hpinI hII hIT hheld
    hL a b.1.2 h1 hon hm0 F
  -- the promise in front, clause by clause
  obtain ⟨hii, hit, hbk, _⟩ := VerifiableInference.Desc.K13.Law.promise_index N Mg links ps
    (fun x : P × VerifiableInference.Desc.First.S => x) k hpinI a hon hm0
  obtain ⟨hd, hrest⟩ := hon
  obtain ⟨hB6, hsam, hsn, _⟩ := hrest.resolve_left (fun h => h hm0)
  simp only [Bool.and_eq_true] at hB6
  have hIdx : N.index ∈ VerifiableInference.Desc.First.sampledIn N
      ((VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD []) :=
    List.mem_flatMap.2 ⟨.pinI, hpinI, by simp⟩
  have hheldA :
      VerifiableInference.Desc.smpHeld a.1.2.st a.1.2.book N.index.1 N.index.2 = true := by
    have := List.all_eq_true.1 hsam N.index hIdx
    rwa [hheld] at this
  -- the four tests on the state and the plan's numbers
  rw [hk] at hbk
  obtain ⟨_, g2, g3, g4, g5, _, _⟩ := VerifiableInference.Desc.K12.Coin.k12_grownAt links N p p'
    [.unmarked, .pinW, .pile, .pinI] π hp ho he ha hp' rfl B leave hS hl d.L ft a.1.2 b.1.2 _ _ n
    (VerifiableInference.Desc.K12.Coin.goOn_of_B hB a.1.2 hcod hbk) h1
  have hPl : VerifiableInference.Desc.Sound.PlacesInBook a.1.2.book := fun i x hx => by
    obtain ⟨T, hT, -⟩ := (VerifiableInference.Desc.Sound.bookFitsB_iff a.1.2.book).1 F.fits i x hx
    exact (Array.getElem?_eq_some_iff.1 hT).1
  show VerifiableInference.Desc.First.onAt N Mg links ps[k + 1]? _ _ b.1 (strsOf Fr b.2)
  rw [hk', hOb, hQb]
  refine ⟨hDec hd, Or.inr ⟨?_, ?_, ?_, fun x hx => absurd hx (List.not_mem_nil)⟩⟩
  · simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨g2, g3⟩, g4⟩, hin a.1 b.1 hpub hB6.1.1.2⟩, ?_⟩, g5 hbk⟩
    have e1 : Mg.pub .indexIs b.1 = true := by
      rw [hII] at hii ⊢
      unfold VerifiableInference.Desc.K13.indexIsC at hii ⊢
      rw [Aidx]
      exact hii
    have e2 : Mg.pub .indexThere b.1 = true := by
      rw [hIT] at hit ⊢
      unfold VerifiableInference.Desc.K13.indexThereC at hit ⊢
      rw [Aidx]
      have e := congrArg Option.isSome Ashape
      rw [Option.isSome_map, Option.isSome_map] at e
      rw [e]
      exact hit
    simp [VerifiableInference.Desc.First.pubHeld, VerifiableInference.Desc.First.pubOfItems, e1, e2]
  · have e3 : Mg.held N.index.1 N.index.2 b.1 = true := by
      rw [hheld]
      exact held_stays π he ha B leave hS hl ft a.1.2 b.1.2 _ _ n h1 hPl _ _ hheldA
    simp [VerifiableInference.Desc.First.samplesHeld, VerifiableInference.Desc.First.sampledIn, e3]
  · intro x hx
    obtain rfl : x = N.index := by
      simpa [VerifiableInference.Desc.First.sampledIn] using hx
    exact hSN (hsn N.index hIdx)

end

end H2K12.AtStep

#print axioms H2K12.AtStep.index_stays
#print axioms H2K12.AtStep.promise_behind
