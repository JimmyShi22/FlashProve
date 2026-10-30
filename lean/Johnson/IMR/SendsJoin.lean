-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsJoin.lean: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre»
(Johnson/Desc/Sound/SmpPlaces.lean): THE JOIN: IN THE GOALS' SCOPE, AT THE PROOF FILE's FIRST CHAIN:
THE DEBT SendsOn (Johnson/IMR/SendsFold.lean: ASKED AT THE STATES THAT THE FOLD FROM s₀ REACHES IN
FRONT OF THE SUB-PROTOCOL, AND AT NO OTHER) AT ALL 358 SUB-PROTOCOLS FROM THE ARMS
(Johnson/IMR/SendsArms.lean: 229 numbers) AND FIVE DEBTS THAT STAY, EACH IN ITS
OWN CONSTANTS; AND THE TOP.
WHY «AT REACHED STATES»: K2's code switch sends what the state's frame says; the batching runs the link's gathered runs: at a state that no fold reaches their laws need not hold: a debt bound over every state could not be paid. At a reached state every theorem along the fold may be spent (ReachedAt unfolds to a fold's accepting; reached_accepts: whatever stands in front has accepted somewhere).
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
LETTERS. codes · ft · sn j (what the sub-protocol number j sends) as in Johnson/IMR/SendsFold.lean;
Z · Bs · c as in Johnson/IMR/SeatOpen.lean's Open.

  senderKind k      k is K1, K2 or K12. sender_count: 78 of the 358 places of the written list are of these kinds (by the kernel): K1 52 · K2 25 · K12 1.
  kindsFit · kinds_fit · kind_at_*   THE CLOSED FACTS: which kind stands at the frames', the batching's and the closing's numbers, at 0, 355 and 357: by the kernel.
  SendDebts ft codes sn Z G₀ c s₀   WHAT STAYS (each but «calm» a SendsOn at ReachedAt ft c.blocksInOrder s₀ ‹its number›):
    calm      sn k = [] wherever the written list's place number k is of no sender's kind. (A sentence on the letter sn.)
    first     (25) the lot's OWN sub-protocol at (1, some l, 1, k): K1's first sending (l = 0) · K2's switch (1 … 23) · K7's (24). «opened» behind it is paid (sends_first).
    hear      (51) the lot's own sub-protocol at (1, some l, i + 1, k), 1 ≤ i, k a sender's kind: K1's later sendings (50) · K2 at the head's second place (1).
    batch     (25) the chain's own link's batching at the link's own gatherer: sends nothing.
    behind    (25) the sub-protocol behind it: the like.
    back      (3) the lot's own sub-protocol at (1, none, j + 1, k), k a sender's kind: K2's finish (353) · the proximity test (354) · W's commitment (356).
  SendsOn.under · sends_first_on   the two rules for a payer, at the states of G.
  sends_scope       in scope: SendDebts ⟹ at every j: SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ j) (sn j) c.blocksInOrder[j].
  seats_scope       THE TOP: besides: the first state has the code table, an empty book, is in step · the plan's lists L are what all 358 send ⟹ behind the first k sub-protocols: SeatsPrefix L · in step · the code table · the two counts.

  start_three · seats_start   THE s₀ AT WHICH THE DEBTS ARE MEANT: THE PROOF FILE's OWN FIRST STATE ProofFile.startS Z p, p the public instance, codes := Z.first.codes: where it bears no mark it has that code table, an empty book, and is in step (every o; no scope): so the top's three premises on s₀ are paid there.

229 + 25 + 51 + 25 + 25 + 3 = 358.
What is not claimed. The five debts. WHERE A FAULT WOULD SIT: batch | behind at []: they hold only if no run of claims and no run behind the batching of a hearing sub-protocol writes the book, the number of oracle messages or the code table (K1's and K2's makers have no such run: held through Lean by rfl at K1.firstSegmentOpening · K1.laterAt · K2.codeSwitchKind; the seated forms: Johnson/IMR/LinkRest.lean's hear_runs) · K12 at 354: k12_appends (Johnson/Desc/K12/Coin/BookAppends.lean) has the arm «the mask has come from outside» alone. The plan's side (that the closed constant's L (P5J.At.laid?, Johnson/P5J/LettersAt2.lean) is that list's layout: laid_of_lists (Johnson/Desc/K12/Door/LaidOfLists.lean) brings it down to one equation of lists, SendsAre; «the order of the entries is the fold's order» lies in it). No soundness.
-/
import Johnson.IMR.SendsArms
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S kindsBeforeBatching closeKinds backKinds)
open VerifiableInference.Desc.K12.Coin (laidOf SeatsPrefix)
open ProofFile (Cl)

/-- The kinds that send. -/
def senderKind (k : KindName) : Bool := k == .K1 || k == .K2 || k == .K12

set_option maxRecDepth 1000000 in
theorem sender_count : (placesW.countP fun p => senderKind p.kind) = 78 ∧
    (placesW.countP fun p => p.kind == .K1) = 52 ∧ (placesW.countP fun p => p.kind == .K2) = 25 ∧
    (placesW.countP fun p => p.kind == .K12) = 1 := by decide +kernel

/-- The kind at a number of the written list. -/
def kindW (k : ℕ) : Option KindName := (placesW[k]?).map (·.kind)

/-- Which kind stands at the frames', the batching's and the closing's numbers. -/
def kindsFit : Bool :=
  kindW 0 == some .frame && kindW 355 == some .K13 && kindW 357 == some .frame &&
    (List.range 25).all fun l =>
      kindW (14 * l + 1) == some .frame && kindW (14 * l + nAt l + 2) == some .K9 &&
        kindW (14 * l + nAt l + 3) == some .frame && kindW (14 * l + nAt l + 4 + 0) == some .K9 &&
        kindW (14 * l + nAt l + 4 + 1) == some .K10 && kindW (14 * l + nAt l + 4 + 2) == some .K9 &&
        kindW (14 * l + nAt l + 7) == some .frame

set_option maxRecDepth 1000000 in
theorem kinds_fit : kindsFit = true := by decide +kernel

/-- **WHAT STAYS.** -/
structure SendDebts (ft : ℕ) (codes : Codes) (sn : ℕ → List (Array OracleNotice)) (Z : ProofFile.Pub)
    (G₀ : ProofFile.Ground) (c : Chain S Cl) (s₀ : S) : Prop where
  calm : ∀ k kd, kindW k = some kd → senderKind kd = false → sn k = []
  first : ∀ l < 25, ∀ (k : KindName) (b' : Block S Cl),
    (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k → (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := some l, piece := 1, kind := k } →
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + 2)) (sn (14 * l + 2)) b'
  hear : ∀ l < 25, ∀ (i : ℕ) (k : KindName) (b' : Block S Cl), 1 ≤ i →
    (kindsBeforeBatching (subAt l) (l == 0))[i]? = some k → senderKind k = true →
    (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } →
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + i + 2)) (sn (14 * l + i + 2)) b'
  batch : ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk →
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + nAt l + 2)) []
      (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order))
  behind : ∀ l < 25, ∀ (Lk : Link S Cl) (b : Block S Cl), c.links[l]? = some Lk → b.rounds = [] →
    (∀ s rs gs, b.decide s rs gs = Lk.runBehind s) →
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + nAt l + 3)) [] b
  back : ∀ (j : ℕ) (k : KindName) (b' : Block S Cl), (backKinds true)[j]? = some k →
    senderKind k = true → (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := none, piece := j + 1, kind := k } →
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (353 + j)) (sn (353 + j)) b'

/-- The debt of a seated sub-protocol is its lot's own's: at the states of G. -/
theorem SendsOn.under {ft : ℕ} {codes : Codes} {G : S → Prop} {snd : List (Array OracleNotice)}
    {b b' : Block S Cl} (h : SendsOn ft codes G snd b') (hU : b.UnderR b') :
    SendsOn ft codes G snd b :=
  fun s s' rs cols n hg hy hc => h s s' rs cols n hg (VerifiableInference.Desc.step_under hU hy) hc

/-- At a link's first place, two stages: at the states of G. -/
theorem sends_first_on {ft : ℕ} {codes : Codes} {G : S → Prop} {snd : List (Array OracleNotice)}
    {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (hj : Joined Z l b b' a)
    (h : SendsOn ft codes G snd b') : SendsOn ft codes G snd b := by
  intro s s' rs cols n hg hy hc
  obtain ⟨fs, f, m, hfs, hf, h1, -, h3, -, -⟩ := hj.step hy
  obtain ⟨c1, a1, i1⟩ := h s m rs cols n hg h1 hc
  obtain ⟨k1, k2, k3⟩ := (frames_calm hfs (List.mem_of_getElem? hf)).2.1 m s' h3
  refine ⟨k1.trans c1, by rw [k3]; exact a1, fun hi => ?_⟩
  have := i1 hi
  unfold InStep at this ⊢
  rw [k2, k3]
  exact this

/-- A kind in front of a batching sends, or it is one of the six quiet makers', or K7. -/
theorem hear_kind_cases {sub : VerifiableInference.Desc.First.ModelPart} {f : Bool} {i : ℕ} {k : KindName}
    (h : (kindsBeforeBatching sub f)[i]? = some k) :
    senderKind k = true ∨ quietMaker k = true ∨ k = KindName.K7 := by
  have hall : (kindsBeforeBatching sub f).all (fun k => senderKind k || quietMaker k || k == .K7) = true := by
    cases sub <;> cases f <;> decide
  have h1 := List.all_eq_true.1 hall k (List.mem_of_getElem? h)
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The closed facts, drawn at a link. -/
theorem kinds_at {l : ℕ} (hl : l < 25) :
    kindW (14 * l + 1) = some .frame ∧ kindW (14 * l + nAt l + 2) = some .K9 ∧
      kindW (14 * l + nAt l + 3) = some .frame ∧ kindW (14 * l + nAt l + 4 + 0) = some .K9 ∧
      kindW (14 * l + nAt l + 4 + 1) = some .K10 ∧ kindW (14 * l + nAt l + 4 + 2) = some .K9 ∧
      kindW (14 * l + nAt l + 7) = some .frame := by
  have h := kinds_fit
  unfold kindsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c'⟩, d⟩, e⟩, f⟩, g⟩ := h.2 l hl
  exact ⟨a, b, c', d, e, f, g⟩

theorem kinds_ends : kindW 0 = some .frame ∧ kindW 355 = some .K13 ∧ kindW 357 = some .frame := by
  have h := kinds_fit
  unfold kindsFit at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

/-- **THE JOIN.** -/
theorem sends_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes}
    {sn : ℕ → List (Array OracleNotice)} {s₀ : S} (D : SendDebts ft codes sn Z Bs.G₀ c s₀) :
    ∀ j b, c.blocksInOrder[j]? = some b → SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ j) (sn j) b := by
  intro j b hb
  have hkind : kindW j = some b.place.kind := by
    unfold kindW
    rw [place_at hS hR O hb]
    rfl
  cases flat_cases hS hR O j b hb with
  | front b hr hd =>
    rw [D.calm 0 _ kinds_ends.1 rfl]
    exact (sends_front hd).on
  | laid l hl b hr hd =>
    rw [D.calm _ _ (kinds_at hl).1 rfl]
    exact (sends_laid hd).on
  | first l hl k0 b b' hk lot hp hj => exact sends_first_on hj (D.first l hl k0 b' hk lot hp)
  | hear l hl i hi k0 b b' name hk lot hp hla =>
    rcases hear_kind_cases hk with hs | hq | rfl
    · exact (D.hear l hl i k0 b' hi hk hs lot hp).under (alone_underR hla)
    · rw [D.calm _ k0 (by rw [hkind, alone_place hla]) (by
        revert hq; cases k0 <;> decide)]
      exact (sends_hear_quiet lot (by rw [hp]; exact hq) hla).on
    · exfalso
      revert hk
      have : i ≠ 0 := by omega
      cases (subAt l) <;> cases (l == 0) <;>
        (rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | omega | decide | skip)
      all_goals (intro h; simp [kindsBeforeBatching] at h)
  | batch l hl Lk p e1 hp hal =>
    rw [D.calm _ _ (kinds_at hl).2.1 rfl]
    exact D.batch l hl Lk e1
  | behind l hl Lk b e1 hr hd =>
    rw [D.calm _ _ (kinds_at hl).2.2.1 rfl]
    exact D.behind l hl Lk b e1 hr hd
  | close l hl p Q q k0 b x hp hQ hk ex hla =>
    rw [D.calm _ k0 (by rw [hkind, alone_place hla]) (by
      have hm := List.mem_of_getElem? hk
      revert hm
      cases k0 <;> decide)]
    exact (sends_close ex hla).on
  | cleared l hl fs f b hfs hf hr hd =>
    rw [D.calm _ _ (kinds_at hl).2.2.2.2.2.2 rfl]
    exact (sends_cleared hfs hf hd).on
  | back q k0 b b' name hk lot hp hla =>
    by_cases hs : senderKind k0 = true
    · exact (D.back q k0 b' hk hs lot hp).under (underR_bare (alone_underR hla))
    · -- of the four kinds behind the links the one that does not send is K13's
      have hk13 : q = 2 ∧ k0 = KindName.K13 := by
        revert hs hk
        rcases q with _ | _ | _ | _ | q
        · intro hk hs; cases Option.some.inj hk; exact absurd rfl hs
        · intro hk hs; cases Option.some.inj hk; exact absurd rfl hs
        · intro hk _; exact ⟨rfl, (Option.some.inj hk).symm⟩
        · intro hk hs; cases Option.some.inj hk; exact absurd rfl hs
        · intro hk _; cases hk
      obtain ⟨rfl, rfl⟩ := hk13
      rw [D.calm 355 _ kinds_ends.2.1 rfl]
      obtain ⟨-, -, ⟨b2, b2', e2, -, rfl, hla2⟩, -⟩ := back_of O
      have hix := (back_numbers hS hR O).1 2 b2 e2
      rw [Option.some.inj (hb.symm.trans hix)]
      exact (sends_355 hla2).on
  | last lot hla =>
    rw [D.calm 357 _ kinds_ends.2.2 rfl]
    exact (sends_last hla).on

/-- **THE TOP.** -/
theorem seats_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes}
    {sn : ℕ → List (Array OracleNotice)} {s₀ : S} (D : SendDebts ft codes sn Z Bs.G₀ c s₀)
    (hc : s₀.st.codes = codes) (hb : s₀.book = { trees := #[], place := #[] }) (hi : InStep s₀)
    {L : VerifiableInference.Desc.K12.Coin.Laid}
    (hL : laidOf codes ((List.range 358).flatMap sn) = some L) {k : ℕ} (hk : k ≤ 358)
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out) :
    SeatsPrefix L out.1.book ∧ InStep out.1 ∧ out.1.st.codes = codes ∧
      ∃ A, laidOf codes ((List.range k).flatMap sn) = some A ∧
        out.1.book.place.size = A.places.length ∧ out.1.book.trees.size = A.shapes.length := by
  have hlen : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]
  exact seats_at_cutR (sends_scope hS hR O D) hc hb hi (hlen ▸ hL) (hlen ▸ hk) hf

end

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE FIRST STATE AT WHICH THE DEBTS ARE MEANT: THE PROOF FILE's OWN, ProofFile.startS Z p**: where it bears no mark it has the public part's code table, an empty book, and is in step. At every o; no premise on scope. -/
theorem start_three (O : Open o pol lay KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (hu : (ProofFile.startS Z p).failed = none) :
    (ProofFile.startS Z p).st.codes = Z.first.codes ∧
      (ProofFile.startS Z p).book = { trees := #[], place := #[] } ∧ InStep (ProofFile.startS Z p) := by
  have h0 : S.startP (VerifiableInference.Desc.First.parP Z.first) Z.first.codes Z.first.shape
      Z.first.layout = some Z.s₀ := ProofFile.Law.pubBy_start (st := ProofFile.plainStarts) O.pub
  unfold S.startP at h0
  split at h0
  · have e := Option.some.inj h0
    unfold ProofFile.startS at hu ⊢
    dsimp only at hu ⊢
    split at hu
    · rename_i hq
      rw [if_pos hq, ← e]
      exact ⟨rfl, rfl, rfl⟩
    · exact nomatch hu
  · cases h0

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE TOP AT THE PROOF FILE's OWN FIRST STATE.** -/
theorem seats_start (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ}
    {sn : ℕ → List (Array OracleNotice)} (p : ProofFile.InstPub)
    (D : SendDebts ft Z.first.codes sn Z Bs.G₀ c (ProofFile.startS Z p))
    (hu : (ProofFile.startS Z p).failed = none) {L : VerifiableInference.Desc.K12.Coin.Laid}
    (hL : laidOf Z.first.codes ((List.range 358).flatMap sn) = some L) {k : ℕ} (hk : k ≤ 358)
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    SeatsPrefix L out.1.book ∧ VerifiableInference.Desc.placesAre L.places out.1.st out.1.book = true := by
  obtain ⟨h1, h2, h3⟩ := start_three O p hu
  obtain ⟨a, b, -, -⟩ := seats_scope hS hR O D h1 h2 h3 hL hk hf
  exact ⟨a, places_are a b⟩

end

end IM

#print axioms IM.start_three
#print axioms IM.seats_start
#print axioms IM.sender_count
#print axioms IM.kinds_fit
#print axioms IM.sends_scope
#print axioms IM.seats_scope
