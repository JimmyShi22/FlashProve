-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowAtSeat.lean: THE SMALLNESS TEST AT ITS SEAT IN onlineDescription's FIRST
CHAIN: "WHAT THE DRAWN MATRIX MULTIPLIES IS SENT BEFORE THE MATRIX IS DRAWN", AT THE RUN'S OWN
RECORD, AT ALL 25 PLACES: THE LAST JOINING. A LAW ABOUT ProofFile's DESCRIPTION, NO PART OF IT. NO
SOUNDNESS.

`k08_before_at_seat` (Johnson/P1K8R/BeforeAtSeat.lean) has its clauses (C) and (D) under the test
`Named.namedB`; `k08_arrays_at_seat` (OrderAtSeat.lean) pays two of that test's five clauses at
the record that the fold hands on in front of the draw. Here the other three are paid:
  `walkGives_of_seven`: `WalkSeven` (Johnson/IMR/WalkGivesAt.lean) IS
    `Named.WalkGives` (Johnson/Desc/First/K8/LawWalk.lean), field by field.
  `cuts`: at a place (l, i) the draw's entry has the number n + 4, with n the number of the entry of
    the link's first sending: 2 · 14 l + 2 · 339.
  `seven_at`: `walkGives_at0`, `walkGives_at`, `walkGives_at24` (WalkGivesAt.lean) at one n.
  `mid_at`: `mid_roots`, `mid_roots24` (Johnson/IMR/MidRoots.lean) at one n.
  `named_at_place`: one place.
  `k08_named_at_seat`: **IN SCOPE, FROM onlineDescription's VALUE F, UNDER F's TEST ON THE PLAN AND ONE
    PUBLIC TEST ON F ALONE (`namesDoorB F`, Johnson/Desc/First/K8/PlanDoor.lean): AT EACH OF THE 25
    PLACES, WHEREVER THE FOLD FROM THE FIRST RECORD OVER THE ENTRIES IN FRONT OF THE DRAW'S GOES ON:
    `Named.namedAt` SAYS YES AT THE RECORD THAT IT HANDS ON; and every array that the matrix
    multiplies lies, now, in a message that that record's statement and book have, in a tree that is
    sent strictly in front of the round of the draw; so does every EARLY CELL's array
    (`early_before_at_entry`); and the law's caller over the members' messages stands, by name, with
    every member's tree sent strictly in front of that round (`caller_before_at_entry`,
    Johnson/Desc/First/K8/LawEarly.lean).**
By calls: the guard of order (OrderAtSeat.lean) · the walk over the link's blocks and the count of
roots at every cut (`walkGives_at…`, `four_counts`, `mid_roots`) · the plan's
names (`names_of_door`, `planGives_of_ranges`: Johnson/Desc/First/K8/) · `Named.namedAt_of_walk`.
Limits. `namesDoorB F` IS A PREMISE: a test with code on public data, meant for the door through
which verify() asks such tests; it is shown true of no F here. THE FOLD STARTS AT THE FIRST RECORD
(`ProofFile.startS Z p`, any request p). MESSAGE-WISE: where inside its message an array's entries lie is
not said. That onlineDescription returns in scope is a premise.

-/
import Johnson.P1K8R.OrderAtSeat
import Johnson.IMR.WalkGivesAt
import Johnson.IMR.RootsTrees
import Johnson.IMR.MidRoots
import Johnson.Desc.First.K8.LawWalk
import Johnson.Desc.First.K8.LawPlanDoor
import Johnson.Desc.First.K8.LawEarly

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn sendRound foldBlocks)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K8
open ProofFile (Cl)

local notation "rIn" => VerifiableInference.Desc.roundsIn

/-- `WalkSeven`'s seven clauses are the seven fields of the structure `Named.WalkGives`. -/
theorem walkGives_of_seven {a b b' : ℕ} {s : S} (h : Meaning.K2.WalkSeven a b b' s) :
    Named.WalkGives a b b' s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- The draw's entry has the number n + 4, n the number of the entry of the link's first sending. -/
theorem cuts {x : ℕ × ℕ} (hx : x ∈ places) :
    x.1 < 25 ∧ x.2 < 7 ∧ ∃ n, 14 * x.1 + x.2 + 2 = n + 4 ∧
      ((x.1 = 0 ∧ n = 2) ∨ (1 ≤ x.1 ∧ x.1 < 24 ∧ n = 14 * x.1 + 2) ∨ (x.1 = 24 ∧ n = 339)) := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases h24 : l = 24
  · subst h24
    exact ⟨by omega, by decide, 339, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  · simp only [h24, if_false]
    refine ⟨hl', by omega, 14 * l + 2, by omega, ?_⟩
    by_cases h0 : l = 0
    · exact Or.inl ⟨h0, by omega⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega, rfl⟩)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The walk over the link's blocks, at one n. -/
theorem seven_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l n : ℕ}
    (hn : (l = 0 ∧ n = 2) ∨ (1 ≤ l ∧ l < 24 ∧ n = 14 * l + 2) ∨ (l = 24 ∧ n = 339))
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (t₀ t₁ t₄ : S) (R₀ R₁ R₄ : List Fmt.RoundView)
    (C₀ C₁ C₄ : List OpenedColumn)
    (f₀ : foldBlocks 0 (c.blocksInOrder.take n) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (n + 1)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₄ : foldBlocks 0 (c.blocksInOrder.take (n + 4)) (ProofFile.startS Z p) R C = .ok (t₄, R₄, C₄)) :
    Meaning.K2.WalkSeven t₀.roots t₁.roots t₄.roots t₄ ∧ t₀.roots ≤ t₁.roots ∧
      t₁.roots ≤ t₄.roots := by
  rcases hn with ⟨-, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨-, rfl⟩
  · exact Meaning.K2.walkGives_at0 hS hR O p R C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  · exact Meaning.K2.walkGives_at hS hR O l h1 h2 p R C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  · exact Meaning.K2.walkGives_at24 hS hR O p R C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄

/-- Between the link's first sending and the sending of the reads the count of roots stays. -/
theorem mid_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l n : ℕ}
    (hn : (l = 0 ∧ n = 2) ∨ (1 ≤ l ∧ l < 24 ∧ n = 14 * l + 2) ∨ (l = 24 ∧ n = 339))
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {r₁ r₃ : S × List Fmt.RoundView × List OpenedColumn}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (n + 1)) (ProofFile.startS Z p) R C = .ok r₁)
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (n + 3)) (ProofFile.startS Z p) R C = .ok r₃) :
    r₃.1.roots = r₁.1.roots := by
  rcases hn with ⟨rfl, rfl⟩ | ⟨_, h2, rfl⟩ | ⟨-, rfl⟩
  · exact Meaning.K2.mid_roots hS hR O (l := 0) (by omega) f₁ f₃
  · exact Meaning.K2.mid_roots hS hR O h2 f₁ f₃
  · exact Meaning.K2.mid_roots24 hS hR O f₁ f₃

/-- One place. -/
theorem named_at_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hP : F.planOk = true)
    (hD : namesDoorB F = true) {x : ℕ × ℕ} (hx : x ∈ places) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) (ProofFile.startS Z p) R C = .ok out) :
    Named.namedAt (ProofFile.k8ParW Z Bs.G₀ Xl x.1).toPar out.1 = true := by
  have ho := ordered_in_front (readsAt_open hS hR O x hx) 0 _ R C out f
  obtain ⟨hl, hi, n, en, hn⟩ := cuts hx
  have hk := Meaning.K2.draw_in_front hS hR O hl hi
  obtain ⟨_, b, Xl', _, _, hf, e3', hla, _, hlk, _⟩ := sitsAt_open hS hR O x hx
  obtain rfl : Xl' = Xl := Option.some.inj (e3'.symm.trans e3)
  have hd := O.desc
  subst hd
  rw [en] at f hf hk
  obtain ⟨_, bM, bR, eM, eR, _, _, hnm⟩ := names_of_door hD (i := n + 4) hf
    (by rw [IM.alone_place hla]) hlk.before
  have e4 : n + 4 - 4 = n := by omega
  have e1 : n + 4 - 1 = n + 3 := by omega
  rw [e4] at eM
  rw [e1] at eR
  rw [e4, e1] at hnm
  obtain ⟨t₄, R₄, C₄⟩ := out
  obtain ⟨t₃, R₃, C₃, f₃⟩ := Meaning.K2.fold_back (k := n + 3) f
  obtain ⟨t₂, R₂, C₂, f₂⟩ := Meaning.K2.fold_back (k := n + 2) f₃
  obtain ⟨t₁, R₁, C₁, f₁⟩ := Meaning.K2.fold_back (k := n + 1) f₂
  obtain ⟨t₀, R₀, C₀, f₀⟩ := Meaning.K2.fold_back (k := n) f₁
  obtain ⟨W, hab, hbb⟩ := seven_at hS hR O hn p R C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f
  have hp : ∀ b ∈ c.blocksInOrder.take (n + 3 + 1), b.planOk = true := fun b hb =>
    (((FileDescription.planOk_ok _).1 hP).blocks₁ b (List.mem_of_mem_take hb)).1
  have hq : t₃.roots = t₁.roots := mid_at hS hR O hn f₁ f₃
  obtain ⟨c1, c2, c3, c4⟩ := Meaning.Carry.four_counts O n (n + 3) (by omega) hk hp 0 _
    (Meaning.K2.start_empty O.pub p).2 R C f₀ f₁ f₃ f hq eM eR
  exact Named.namedAt_of_walk ho (walkGives_of_seven W) hab hbb
    (Named.planGives_of_ranges hnm c1 c2 c3 c4)

end

section
open Cb Cb.Pv.Tail KObj Johnson.Pack VerifiableInference.Desc.Sound

/-- **"M BEFORE THE DRAW", AT THE SEAT, AT THE RUN'S OWN RECORD, AT ALL 25 PLACES.** -/
theorem k08_named_at_seat {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hP : F.planOk = true)
    (hD : namesDoorB F = true) :
    ∃ (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ x ∈ places, ∃ Xl, G₀.built[x.1]? = some Xl ∧
        ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
          foldBlocks 0 (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) (ProofFile.startS Z p) R C = .ok out →
          Named.namedAt (ProofFile.k8ParW Z G₀ Xl x.1).toPar out.1 = true ∧
          ∃ tl L, out.1.tl? = some tl ∧ out.1.link? = some L ∧
            (∀ t ∈ Named.arrays tl, ∃ o m j, Named.msgNow L t = some o ∧
              Named.memberAt out.1.st out.1.book o = some m ∧
              sendRound F.roundsDeclaredByBlocks.1 m.2.1 = some j ∧
              j < rIn (c.blocksInOrder.take (14 * x.1 + x.2 + 2))) ∧
            (∀ t r k, OnBytes.Tie.Pv.Tail.early tl (.cell t r k) = true →
              ∃ o m j, Named.msgNow L t = some o ∧
                Named.memberAt out.1.st out.1.book o = some m ∧
                sendRound F.roundsDeclaredByBlocks.1 m.2.1 = some j ∧
                j < rIn (c.blocksInOrder.take (14 * x.1 + x.2 + 2))) ∧
            ∀ (cs : OnBytes.Codes) (rad : OnBytes.OracleShape → ℕ) (tl0 : HTailF2)
              (Θ : TLetters Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0))
              (rdm : (sigOf cs (Named.listOf rad out.1.st out.1.book tl L)).Msg → Θ.M),
              ∃ K : CallerAt (ProofFile.k8ParW Z G₀ Xl x.1).toPar
                  (tailCallerOf (OnBytes.Tie.Pv.Tail.sizeOf tl0) Θ
                    (sigOf cs (Named.listOf rad out.1.st out.1.book tl L)) rdm),
                (∀ a, K.dep a) ∧
                (∀ a, K.no a = (Named.seatFn rad out.1.st out.1.book tl L a).1) ∧
                ∀ a, ∃ j, sendRound F.roundsDeclaredByBlocks.1 (K.no a) = some j ∧
                  j < rIn (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  refine ⟨Z, Bs.G₀, c, A, B, O.pub, O.blank, O.desc, fun x hx => ?_⟩
  have hd := O.desc
  obtain ⟨b, Xl, _, e3, _, hB⟩ := beforeAt_of_sits (sitsAt_open hS hR O x hx) (hd ▸ hP)
  obtain ⟨_, b', Xl', _, _, hf, e3', _, _, hlk, _⟩ := sitsAt_open hS hR O x hx
  obtain rfl : Xl' = Xl := Option.some.inj (e3'.symm.trans e3)
  refine ⟨Xl', e3, fun p R C out f => ?_⟩
  have hN := named_at_place hS hR O hP hD hx e3 p R C out f
  have ho := ordered_in_front (readsAt_open hS hR O x hx) 0 _ R C out f
  obtain ⟨tl, L, ht, hl, _⟩ := Named.ordered_spec ho
  have hNB : Named.namedB (ProofFile.k8ParW Z Bs.G₀ Xl' x.1).toPar out.1.st out.1.book tl L = true := by
    unfold Named.namedAt at hN
    rw [ht, hl] at hN
    exact hN
  subst hd
  exact ⟨hN, tl, L, ht, hl, (hB.2.2.2.2 out.1.st out.1.book tl L hNB).1,
    fun t r k he => early_before_at_entry _ hlk _ hf hP _ _ tl L hNB t r k he,
    fun cs rad tl0 Θ rdm => caller_before_at_entry _ hlk _ hf hP cs rad _ _ tl L tl0 Θ rdm hNB⟩

end

end P1K8S

#print axioms P1K8S.seven_at
#print axioms P1K8S.named_at_place
#print axioms P1K8S.k08_named_at_seat
