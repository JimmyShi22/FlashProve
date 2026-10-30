-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/LinkSeat.lean.
one_at_place · block_by_place: in a seat without a fault two blocks of the lots, of a kind, at one
place, are one: SO A CALLER CAN NAME b' BY ITS OWN TERM. NOTE: faults_unique
(Johnson/Loose/H2K12/SitsInPure.lean) says the same of faultsOf.
The rest of this head may differ from this file's text; where it does, the text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: A LINK OF onlineDescription's FIRST CHAIN: K9's
PLACE (its batching), its two orders, its two tests, its name and numbers. (Its hearing blocks: the
other seats. Its lay | clear: Johnson/IMR/FrameSeat.lean. Its close: Johnson/IMR/CloseSeat.lean.)
OBJECT. THE SEATED CONSTANT AT K9's PLACE: VerifiableInference.Desc.K9.batch K9.atS p g (Johnson/Desc/First/Batch/Kind.lean), p given by ProofFile.k9Where (ProofFile.k9Stretches Z) l = some p (Johnson/Desc/ProofFile/Lot/K9.lean: k9Ninth's field batch), g: WHATEVER
GATHERER THE FRAME HANDS IT: Link.blocksInOrder hands it claimsInBy Lk.each Lk.hear Lk.order (Johnson/Desc/Block.lean). AND Lk.each | Lk.tests: the same lot's K9.eachAtS … | ProofFile.k9Tests Z l WHERE testsWhere | k9Tests RETURN (in scope they do: testsWhere_scope), ELSE THE TESTS THAT ALWAYS PASS; Lk.order | orderAfter: the driver's orderOf | orderAfterOf.
USER. K9's laws at the seated batching · every kind that states a run (K3 · K4 · K5 · K6 · K8 · K11): with ‹kind›_of's Lk.hear[i]? = some b, claims_lookup (Johnson/IMR/SeatForm.lean) and Lk.order = orderOf sub, «the frame looks up run (i, name) in this Lk» has its object.
LETTERS. As in Johnson/IMR/K6Seat.lean. p: HANDED OUT BY k9At Z l = some p. «The seat has no fault» is the opening's own clause (Open.sound).

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are still owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  link_fields       (general in the seat) a link of chainBy's chain: name · chain · number · order · orderAfter · each · tests · the number of hearing blocks · Lk.batch g = guarded { batch0 g with place := a9 }; EITHER batch0 is the road's maker at a9, OR the road has none there and SOME
                    entry (sp, ok b0) of the list of places bears the address a9 (batch0 is not tied to b0 in the statement: the arm serves to be shut out).
  stands_in_shape · shape_places · k10_in_flat   BY PLACES, NOT BY NAMES: in a seat without a fault a block of a kind stands at a place of the shape; the shape's places are the driver's table (flat_places); the table's one place of the kind K10 in link l is piece n + 4.
  k9_batch_some | _congr · only_K9_makes · lot_K9 · k9_own_mem · k9Where_fields · k10Par_fields   K9's lot's text.
  k9_alone          (no premise on scope) at every link l of the row of links: k9At Z l = some p · p.piece = n + 1 · ∀ g, Lk.batch g IS seatedAs sameReply (K9.batch atS p g) (Lk.batch g).name a9: ALONE · the link's other fields.
                    HOW THE FALL-BACK IS SHUT OUT (fill: «fr.batch a <|> the list's block at a, which drops the gatherer»): were the road's maker none at a9, a block of the list bore a9: EITHER another spot's face: then K9's lot answers at a9 too (its maker hangs on kind,
                    link and piece alone); OR one of the closing's two blocks of the kind K9: but their sibling of the kind K10 stands, for want of a fault, at piece n + 4, so they stand at n + 3 and n + 5.
  road_each | road_tests   Link.each | tests at onlineDescription's seat, evaluated: K9's lot alone gives them.
  batch_in_flat     (general in the link; Block.lean's text) Lk.blocksInOrder[Lk.hear.length + 1]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).
  subAt · subs_scope · subAt_head | _layers | _attention · sortAt · testsWhere_scope   in scope: the sort of link l; testsWhere RETURNS at every l < 25, with the sort of the order that is run.
  links_25          in scope: c.links.length = 25 (the driver's linksOk: the head stands last and nowhere else; it stands at 24).
  k9_of             in scope: 25 links, and at every l < 25: p (piece n + 1 · chain 1 · link l · pieceEq = piece + 2) · ∀ g, Lk.batch g ALONE · c.blocksInOrder[14 * l + Lk.hear.length + 2]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)): THE BATCHING THAT THE FOLD
                    RUNS, BY ITS NUMBER IN THE FLAT LIST · the orders · testsWhere Z.p.X l 0 = some w ∧ w.1 = sortAt l ∧ Lk.each = K9.eachAtS w.1 · k9Tests Z l = some T ∧ Lk.tests = T: NO «.getD».

WHO PAYS THE PREMISES: as in Johnson/IMR/K6Seat.lean.
What is not claimed. OUTSIDE THE SCOPE (k9_alone · road_each · road_tests): the statements leave the arm «the test that always passes» open (a match on testsWhere | k9Tests). lackingAt (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean, read in another version) REFUSES a seat at which a link of the plan has no giver of each | tests: that this shuts the arm at every link of the row
is not typed here. Nothing on Lk.lay | clear | close. Of p: rows | work | sent are known through k9At's equation alone. Nothing on what K9.batch decides. (Lk.batch g).name: which string it is. F.first is c by rfl only behind «subst» on O.desc. No soundness.

-/
import Johnson.IMR.LaidFirst
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs
import Johnson.IMR.FlatScope

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

universe u v

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard linkAt blockAt kindsBeforeBatching addresses hearsReply
  orderOf orderAfterOf flatPlacesOf linkPlaces closeAddresses closeKinds backKinds frameAt)
open OnBytes.L5.LinksOrder (ok_bind)
open ProofFile (Cl)

/-- The batching's address in link l. -/
abbrev a9Of (l : ℕ) (sub : ModelPart) : Place :=
  { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1, kind := .K9 }

/-! ## 1 A link's fields, by the driver's and the fold's texts -/

/-- **A link of the chain: its name, numbers, two orders, two tests, and its batching.** -/
theorem link_fields {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hb : (ProofFile.partsAt T B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c) (l : ℕ)
    (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) :
    ∃ (Lk : Link S Cl) (batch0 : ProofFile.Gatherer → Block S Cl), c.links[l]? = some Lk ∧
      Lk.name = s!"link {l}" ∧ Lk.chain = 1 ∧ Lk.number = l ∧ Lk.order = orderOf sub ∧
      Lk.orderAfter = orderAfterOf sub ∧ Lk.each = (ProofFile.partsAt T B).road.each l ∧
      Lk.tests = (ProofFile.partsAt T B).road.tests l ∧
      Lk.hear.length = (kindsBeforeBatching sub (l == 0)).length ∧
      (∀ g, Lk.batch g = Block.guarded T.same hearsReply { batch0 g with place := a9Of l sub }) ∧
      ((ProofFile.partsAt T B).road.batch (a9Of l sub) = some batch0 ∨
        ((ProofFile.partsAt T B).road.batch (a9Of l sub) = none ∧
          ∃ sp b0, (sp, Except.ok b0) ∈ (ProofFile.partsAt T B).places ∧ b0.place = a9Of l sub)) := by
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · rename_i z hz
    dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        obtain ⟨Lk, hLk, eLk⟩ := firstChain_link h1 l sub hl
        unfold linkAt at hLk
        simp only [Option.bind_eq_bind, Option.pure_def] at hLk
        obtain ⟨hear, hh, hLk⟩ := Option.bind_eq_some_iff.1 hLk
        obtain ⟨batch, hbt, hLk⟩ := Option.bind_eq_some_iff.1 hLk
        obtain ⟨close, hcl, hLk⟩ := Option.bind_eq_some_iff.1 hLk
        cases hLk
        have hlen : hear.length = (kindsBeforeBatching sub (l == 0)).length := by
          rw [VerifiableInference.Desc.First.length_of_mapM _ _ _ hh,
            VerifiableInference.Desc.First.length_addresses]
        refine ⟨_, batch, eLk, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun g => rfl, ?_⟩
        · show (hear.map _).length = _
          rw [List.length_map, hlen]
        · cases hr : (ProofFile.partsAt T B).road.batch (a9Of l sub) with
          | some mk =>
            left
            have hbt' : ((ProofFile.partsAt T B).road.batch (a9Of l sub) <|> _) = some batch := hbt
            rw [hr] at hbt'
            exact hbt'
          | none =>
            right
            refine ⟨rfl, ?_⟩
            have hbt' : ((ProofFile.partsAt T B).road.batch (a9Of l sub) <|> _) = some batch := hbt
            rw [hr] at hbt'
            obtain ⟨b, hb', -⟩ := Option.map_eq_some_iff.1 hbt'
            have hm := List.mem_of_find?_eq_some hb'
            have hpl : b.place = a9Of l sub := by simpa using List.find?_some hb'
            obtain ⟨b0, hb0, ej⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hm)
            obtain ⟨x, hx, ex⟩ := OnBytes.Road.L5.mapM_mem _ _ _ hb b0 hb0
            obtain ⟨sp, y⟩ := x
            obtain rfl : y = .ok b0 := ex
            refine ⟨sp, b0, hx, ?_⟩
            split at ej <;> subst ej <;> exact hpl

/-! ## 2 A seat without a fault: its blocks of a kind stand at the driver's places -/

/-- In a seat without a fault every block of a kind stands at a place of the shape. -/
theorem stands_in_shape {T : ProofFile.PureSeat} {B : ProofFile.PureBase} (hf : ProofFile.faultsAt T B = [])
    {o : Block S Cl} (ho : o ∈ B.all.flatMap fun x => x.2) (hk : o.place.kind ≠ KindName.frame) :
    ∃ e ∈ B.shape, e.2 = o.place := by
  simp only [ProofFile.faultsAt, ProofFile.faultsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at hf
  obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hf
  have h2 := List.filter_eq_nil_iff.1 h1 o ho
  have hk' : (o.place.kind != KindName.frame) = true := by simpa using hk
  rw [hk', Bool.true_and] at h2
  have h3 : (B.shape.any fun b => b.2 == o.place) = true := by simpa using h2
  obtain ⟨e, he, h4⟩ := List.any_eq_true.1 h3
  exact ⟨e, he, by simpa using h4⟩

/-- **In a seat without a fault at most one block stands at a place of the shape**: over all blocks of all lots. -/
theorem one_at_place {T : ProofFile.PureSeat} {B : ProofFile.PureBase} (hf : ProofFile.faultsAt T B = [])
    {b₁ b₂ : Block S Cl} (h₁ : b₁ ∈ B.all.flatMap fun x => x.2) (h₂ : b₂ ∈ B.all.flatMap fun x => x.2)
    {e : String × Place} (he : e ∈ B.shape) (e₁ : b₁.place = e.2) (e₂ : b₂.place = e.2) : b₁ = b₂ := by
  simp only [ProofFile.faultsAt, ProofFile.faultsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at hf
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩, -⟩, -⟩ := hf
  have h4 := List.filter_eq_nil_iff.1 h3 e he
  have h5 : ((B.all.flatMap fun x => x.2).filter fun o => o.place == e.2).length ≤ 1 := by
    simpa using h4
  have m₁ : b₁ ∈ (B.all.flatMap fun x => x.2).filter fun o => o.place == e.2 :=
    List.mem_filter.2 ⟨h₁, by simpa using e₁⟩
  have m₂ : b₂ ∈ (B.all.flatMap fun x => x.2).filter fun o => o.place == e.2 :=
    List.mem_filter.2 ⟨h₂, by simpa using e₂⟩
  generalize (B.all.flatMap fun x => x.2).filter (fun o => o.place == e.2) = L at h5 m₁ m₂
  match L, h5, m₁, m₂ with
  | [x], _, m₁, m₂ =>
    rw [List.mem_singleton.1 m₁, List.mem_singleton.1 m₂]

/-- **So a lot's block of a kind is named by its place**: two blocks of a seat's lots, of a kind, at one place, are one. -/
theorem block_by_place {T : ProofFile.PureSeat} {B : ProofFile.PureBase} (hf : ProofFile.faultsAt T B = [])
    (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) {L₁ L₂ : ProofFile.Lot} (hL₁ : L₁ ∈ T.lots)
    (hL₂ : L₂ ∈ T.lots) {b₁ b₂ : Block S Cl} (h₁ : b₁ ∈ L₁.blocks B.G₀) (h₂ : b₂ ∈ L₂.blocks B.G₀)
    (hk : b₁.place.kind ≠ KindName.frame) (hp : b₁.place = b₂.place) : b₁ = b₂ := by
  have m : ∀ {L : ProofFile.Lot} {b : Block S Cl}, L ∈ T.lots → b ∈ L.blocks B.G₀ →
      b ∈ B.all.flatMap fun x => x.2 := fun {L b} hL hb => by
    rw [hall]
    exact List.mem_flatMap.2 ⟨(L, L.blocks B.G₀), List.mem_map.2 ⟨L, hL, rfl⟩, hb⟩
  obtain ⟨e, he, ee⟩ := stands_in_shape hf (m hL₁ h₁) hk
  exact one_at_place hf (m hL₁ h₁) (m hL₂ h₂) he ee.symm (hp ▸ ee.symm)

/-- The shape's places are the driver's table. -/
theorem shape_places {Z : ProofFile.Pub} {shape : List (String × Place)} (h : ProofFile.shapeOf Z = .ok shape) :
    ∃ several, shape.map (·.2) = flatPlacesOf (ProofFile.subsOf Z) several := by
  unfold ProofFile.shapeOf at h
  obtain ⟨spots, _, h⟩ := ok_bind h
  dsimp only at h
  obtain ⟨c, hc, h⟩ := ok_bind h
  cases h
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        have e := VerifiableInference.Desc.First.flat_places _ _ _ _ h1
        exact ⟨_, by rw [List.map_map]; exact e⟩

theorem no_K10_hears (sub : ModelPart) (f : Bool) : KindName.K10 ∉ kindsBeforeBatching sub f := by
  cases sub <;> cases f <;> decide

/-- **The driver's one place of the kind K10 in link l is piece n + 4.** -/
theorem k10_in_flat {links : List ModelPart} {several : Bool} {l q : ℕ}
    (h : (⟨1, some l, q, .K10⟩ : Place) ∈ flatPlacesOf links several) :
    ∃ sub, links[l]? = some sub ∧ q = (kindsBeforeBatching sub (l == 0)).length + 4 := by
  unfold flatPlacesOf at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_cons.1 h with h | h
      · cases h
      · obtain ⟨x, hx, h⟩ := List.mem_flatMap.1 h
        obtain ⟨sub, l'⟩ := x
        have hx' : links[l']? = some sub := by simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hx)
        unfold linkPlaces at h
        dsimp only at h
        rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · rcases List.mem_append.1 h with h | h
            · rcases List.mem_cons.1 h with h | h
              · cases h
              · unfold addresses at h
                obtain ⟨y, hy, e⟩ := List.mem_map.1 h
                have hk : y.1 = KindName.K10 := congrArg Place.kind e
                have hm : y.1 ∈ kindsBeforeBatching sub (l' == 0) := (List.mem_zipIdx hy).2.2 ▸ List.getElem_mem _
                rw [hk] at hm
                exact absurd hm (no_K10_hears _ _)
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h <;> cases h
          · unfold closeAddresses closeKinds at h
            simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons,
              List.not_mem_nil, or_false] at h
            rcases h with h | h | h
            · cases h
            · cases h
              exact ⟨sub, hx', rfl⟩
            · cases h
        · obtain h := List.mem_singleton.1 h
          cases h
    · unfold addresses at h
      obtain ⟨y, _, e⟩ := List.mem_map.1 h
      cases e
  · obtain h := List.mem_singleton.1 h
    cases h

/-! ## 3 K9's lot -/

theorem lookup_map_self {β : Type} (f : ℕ → β) (l : ℕ) (v : β) : ∀ L : List ℕ,
    (L.map fun k => (k, f k)).lookup l = some v → v = f l
  | [], h => by cases h
  | k :: L, h => by
    simp only [List.map_cons, List.lookup_cons] at h
    cases e : l == k with
    | true =>
      rw [e] at h
      obtain rfl : l = k := by simpa using e
      exact (Option.some.inj h).symm
    | false =>
      rw [e] at h
      exact lookup_map_self f l v L h

/-- K9's numbers at a segment, as its lot reads them. -/
abbrev k9At (Z : ProofFile.Pub) (l : ℕ) : Option VerifiableInference.Desc.K9.Where :=
  ProofFile.k9Where (ProofFile.k9Stretches Z) l

theorem k9Where_fields {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × ℕ)} {l : ℕ}
    {p : VerifiableInference.Desc.K9.Where} (h : ProofFile.k9Where xs l = some p) :
    p.chain = 1 ∧ p.link = l ∧ p.pieceEq = p.piece + 2 := by
  unfold ProofFile.k9Where at h
  obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨d, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, rfl, rfl⟩

/-- **What K9's lot's maker is, where it gives one.** -/
theorem k9_batch_some {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {mk : ProofFile.Gatherer → Block S Cl}
    (h : (ProofFile.k9Ninth Z).batch G a = some mk) :
    ∃ l p, a.kind = KindName.K9 ∧ a.link = some l ∧ k9At Z l = some p ∧ p.piece = a.piece ∧
      mk = fun g => VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p g := by
  unfold ProofFile.k9Ninth at h
  dsimp only at h
  split at h
  · rename_i l hk hl
    obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, hv, e⟩ := Option.bind_eq_some_iff.1 hp
    have ev := lookup_map_self _ _ _ _ hv
    split at h
    · rename_i hpc
      obtain rfl := Option.some.inj h
      refine ⟨l, p, hk, hl, ?_, by simpa using hpc, rfl⟩
      subst ev
      exact e
    · cases h
  · cases h

/-- The maker hangs on the address's kind, link and piece alone. -/
theorem k9_batch_congr (Z : ProofFile.Pub) (G : ProofFile.Ground) {a a' : Place} (hk : a.kind = a'.kind)
    (hl : a.link = a'.link) (hp : a.piece = a'.piece) :
    (ProofFile.k9Ninth Z).batch G a = (ProofFile.k9Ninth Z).batch G a' := by
  unfold ProofFile.k9Ninth
  dsimp only
  rw [hk, hl, hp]

/-- K9's lot alone gives a maker. -/
theorem only_K9_makes {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {a : Place} {mk : ProofFile.Gatherer → Block S Cl} (hmk : L.batch G a = some mk) :
    L = ProofFile.k9Ninth Z := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  iterate 7 exact nomatch hmk
  · rfl
  iterate 7 exact nomatch hmk

/-- A block of kind K9 or K10 of the seat is one of K9's lot's own, carried over. -/
theorem lot_K9 {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b : Block S Cl} (hb : b ∈ L.blocks G)
    (hk : b.place.kind = KindName.K9 ∨ b.place.kind = KindName.K10) : L = ProofFile.k9Ninth Z := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  · rw [kind_frames Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K1 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K2 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K3 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K4 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K5 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K8 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rfl
  · rw [kind_K11 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K12 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K13 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K13_4 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K13_end Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K6 Z G b hb] at hk; rcases hk with h | h <;> cases h
  · rw [kind_K7_lot rfl rfl b hb] at hk; rcases hk with h | h <;> cases h

/-- **K9's lot's own blocks, segment by segment**: the closing's three at that segment's numbers, or a refuser at piece 0 of the kind K10. -/
theorem k9_own_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : Block S Unit} (h : x ∈ (ProofFile.k9Ninth Z).own G) :
    (∃ l p P, k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some P ∧
        x ∈ VerifiableInference.Desc.K9.closeOf p P ∧
        ∀ y ∈ (VerifiableInference.Desc.K9.closeOf p P : List (Block S Unit)),
          y ∈ (ProofFile.k9Ninth Z).own G) ∨
      ∃ l, x.place = ⟨1, some l, 0, KindName.K10⟩ := by
  unfold ProofFile.k9Ninth at h ⊢
  dsimp only at h ⊢
  obtain ⟨w, hw, hx⟩ := List.mem_flatMap.1 h
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hw
  dsimp only at hx
  split at hx
  · rename_i p P hpP
    obtain ⟨p', hp', e⟩ := Option.bind_eq_some_iff.1 hpP
    obtain ⟨P', hP', e⟩ := Option.map_eq_some_iff.1 e
    cases e
    refine Or.inl ⟨l, p, P, hp', hP', hx, fun y hy => ?_⟩
    refine List.mem_flatMap.2 ⟨_, hw, ?_⟩
    dsimp only
    rw [hpP]
    exact hy
  · obtain rfl := List.mem_singleton.1 hx
    exact Or.inr ⟨l, rfl⟩

theorem k10Par_fields {Z : ProofFile.Pub} {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × ℕ)}
    {p : VerifiableInference.Desc.K9.Where} {P : VerifiableInference.Desc.First.Close.Par}
    (h : ProofFile.k10Par Z xs p = some P) : P.link = p.link ∧ P.piece = p.pieceEq + 1 := by
  unfold ProofFile.k10Par at h
  obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Gr, _, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-! ## 4 K9's place -/

section
variable {pol lay KL : ByteArray} {F F' : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The road's maker at an address, opened: it is K9's lot's. -/
theorem road_batch_some {a : Place} {mk : ProofFile.Gatherer → Block S Cl}
    (h : (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road.batch a = some mk) :
    ∃ mk0, (ProofFile.k9Ninth Z).batch Bs.G₀ a = some mk0 ∧ ∀ g, ∃ name, mk g = marked (mk0 g) name := by
  simp only [ProofFile.partsAt] at h
  obtain ⟨mk0, hmk, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some hmk
  obtain rfl := only_K9_makes (List.mem_filter.1 hL).1 e
  exact ⟨mk0, e, fun g => ⟨_, rfl⟩⟩

/-- Where K9's lot gives a maker at an address, the road has one there. -/
theorem road_batch_ne {a : Place} {mk0 : ProofFile.Gatherer → Block S Cl}
    (h : (ProofFile.k9Ninth Z).batch Bs.G₀ a = some mk0) :
    (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road.batch a ≠ none := by
  intro hn
  simp only [ProofFile.partsAt] at hn
  rw [Option.map_eq_none_iff, List.findSome?_eq_none_iff] at hn
  have hm : ProofFile.k9Ninth Z ∈ (ProofFile.pureSeat o Z).lots.filter fun L => !L.letters := by
    refine List.mem_filter.2 ⟨?_, rfl⟩
    show ProofFile.k9Ninth Z ∈ ProofFile.onlineFirstChainBlockTables Z
    unfold ProofFile.onlineFirstChainBlockTables
    simp
  rw [hn _ hm] at h
  cases h

/-- **K9's PLACE: THE BATCHING IS K9's FILES' OWN, AT THE FRAME's GATHERER, ALONE**, and the link's other fields. No premise on scope. -/
theorem k9_alone (O : Open o pol lay KL F Z Bs base c A B) (l : ℕ) (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) :
    ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where), c.links[l]? = some Lk ∧
      k9At Z l = some p ∧ p.piece = (kindsBeforeBatching sub (l == 0)).length + 1 ∧ p.chain = 1 ∧ p.link = l ∧
      p.pieceEq = p.piece + 2 ∧
      (∀ g, LaidAlone ProofFile.sameReply (Lk.batch g)
        (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p g) (Lk.batch g).name
        (a9Of l sub)) ∧
      Lk.name = s!"link {l}" ∧ Lk.chain = 1 ∧ Lk.number = l ∧ Lk.order = orderOf sub ∧
      Lk.orderAfter = orderAfterOf sub ∧ Lk.hear.length = (kindsBeforeBatching sub (l == 0)).length ∧
      Lk.each = (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road.each l ∧
      Lk.tests = (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road.tests l := by
  obtain ⟨hs, hsh, -, hall⟩ := base_made O.made
  have hf := O.sound
  obtain ⟨Lk, batch0, e1, n1, n2, n3, n4, n5, n6, n7, n8, hbat, harm⟩ :=
    link_fields O.places O.chain l sub hl
  have hroad : ∃ mk, (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road.batch (a9Of l sub) = some mk := by
    rcases harm with h | ⟨hn, sp, b0, hx, hpl⟩
    · exact ⟨_, h⟩
    · exfalso
      obtain ⟨hsp, harm2⟩ := places_from_lots hall sp b0 hx
      rcases harm2 with ⟨mk', hmk', rfl⟩ | ⟨-, L, hL, b', hb', ep, rfl⟩
      · -- the face of another spot bears the batching's address: then K9's lot answers at that address too
        obtain ⟨mk0, h0, hm⟩ := road_batch_some hmk'
        obtain ⟨l'', p', k1, k2, k3, k4, rfl⟩ := k9_batch_some h0
        obtain ⟨nm, enm⟩ := hm (fun s => .ok ([], s))
        rw [enm] at hpl
        obtain ⟨f1, f2, -⟩ := k9Where_fields k3
        have hpl' : (⟨p'.chain, some p'.link, p'.piece, KindName.K9⟩ : Place) = a9Of l sub := hpl
        have e2 : (some p'.link : Option ℕ) = some l := congrArg Place.link hpl'
        have e3 : p'.piece = (kindsBeforeBatching sub (l == 0)).length + 1 := congrArg Place.piece hpl'
        have hc9 := k9_batch_congr Z Bs.G₀ (a := sp.place) (a' := a9Of l sub) k1
          (by rw [k2, ← f2]; exact e2) (by rw [← k4]; exact e3)
        rw [h0] at hc9
        exact road_batch_ne hc9.symm hn
      · -- a block of a lot at the batching's address: it were one of the closing's: but the closing's K10 stands at n + 4
        have hpl' : b'.place = a9Of l sub := hpl
        obtain rfl := lot_K9 hL hb' (Or.inl (by rw [hpl']))
        rcases blocks_mem hb' with ⟨x, hx', rfl⟩ | h
        · rcases k9_own_mem hx' with ⟨l', p, P, hp, hP, hxc, hallc⟩ | ⟨l', e⟩
          · obtain ⟨f1, f2, f3⟩ := k9Where_fields hp
            obtain ⟨g1, g2⟩ := k10Par_fields hP
            -- the closing's own block stands at a place of the shape
            have hcl : (VerifiableInference.Desc.K9.closing P : Block S Unit) ∈
                (VerifiableInference.Desc.K9.closeOf p P : List (Block S Unit)) := by
              unfold VerifiableInference.Desc.K9.closeOf
              simp
            have hin : ((VerifiableInference.Desc.K9.closing P : Block S Unit).retype : Block S Cl) ∈
                Bs.all.flatMap fun x => x.2 := by
              rw [hall]
              refine List.mem_flatMap.2 ⟨(ProofFile.k9Ninth Z, (ProofFile.k9Ninth Z).blocks Bs.G₀),
                List.mem_map.2 ⟨_, hL, rfl⟩, ?_⟩
              unfold ProofFile.Lot.blocks ProofFile.asCl
              exact List.mem_append_left _ (List.mem_map.2 ⟨_, hallc _ hcl, rfl⟩)
            obtain ⟨e, he, e2⟩ := stands_in_shape hf hin (by
              show KindName.K10 ≠ KindName.frame
              decide)
            obtain ⟨several, hpls⟩ := shape_places hsh
            have hmem : (⟨1, some P.link, P.piece, KindName.K10⟩ : Place) ∈
                flatPlacesOf (ProofFile.subsOf Z) several := by
              rw [← hpls]
              exact List.mem_map.2 ⟨e, he, e2⟩
            obtain ⟨sub', hs', hq⟩ := k10_in_flat hmem
            -- x is the one equation or «shut», at the batching's address
            unfold VerifiableInference.Desc.K9.closeOf at hxc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hxc
            rcases hxc with rfl | rfl | rfl
            · have h1 : (⟨p.chain, some p.link, p.pieceEq, KindName.K9⟩ : Place) = a9Of l sub := hpl'
              have e3 : (some p.link : Option ℕ) = some l := congrArg Place.link h1
              have e4 : p.pieceEq = (kindsBeforeBatching sub (l == 0)).length + 1 := congrArg Place.piece h1
              obtain rfl : p.link = l := Option.some.inj e3
              rw [g1, hl] at hs'
              obtain rfl := Option.some.inj hs'
              rw [g1] at hq
              omega
            · have h1 : (⟨1, some P.link, P.piece, KindName.K10⟩ : Place) = a9Of l sub := hpl'
              have e5 : KindName.K10 = KindName.K9 := congrArg Place.kind h1
              cases e5
            · have h1 : (⟨p.chain, some p.link, P.piece + 1, KindName.K9⟩ : Place) = a9Of l sub := hpl'
              have e3 : (some p.link : Option ℕ) = some l := congrArg Place.link h1
              have e4 : P.piece + 1 = (kindsBeforeBatching sub (l == 0)).length + 1 := congrArg Place.piece h1
              obtain rfl : p.link = l := Option.some.inj e3
              rw [g1, hl] at hs'
              obtain rfl := Option.some.inj hs'
              rw [g1] at hq
              omega
          · have h1 : (x.retype : Block S Cl).place = x.place := rfl
            rw [h1, e] at hpl'
            cases hpl'
        · exact nomatch h
  obtain ⟨mk, hmk⟩ := hroad
  have eb : batch0 = mk := by
    rcases harm with h | ⟨hn, -⟩
    · exact Option.some.inj (h.symm.trans hmk)
    · rw [hn] at hmk
      cases hmk
  subst eb
  obtain ⟨mk0, h0, hm⟩ := road_batch_some hmk
  obtain ⟨l'', p, k1, k2, k3, k4, rfl⟩ := k9_batch_some h0
  obtain rfl : l = l'' := Option.some.inj k2
  obtain ⟨f1, f2, f3⟩ := k9Where_fields k3
  refine ⟨Lk, p, e1, k3, k4, f1, f2, f3, fun g => ?_, n1, n2, n3, n4, n5, n8, n6, n7⟩
  obtain ⟨nm, enm⟩ := hm g
  have e : Lk.batch g = seatedAs ProofFile.sameReply
      (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p g) nm (a9Of l sub) := by
    rw [hbat g, enm]
    rfl
  have en : (Lk.batch g).name = nm := by rw [e]; rfl
  rw [en]
  exact e

end

/-! ## 5 The link's two tests, and the batching in the flat list -/

theorem findSome_only {α : Type u} {β : Type v} (f : α → Option β) (x : α) : ∀ l : List α,
    (∀ y ∈ l, f y = none ∨ y = x) → x ∈ l → l.findSome? f = f x
  | [], _, hx => by cases hx
  | y :: l, h, hx => by
    rw [List.findSome?_cons]
    rcases h y List.mem_cons_self with hy | rfl
    · rw [hy]
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hy]
        refine List.findSome?_eq_none_iff.2 fun z hz => ?_
        rcases h z (List.mem_cons_of_mem _ hz) with e | rfl
        · exact e
        · exact hy
      · exact findSome_only f x l (fun z hz => h z (List.mem_cons_of_mem _ hz)) hx
    · cases e : f y with
      | some b => rfl
      | none =>
        refine List.findSome?_eq_none_iff.2 fun z hz => ?_
        rcases h z (List.mem_cons_of_mem _ hz) with e' | rfl
        · exact e'
        · exact e

theorem quiet_all (Z : ProofFile.Pub) :
    ((ProofFile.pureSeat o Z).lots.filter fun L => !L.letters) = ProofFile.onlineFirstChainBlockTables Z := by
  refine List.filter_eq_self.2 fun L hL => ?_
  have hL' : L ∈ ProofFile.onlineFirstChainBlockTables Z := hL
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL'
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL'
  rcases hL' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl) <;> rfl

theorem k9_in_seat (Z : ProofFile.Pub) : ProofFile.k9Ninth Z ∈ ProofFile.onlineFirstChainBlockTables Z := by
  unfold ProofFile.onlineFirstChainBlockTables
  simp

theorem only_K9_each {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : ℕ} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z) :
    L.each G l = none ∨ L = ProofFile.k9Ninth Z := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  iterate 7 exact Or.inl rfl
  · exact Or.inr rfl
  iterate 7 exact Or.inl rfl

theorem only_K9_tests {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : ℕ} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z) :
    L.tests G l = none ∨ L = ProofFile.k9Ninth Z := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  iterate 7 exact Or.inl rfl
  · exact Or.inr rfl
  iterate 7 exact Or.inl rfl

/-- **Link.each at onlineDescription's seat is K9's files'**: eachAtS at testsWhere's first number; where testsWhere gives nothing: the test that always passes. -/
theorem road_each (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (l : ℕ) :
    (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road.each l =
      (match (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).map fun w =>
          VerifiableInference.Desc.K9.eachAtS w.1 with
        | some f => f
        | none => fun _ _ _ => .ok ()) := by
  simp only [ProofFile.partsAt]
  rw [quiet_all, findSome_only _ (ProofFile.k9Ninth Z) _ (fun L hL => only_K9_each hL) (k9_in_seat Z)]
  rfl

/-- **Link.tests at onlineDescription's seat is K9's files'** (ProofFile.k9Tests Z l); where k9Tests gives nothing: the test that always passes. -/
theorem road_tests (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (l : ℕ) :
    (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road.tests l =
      (match ProofFile.k9Tests Z l with
        | some f => f
        | none => fun _ => .ok ()) := by
  simp only [ProofFile.partsAt]
  rw [quiet_all, findSome_only _ (ProofFile.k9Ninth Z) _ (fun L hL => only_K9_tests hL) (k9_in_seat Z)]
  rfl

/-- By Block.lean's text: in a link's flat list, behind «laid» and the hearing blocks, stands the batching AT THE FRAME's OWN GATHERER. General in the link. -/
theorem batch_in_flat {σ C : Type} (Lk : Link σ C) :
    Lk.blocksInOrder[Lk.hear.length + 1]? =
      some (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) := by
  unfold Link.blocksInOrder
  refine getElem?_append_some (getElem?_append_some ?_ _) _
  have e : Lk.hear.length + 1 = (({ VerifiableInference.Desc.roundlessBlock (Lk.name ++ ": laid") Lk.chain
      (some Lk.number) 0 Lk.lay with
      planOk := VerifiableInference.Desc.orderOk Lk.hear Lk.order &&
        VerifiableInference.Desc.orderAfterOk Lk.hear Lk.orderAfter && Lk.close.all Block.hasNoClaimsAndNothingAfter &&
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)).hasNoClaimsAndNothingAfter } :
      Block σ C) :: Lk.hear).length + 0 := by
    rw [List.length_cons]
  rw [e, getElem?_append_add]
  rfl

/-! ## 6 In the goals' scope -/

/-- The sort of link number l, in scope. -/
def subAt (l : ℕ) : ModelPart := if l = 24 then .head else if l % 2 = 0 then .layers else .attention

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem subs_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : ∀ l < 25, (ProofFile.subsOf Z)[l]? = some (subAt l) := by
  intro l hl
  unfold subAt
  by_cases h24 : l = 24
  · subst h24
    exact subs_head hS hR O.pub O.blank
  · rw [if_neg h24]
    by_cases he : l % 2 = 0
    · rw [if_pos he]
      have h := subs_at hS hR O.pub O.blank (g := l / 2) (by omega)
      rwa [show 2 * (l / 2) = l by omega] at h
    · rw [if_neg he]
      have h := subs_att hS hR O.pub O.blank (g := l / 2) (by omega)
      rwa [show 2 * (l / 2) + 1 = l by omega] at h

theorem subAt_head : subAt 24 = .head := rfl
theorem subAt_layers (g : ℕ) (hg : g < 12) : subAt (2 * g) = .layers := by
  unfold subAt
  rw [if_neg (by omega), if_pos (by omega)]
theorem subAt_attention (g : ℕ) : subAt (2 * g + 1) = .attention := by
  unfold subAt
  rw [if_neg (by omega), if_neg (by omega)]

/-- K9's files' word for the sort of link number l, in scope. -/
def sortAt (l : ℕ) : VerifiableInference.Desc.K9.SegSort :=
  if l = 24 then .head else if l % 2 = 0 then .layers else .attention

/-- **In scope testsWhere returns at every link, with the sort of the order that is run.** -/
theorem testsWhere_scope {X : OnBytes.Model.Verify.Public} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf P.pol P.KL (some lay) = .ok X) :
    ∀ l < 25, ∃ w, VerifiableInference.Desc.K9.testsWhere X l 0 = some w ∧ w.1 = sortAt l := by
  intro l hl
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  have h24 := Meaning.scope_plans24 hS hR hX
  unfold VerifiableInference.Desc.K9.testsWhere sortAt
  rw [hq, hN]
  simp only [if_true]
  by_cases e24 : l = 24
  · subst e24
    exact ⟨_, rfl, rfl⟩
  · have c1 : (l == 2 * 12) = false := by simpa using e24
    rw [c1, if_neg e24]
    simp only [Bool.false_eq_true, if_false]
    by_cases he : l % 2 = 0
    · have c2 : (l % 2 == 0) = true := by simpa using he
      obtain ⟨⟨hp, ehp⟩, -⟩ := h24 (l / 2) (by omega)
      rw [c2, if_pos he, ehp]
      exact ⟨_, rfl, rfl⟩
    · have c2 : (l % 2 == 0) = false := by simpa using he
      obtain ⟨-, a, ea, -⟩ := h24 (l / 2) (by omega)
      rw [c2, if_neg he, ea]
      exact ⟨_, rfl, rfl⟩

/-- **onlineDescription's first chain has 25 links, in scope.** -/
theorem links_25 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : c.links.length = 25 := by
  have hc := O.chain
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        unfold firstChain at h1
        obtain ⟨c0, h0, rfl⟩ := Option.map_eq_some_iff.1 h1
        unfold firstChainWithoutReplyGuard at h0
        simp only [Option.bind_eq_bind, Option.pure_def] at h0
        split at h0
        · cases h0
        rename_i hok
        obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
        obtain ⟨ls, hls, h0⟩ := Option.bind_eq_some_iff.1 h0
        obtain ⟨back, _, h0⟩ := Option.bind_eq_some_iff.1 h0
        cases h0
        have hlen : ls.length = (ProofFile.subsOf Z).length := by
          have e := VerifiableInference.Desc.First.map_of_mapM _ (fun _ => ()) (fun _ => ())
            (fun _ _ _ => rfl) _ _ hls
          have e2 := congrArg List.length e
          simpa using e2
        have hok' : VerifiableInference.Desc.First.linksOk (ProofFile.subsOf Z) = true := by simpa using hok
        unfold VerifiableInference.Desc.First.linksOk at hok'
        rw [Bool.and_eq_true] at hok'
        have h24 := subs_head hS hR O.pub O.blank
        have hlt : 24 < (ProofFile.subsOf Z).length := (List.getElem?_eq_some_iff.1 h24).1
        show (ls.map _).length = 25
        rw [List.length_map, hlen]
        by_contra hne
        have hd : (ProofFile.subsOf Z).dropLast[24]? = some ModelPart.head := by
          rw [List.getElem?_dropLast, if_pos (by omega)]
          exact h24
        have hm := List.all_eq_true.1 hok'.2 _ (List.mem_of_getElem? hd)
        simp at hm

/-- **EVERY ONE OF THE 25 LINKS OF onlineDescription's FIRST CHAIN, IN SCOPE: ITS BATCHING IS K9's FILES' OWN AT THE FRAME's GATHERER AND STANDS AT A NAMED NUMBER OF THE FLAT LIST; ITS ORDERS ARE THE DRIVER's; ITS TWO TESTS ARE K9's
FILES', AT THE SORT OF THE ORDER THAT IS RUN** (testsWhere and k9Tests RETURN in scope: no test that always passes is laid). -/
theorem k9_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    c.links.length = 25 ∧
    ∀ l < 25, ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where)
        (w : VerifiableInference.Desc.K9.SegSort × ℕ × VerifiableInference.Desc.K9.TWhere)
        (T : S → Except String Unit), c.links[l]? = some Lk ∧
      k9At Z l = some p ∧ p.piece = (kindsBeforeBatching (subAt l) (l == 0)).length + 1 ∧ p.chain = 1 ∧
      p.link = l ∧ p.pieceEq = p.piece + 2 ∧
      (∀ g, LaidAlone ProofFile.sameReply (Lk.batch g)
        (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p g) (Lk.batch g).name
        (a9Of l (subAt l))) ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 2]? =
        some (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) ∧
      Lk.name = s!"link {l}" ∧ Lk.chain = 1 ∧ Lk.number = l ∧ Lk.order = orderOf (subAt l) ∧
      Lk.orderAfter = orderAfterOf (subAt l) ∧
      Lk.hear.length = (kindsBeforeBatching (subAt l) (l == 0)).length ∧
      VerifiableInference.Desc.K9.testsWhere Z.p.X l 0 = some w ∧ w.1 = sortAt l ∧
      Lk.each = VerifiableInference.Desc.K9.eachAtS w.1 ∧
      ProofFile.k9Tests Z l = some T ∧ Lk.tests = T := by
  refine ⟨links_25 hS hR O, fun l hl => ?_⟩
  obtain ⟨Lk, p, e1, e2, e3, f1, f2, f3, e4, n1, n2, n3, n4, n5, n6, n7, n8⟩ :=
    k9_alone O l (subAt l) (subs_scope hS hR O l hl)
  have hX := O.public
  rw [O.W] at hX
  obtain ⟨w, hw, hs⟩ := testsWhere_scope hS hR hX l hl
  have hT : ∃ T, ProofFile.k9Tests Z l = some T := by
    unfold ProofFile.k9Tests
    rw [hw]
    exact ⟨_, rfl⟩
  obtain ⟨T, hT⟩ := hT
  have hflat : c.blocksInOrder[14 * l + Lk.hear.length + 2]? =
      some (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) := by
    have h := link_at_flat e1 (batch_in_flat Lk)
    have e := flatIx_scope hS hR O (l := l) (by omega) Lk.hear.length
    unfold flatIx at e
    rw [show (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length +
        (Lk.hear.length + 1)) = 14 * l + Lk.hear.length + 2 by omega] at h
    exact h
  refine ⟨Lk, p, w, T, e1, e2, e3, f1, f2, f3, e4, hflat, n1, n2, n3, n4, n5, n6, hw, hs, ?_, hT, ?_⟩
  · rw [n7, road_each, hw]
    rfl
  · rw [n8, road_tests, hT]

end

end IM

#print axioms IM.road_each
#print axioms IM.road_tests
#print axioms IM.batch_in_flat
#print axioms IM.testsWhere_scope
#print axioms IM.links_25
#print axioms IM.k9_of
#print axioms IM.k9_alone
#print axioms IM.link_fields
#print axioms IM.stands_in_shape
#print axioms IM.one_at_place
#print axioms IM.block_by_place
#print axioms IM.shape_places
#print axioms IM.k10_in_flat
