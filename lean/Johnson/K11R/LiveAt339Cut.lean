-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/LiveAt339Cut.lean: NUMBER 339 OF THE FIRST CHAIN's FLAT LIST IS THE CODE SWITCH IN THE HEAD's DRESS, WITH «THE FIRST CHAIN's ROWS ARE THE WRITTEN ONES» (hc : PlanWritten.cutOf c.blocksInOrder = cutFirstFull) IN THE PLACE OF THE TEST standsHeadB (LiveAt339.lean): NO NEW PREMISE FOR THE MERGE's LAW, WHICH HAS hc IN FRONT ALREADY.
HOW. The dress goes by P1K2.standsOf of the place of the plan's list of which the lot's sub-protocol x is made; by IM.spot_head (Johnson/IMR/K2Seat.lean) that word goes by the head h of the place's name s!"{h}:{n}", n the piece. Under hc the SEATED sub-protocol b at 339 bears the name "H:2" (name339_full: by the kernel, on the written list). b.name is the name of a place sp of the plan's list at the address (IM.chain_hear_alone). THAT x BEARS THE SAME NAME: the lot lays a sub-protocol t for sp too (table_of_spot), of sp's name; t stands at the address: it stands at sp's place, or at the place of a place of the plan's list named "H:2", which stands in the written table (IM.stands_in_shape · shape_places · subs_all: a seat without a fault), where the places of the kind K2 are the address itself and places with the piece 1 (k2_places_full: by the kernel), and a name s!"{h}:{1}" is not "H:2"; and in a seat without a fault two sub-protocols at one place are one (IM.block_by_place): so t = x up to the type of claims, and x.name = "H:2".
  head_of_name2 · name1_ne       two lemmas on strings.
  k2_places_full · name339_full  two closed facts on written lists, by the kernel.
  table_of_spot                  the lot's table at a place of the plan's list.
  spot_at_339 · stands_of_name   a place named "H:2" of the kind K2 in the written table stands at the address; at the address it stands as the head's.
  live_at_339_cut                THE END: live_at_339's conclusion, to the letter, from scope · an opening's letters · F.planOk = true · hc.
LIMITS. At OnBytes.secondHashFunction alone. hc is a premise (a row of the entry tests' thirteen rows (GLOSSARY.md, "entry tests"); who pays it is not said here). That a step at 339 ACCEPTS at some state is not shown. No soundness. Nothing on hiding.
-/
import Johnson.K11R.LiveAt339
import Johnson.IMR.LinkSeat
import Johnson.IMR.PlacesScope
import Johnson.Desc.Ok.PlanWritten.CutTest
import Johnson.Desc.Ok.PlanWritten.CutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K11Live

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName blocksOk)
open VerifiableInference.Desc.First (S flatPlacesOf kindsBeforeBatching)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open IM (k2P under LaidAlone)
open ProofFile (Cl)

/-! ## Names -/

theorem head_of_name2 (h : String) (e : s!"{h}:{2}" = "H:2") : h = "H" := by
  have e2 : (h ++ ":" ++ toString 2).toList = ("H:2" : String).toList := congrArg String.toList e
  rw [String.toList_append, String.toList_append, IM.colon_list] at e2
  have e3 : h.toList ++ [':'] ++ ['2'] = ['H'] ++ [':'] ++ ['2'] := e2
  have e4 := List.append_cancel_right (List.append_cancel_right e3)
  exact String.toList_inj.1 e4

theorem name1_ne (h : String) : s!"{h}:{1}" ≠ "H:2" := by
  intro e
  have e2 := congrArg (fun s : String => s.toList.reverse.take 2) e
  dsimp only at e2
  have e3 : ['1', ':'] = ['2', ':'] := (IM.tail_one h _ '1' rfl).symm.trans e2
  simp at e3

/-! ## Closed facts on the written lists -/

set_option maxRecDepth 100000 in
theorem k2_places_full : ∀ sv : Bool, ((flatPlacesOf IM.linksW sv).all fun a =>
    !(a.kind == KindName.K2) || a == a339 || a.piece == 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem name339_full : (cutFirstFull[339]?).map (·.1) = some "H:2" := by decide +kernel

/-! ## The lot's table at a place of the plan's list -/

/-- **The sub-protocol that the code switch's lot lays for a place sp of the plan's list** bears sp's
name; it fails its test on the plan and stands at sp's place, or it stands at the place of a place
of the plan's list of sp's name. -/
theorem table_of_spot {Z : ProofFile.Pub} {G : ProofFile.Ground} {sp : ProofFile.Spot} (hsp : sp ∈ P1K2.purePlaces Z) :
    ∃ t ∈ P1K2.pureTable (fun _ _ => some none) Z G, t.name = sp.name ∧
      ((t.planOk = false ∧ t.place = sp.place) ∨
        ∃ sps sp2, ProofFile.spotsOf Z.cuts = some sps ∧ sp2 ∈ sps ∧ sp2.place.kind = KindName.K2 ∧
          sp2.name = sp.name ∧ t.place = sp2.place) := by
  unfold P1K2.pureTable
  refine ⟨_, List.mem_map_of_mem hsp, ?_⟩
  cases hy : (P1K2.pureSpots Z G).find? (fun x => x.1.name == sp.name) with
  | none => exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | some y =>
    dsimp only
    cases hpa : P1K2.pureAt (fun _ _ => some none) G y with
    | none => exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | some c =>
      show c.name = sp.name ∧ _
      have hny : y.1.name = sp.name := by simpa using List.find?_some hy
      have hm := List.mem_of_find?_eq_some hy
      unfold P1K2.pureSpots at hm
      cases hs : ProofFile.spotsOf Z.cuts with
      | none => rw [hs] at hm; cases hm
      | some sps =>
        rw [hs] at hm
        have hm' : y ∈ P1K2.p2All Z G sps := hm
        unfold P1K2.p2All at hm'
        split at hm'
        · cases hm'
        · obtain ⟨sp', hs', e⟩ := List.mem_filterMap.1 hm'
          obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 e
          obtain ⟨hs1, hs2⟩ := List.mem_filter.1 hs'
          have hk2 : sp'.place.kind = KindName.K2 := by simpa using hs2
          have hc : c.name = sp'.name ∧ c.place = sp'.place := by
            unfold P1K2.pureAt at hpa
            dsimp only at hpa
            split at hpa
            · obtain rfl := Option.some.inj hpa
              exact ⟨rfl, rfl⟩
            · obtain ⟨HP, _, rfl⟩ := Option.map_eq_some_iff.1 hpa
              exact ⟨rfl, rfl⟩
            · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hpa
              obtain ⟨l, _, ho⟩ := Option.bind_eq_some_iff.1 ho
              obtain rfl : none = o := Option.some.inj ho
              exact ⟨rfl, rfl⟩
          exact ⟨hc.1.trans hny, Or.inr ⟨sps, sp', rfl, hs1, hk2, hny, hc.2⟩⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- A place of the plan's list of the kind K2 that bears the name "H:2" and stands at a place of the
written table stands at the code switch's address in the output head's link. -/
theorem spot_at_339 {sps : List ProofFile.Spot} (hs : ProofFile.spotsOf Z.cuts = some sps) {sp : ProofFile.Spot}
    (hsp : sp ∈ sps) (hk : sp.place.kind = KindName.K2) (hn : sp.name = "H:2") {sv : Bool}
    (hm : sp.place ∈ flatPlacesOf IM.linksW sv) : sp.place = a339 := by
  have h1 := List.all_eq_true.1 (k2_places_full sv) sp.place hm
  rw [hk] at h1
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exfalso
    unfold ProofFile.spotsOf at hs
    obtain ⟨h, n, ⟨en, epc, -, -⟩ | ⟨h9, -⟩⟩ := IM.spot_head _ _ _ _ _ hs sp hsp
    · rw [hk] at epc
      have e1 : n = 1 := by
        rw [h1] at epc
        simpa using epc.symm
      subst e1
      exact name1_ne h (en.symm.trans hn)
    · rw [hk] at h9
      cases h9

/-- A place of the plan's list at that address that bears the name "H:2" stands as the head's. -/
theorem stands_of_name {sps : List ProofFile.Spot} (hs : ProofFile.spotsOf Z.cuts = some sps) {sp : ProofFile.Spot}
    (hsp : sp ∈ sps) (hp : sp.place = a339) (hn : sp.name = "H:2") :
    P1K2.standsOf sp = At.head := by
  unfold ProofFile.spotsOf at hs
  obtain ⟨h, n, ⟨en, epc, -, est⟩ | ⟨h9, -⟩⟩ := IM.spot_head _ _ _ _ _ hs sp hsp
  · rw [hp] at epc
    have e2 : n = 2 := by simpa using epc.symm
    subst e2
    obtain rfl : h = "H" := head_of_name2 h (en.symm.trans hn)
    rw [est]
    rfl
  · rw [hp] at h9
    cases h9

/-- **NUMBER 339 OF THE FIRST CHAIN's FLAT LIST IS THE CODE SWITCH IN THE HEAD's DRESS, WHERE THE
FIRST CHAIN's ROWS ARE THE WRITTEN ONES.** -/
theorem live_at_339_cut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hc : cutOf c.blocksInOrder = cutFirstFull) :
    ∃ (b : Block S Cl) (x : Block S Unit) (Pr : P1K2.Prep) (n : P1K2.Nums)
        (HP : VerifiableInference.Desc.First.K2.HeadPar),
      c.blocksInOrder[339]? = some b ∧ LaidAlone ProofFile.sameReply b x.retype b.name a339 ∧
      P1K2.prepOf Z Bs.G₀ = some Pr ∧ P1K2.numsAt Pr (some 24) = some n ∧
      P1K2.pureLetters Bs.G₀ 24 = some HP ∧
      x = under x.name a339 ((codeSwitchKind (k2P Z a339 x.name .head n) : Block S Unit).andThen x.name
        (headOpened x.name a339 HP)) := by
  have hd := O.desc
  subst hd
  obtain ⟨hspots, hshape, -, hall⟩ := IM.base_made O.made
  have hk : (kindsBeforeBatching .head (24 == 0))[1]? = some KindName.K2 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, sp, hsp, L, hL, b', hb', es, ep, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain 24 .head (IM.subs_head hS hR O.pub O.blank) 1 .K2 hk
      (by decide) (by decide) (by decide)
  obtain rfl : L = ProofFile.k2Pure Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [ep])
  have hxa : x.place = a339 := ep
  have e339 : c.blocksInOrder[339]? = some b := by
    have h := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O (Nat.le_refl 24) 1] at h
  -- the seated sub-protocol's name, off the written rows
  have hbn : b.name = "H:2" := by
    have h1 : ((cutOf c.blocksInOrder)[339]?).map (·.1) = some b.name := by
      unfold cutOf
      rw [List.getElem?_map, e339]
      rfl
    rw [hc, name339_full] at h1
    exact (Option.some.inj h1).symm
  have hspn : sp.name = "H:2" := (IM.alone_name hla).symm.trans hbn
  -- its test on the plan
  have hb : blocksOk c.blocksInOrder = true := by
    cases hb : blocksOk (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
        (ProofFile.startS Z) c).first.blocksInOrder with
    | true => exact hb
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at hOk
  have hbp : b.planOk = true := by
    have h1 := List.all_eq_true.1 hb b (List.mem_of_getElem? e339)
    simp only [Bool.and_eq_true] at h1
    exact h1.1
  have hxp : x.planOk = true := by
    rw [IM.alone_planOk hla] at hbp
    exact (IM.retype_planOk x hbp).1
  -- the lot's sub-protocol for the plan's place sp
  have hspP : sp ∈ P1K2.purePlaces Z := by
    unfold P1K2.purePlaces
    rw [hspots]
    exact List.mem_filter.2 ⟨hsp, by rw [es]; rfl⟩
  obtain ⟨t, ht, htn, harm⟩ := table_of_spot (G := Bs.G₀) hspP
  have htb : (t.retype : Block S Cl) ∈ (ProofFile.k2Pure Z).blocks Bs.G₀ := by
    unfold ProofFile.Lot.blocks ProofFile.asCl
    exact List.mem_append_left _ (List.mem_map_of_mem ht)
  have hkt : t.place.kind = KindName.K2 := IM.kind_K2 Z Bs.G₀ _ htb
  have htp : t.place = a339 := by
    rcases harm with ⟨_, hp⟩ | ⟨sps, sp2, hs2, hsp2, hk2, hn2, hp⟩
    · rw [hp, es]
    · have hmem : (t.retype : Block S Cl) ∈ Bs.all.flatMap fun y => y.2 := by
        rw [hall]
        exact List.mem_flatMap.2 ⟨(ProofFile.k2Pure Z, (ProofFile.k2Pure Z).blocks Bs.G₀),
          List.mem_map.2 ⟨ProofFile.k2Pure Z, hL, rfl⟩, htb⟩
      obtain ⟨e, he, ee⟩ := IM.stands_in_shape O.sound hmem (by
        show t.place.kind ≠ KindName.frame
        rw [hkt]
        decide)
      obtain ⟨sv, hsv⟩ := IM.shape_places hshape
      rw [IM.subs_all hS hR O] at hsv
      have hm : sp2.place ∈ flatPlacesOf IM.linksW sv := by
        rw [← hsv, ← hp]
        exact List.mem_map.2 ⟨e, he, ee⟩
      rw [hp]
      exact spot_at_339 hs2 hsp2 hk2 (hn2.trans hspn) hm
  have hxt : (t.retype : Block S Cl) = x.retype :=
    IM.block_by_place O.sound hall hL hL htb hb' (by
      show t.place.kind ≠ KindName.frame
      rw [hkt]
      decide) (htp.trans hxa.symm)
  have hxn : x.name = "H:2" := by
    have h1 : (t.retype : Block S Cl).name = (x.retype : Block S Cl).name :=
      congrArg (fun y : Block S Cl => y.name) hxt
    have h2 : t.name = x.name := h1
    rw [← h2, htn, hspn]
  -- so the place of which x is made stands as the head's
  obtain ⟨sps, sp', hs, hsp', en, ep', Pr, n, hP, hn, harm'⟩ := k2_mem_spot hx hxp
  have hh : P1K2.standsOf sp' = At.head :=
    stands_of_name hs hsp' (ep'.symm.trans hxa) (en.symm.trans hxn)
  rw [← ep', hxa] at hn
  rw [← ep', ← en, hxa] at harm'
  have hla' : LaidAlone ProofFile.sameReply b x.retype b.name a339 := by
    rw [IM.alone_name hla]
    exact hla
  rcases harm' with ⟨h0, _⟩ | ⟨_, l, HP, hl, hHP, ex⟩ | ⟨h0, _⟩
  · rw [hh] at h0
    cases h0
  · obtain rfl : 24 = l := Option.some.inj hl
    exact ⟨b, x, Pr, n, HP, e339, hla', hP, hn, hHP, ex⟩
  · rw [hh] at h0
    cases h0

end

end K11Live

#print axioms K11Live.head_of_name2
#print axioms K11Live.name1_ne
#print axioms K11Live.k2_places_full
#print axioms K11Live.name339_full
#print axioms K11Live.table_of_spot
#print axioms K11Live.spot_at_339
#print axioms K11Live.stands_of_name
#print axioms K11Live.live_at_339_cut
