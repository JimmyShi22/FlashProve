-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/SeatCoreFits.lean: THE IOP OF THE LOTS' SUB-PROTOCOLS
ALONE (ProofFile.onlineDescriptionFromPublicPart), GENERAL IN THE SEAT: every sub-protocol of the first chain's flat list that
passes its own test on the list of rounds keeps R at rounds that fit, where the lots' do.
  LotsKeepF HAS THREE FIELDS WHERE LotsKeep HAS TWO: blocks (inside a link: WholeF) · frames (of the
  kind "frame": Whole, AT ANY ROUNDS: the harness runs these at no round at all, as plain functions)
  · batch.
  guardMark_decidesF | _wholeF · retype_wholeF · fill_keepsF · chainBy_frontF | _backF ·
  partsAt_roadWF | _framesF | _baseF | _baseAllF · LotsAllF · pureZ_flatF   carried
CARRIED BY PROGRAM out of Johnson/IMR/KeepsSeat.lean:
each declaration that is needed for the top and names Decides | Whole is copied under its own name
with a letter behind it (F | W), with Fits | WholeF in that word's place; its docstrings are struck
(they are that file's); where a proof opens the word itself it is turned by hand. THE ORIGINAL IS
IMPORTED AND NOT TURNED: what names neither word is called from it. IF THE ORIGINAL ITSELF IS
WIDENED INSTEAD, THIS FILE FALLS.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.IMR.KeepsSeat
import Johnson.Desc.Tidy.Fits
import Johnson.Desc.AtSeats.Fit.FoldFits
import Johnson.Desc.AtSeats.Fit.DriverFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S firstChain)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Keeps (WholeF Fits LinkKeepsF wholeF_of_whole fits_of_decides
    andThen_wholeF whole_sameF fits_planOk)
open ProofFile (guardMark fill chainC chainBy Frames Gather FrameRole Lot Ground)

variable {R : S → S → Prop}

theorem guardMark_decidesF {b : Block S ProofFile.Cl} (W : Fits R b) : Fits R (guardMark b) :=
  fun hp s rs gs s' hf h => by
  obtain ⟨t, e, h⟩ := Keeps.ebind_ok (x := b.decide s (rs.map noDigest) gs) h
  split at h
  · cases h
    exact W hp s rs gs _ hf e
  · cases h

theorem guardMark_wholeF {b : Block S ProofFile.Cl} (W : WholeF R b) : WholeF R (guardMark b) :=
  ⟨guardMark_decidesF W.1, W.2.1, W.2.2⟩

theorem retype_wholeF {T Cl Cl' : Type} {Q : T → T → Prop} {b : Block T Cl} (W : WholeF Q b) :
    WholeF Q (b.retype : Block T Cl') :=
  ⟨fun hp => W.1 ((Bool.and_eq_true _ _ ▸ hp).1), (fun _ hc => nomatch hc), W.2.2⟩

variable {Cl : Type}

theorem fill_keepsF {bs : List (Block S Cl)} {z : Block S Cl} {fr : Frames S Cl}
    (hb : ∀ b ∈ bs, b.place.link ≠ none → WholeF R b)
    (hbat : ∀ a mk, fr.batch a = some mk → ∀ f, FnCl R f → Fits R (mk f))
    (hl : ∀ l, Fn R (fr.lay l)) (hc : ∀ l, Fn R (fr.clear l)) (hf : Fits R fr.first) :
    BlocksKeepF R (fill bs z fr) where
  block a b ha h := by
    have h' : (bs.find? fun b => b.place == a) = some b := h
    have hp : (b.place == a) = true :=
      List.find?_some (p := fun x : Block S Cl => x.place == a) h'
    have e : b.place = a := eq_of_beq hp
    exact hb b (List.mem_of_find?_eq_some h') (e ▸ ha)
  batch a mk ha h f hf' := by
    have h' : (fr.batch a <|> (bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h
    cases hq : fr.batch a with
    | some m =>
      rw [hq] at h'
      have e : some m = some mk := h'
      cases e
      exact hbat a _ hq f hf'
    | none =>
      rw [hq] at h'
      have h'' : ((bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h'
      obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1 h''
      have hp : (b.place == a) = true :=
        List.find?_some (p := fun x : Block S Cl => x.place == a) hb'
      have e : b.place = a := eq_of_beq hp
      exact (hb b (List.mem_of_find?_eq_some hb') (e ▸ ha)).1
  lay := hl
  clear := hc
  first := hf

theorem chainBy_frontF (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) {Z : ProofFile.Pub}
    {base : List (Block S ProofFile.Cl)} {fr : List (FrameRole × Block S ProofFile.Cl)}
    {road : Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl} (h : chainBy Z base fr road = .ok c)
    (hb : ∀ b ∈ base, b.place.link ≠ none → WholeF R b) (hfr : ∀ x ∈ fr, Whole R x.2)
    (hbat : ∀ a mk, road.batch a = some mk → ∀ f, FnCl R f → Fits R (mk f)) :
    ∀ b ∈ frontOf c, Fits R b := by
  unfold chainBy at h
  obtain ⟨z, several, hc⟩ := chainC_first h
  refine firstChain_frontF hr ht (fill_keepsF ?_ hbat ?_ ?_ ?_) hc
  · intro b hb' hl
    obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hb')
    split
    · rename_i x hx
      simp only [hx] at hl
      exact Keeps.andThen_wholeF R ht _ _ _ (hb b₀ h₀ hl)
        (Keeps.wholeF_of_whole (guarded_whole _ _ (hfr x (List.mem_of_find?_eq_some hx))))
    · rename_i hx
      simp only [hx] at hl
      exact hb b₀ h₀ hl
  · intro l t s' k
    dsimp only at k
    split at k
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hfr x (List.mem_of_find?_eq_some hx)).1 _ _ _ _ k
    · cases k
      exact hr _
  · intro l t s' k
    dsimp only at k
    split at k
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact (hfr x (List.mem_of_find?_eq_some hx)).1 _ _ _ _ k
    · cases k
      exact hr _
  · dsimp only
    split
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      exact Keeps.fits_of_decides (hfr x (List.mem_of_find?_eq_some hx)).1
    · exact fun _ s _ _ s' _ k => by cases k; exact hr _

theorem chainBy_backF (ht : ∀ a b c, R a b → R b c → R a c) {Z : ProofFile.Pub}
    {base : List (Block S ProofFile.Cl)} {fr : List (FrameRole × Block S ProofFile.Cl)}
    {road : Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl} (h : chainBy Z base fr road = .ok c)
    (hb : ∀ b ∈ base, b.planOk = true → WholeF R b) (hfr : ∀ x ∈ fr, Whole R x.2) :
    ∀ b ∈ backOf c, b.planOk = true → Fits R b := by
  unfold chainBy at h
  obtain ⟨z, several, hz, hc⟩ := chainC_last h
  refine firstChain_backF (fun a b _ e => ?_) ?_ hc
  · have e' := List.mem_of_find?_eq_some e
    obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_of_mem_dropLast e')
    split
    · rename_i x hx
      intro hp
      exact (Keeps.andThen_wholeF R ht _ _ _ (hb b₀ h₀ (Bool.and_eq_true _ _ ▸ hp).1)
        (Keeps.wholeF_of_whole (guarded_whole _ _ (hfr x (List.mem_of_find?_eq_some hx))))).1
    · exact fun hp => (hb b₀ h₀ hp).1
  · obtain ⟨b₀, h₀, e₀⟩ := List.mem_map.1 (List.mem_of_getLast? hz)
    show z.planOk = true → Fits R z
    rw [← e₀]
    split
    · rename_i x hx
      intro hp
      exact (Keeps.andThen_wholeF R ht _ _ _ (hb b₀ h₀ (Bool.and_eq_true _ _ ▸ hp).1)
        (Keeps.wholeF_of_whole (guarded_whole _ _ (hfr x (List.mem_of_find?_eq_some hx))))).1
    · exact fun hp => (hb b₀ h₀ hp).1

structure LotsKeepF (R : S → S → Prop) (lots : List Lot) (G : Ground) : Prop where
  blocks : ∀ L ∈ lots, ∀ b ∈ L.blocks G, b.place.link ≠ none → WholeF R b
  frames : ∀ L ∈ lots, ∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → Whole R b
  batch : ∀ L ∈ lots, ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f)

variable {T : ProofFile.PureSeat} {B : ProofFile.PureBase}

theorem partsAt_roadWF (K : LotsKeepF R T.lots B.G₀) {a : Place}
    {mk : (S → Except String (List ProofFile.Cl × S)) → Block S ProofFile.Cl}
    (h : (ProofFile.partsAt T B).road.batch a = some mk) :
    ∀ f, FnCl R f → WholeF R (mk f) := by
  intro f hf
  simp only [ProofFile.partsAt] at h
  obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some h₀
  exact guardMark_wholeF (K.batch L (List.mem_of_mem_filter hL) a mk₀ e f hf)

theorem partsAt_framesF (K : LotsKeepF R T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) :
    ∀ x ∈ (ProofFile.partsAt T B).frames, Whole R x.2 := by
  intro x hx
  simp only [ProofFile.partsAt] at hx
  obtain ⟨y, hy, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · cases hx
  · obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hx
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
    obtain ⟨k1, k2⟩ := hall y hy
    have W : Whole R b := K.frames y.1 k1 b (k2 ▸ hb1) hb2
    split at e
    · cases e
    · cases e
    · cases e
      exact guardMark_whole W

theorem partsAt_baseF (hr : ∀ s, R s s) (K : LotsKeepF R T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) {base : List (Block S ProofFile.Cl)}
    (h : (ProofFile.partsAt T B).base = .ok base) : ∀ b ∈ base, b.place.link ≠ none → WholeF R b := by
  intro b hb hl
  unfold ProofFile.PureParts.base at h
  obtain ⟨x, hx, e⟩ := mem_of_mapM_ok _ _ _ h b hb
  simp only [ProofFile.partsAt] at hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  dsimp only at e
  split at e
  · rename_i _ _ f hface
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hface
    obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hmk
    obtain ⟨L, hL, eL⟩ := List.exists_of_findSome?_eq_some h₀
    cases e
    exact guardMark_wholeF (K.batch L (List.mem_of_mem_filter hL) _ mk₀ eL _
      (fun s y k => by cases k; exact hr s))
  · rename_i _ _ y _ hs
    obtain ⟨z, hz, ez⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hs)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 ez
    obtain ⟨k1, k2⟩ := hall z hz
    cases e
    exact guardMark_wholeF (K.blocks z.1 k1 b₀ (k2 ▸ List.mem_of_find?_eq_some hb₀) hl)
  · split at e <;> cases e

structure LotsAllF (R : S → S → Prop) (lots : List Lot) (G : Ground) : Prop where
  blocks : ∀ L ∈ lots, ∀ b ∈ L.blocks G, b.planOk = true → WholeF R b
  batch : ∀ L ∈ lots, ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f)

theorem partsAt_baseAllF (hr : ∀ s, R s s) (K : LotsAllF R T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) {base : List (Block S ProofFile.Cl)}
    (h : (ProofFile.partsAt T B).base = .ok base) : ∀ b ∈ base, b.planOk = true → WholeF R b := by
  intro b hb hp
  unfold ProofFile.PureParts.base at h
  obtain ⟨x, hx, e⟩ := mem_of_mapM_ok _ _ _ h b hb
  simp only [ProofFile.partsAt] at hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  dsimp only at e
  split at e
  · rename_i _ _ f hface
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hface
    obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hmk
    obtain ⟨L, hL, eL⟩ := List.exists_of_findSome?_eq_some h₀
    cases e
    exact guardMark_wholeF (K.batch L (List.mem_of_mem_filter hL) _ mk₀ eL _
      (fun s y k => by cases k; exact hr s))
  · rename_i _ _ y _ hs
    obtain ⟨z, hz, ez⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hs)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 ez
    obtain ⟨k1, k2⟩ := hall z hz
    cases e
    exact guardMark_wholeF (K.blocks z.1 k1 b₀ (k2 ▸ List.mem_of_find?_eq_some hb₀) hp)
  · split at e <;> cases e

theorem pureZ_flatF (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) {Z : ProofFile.Pub}
    (K : ∀ G, LotsKeepF R T.lots G) (Ka : ∀ G, LotsAllF R T.lots G) {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy T.older T.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Fits R b := by
  obtain ⟨B, base, c, A, B', hB, -, -, hbase, hc, -, -, e⟩ := IM.pure_chain h
  have hall := all_of_made (IM.base_made hB).2.2.2
  have hF := partsAt_framesF (K _) hall
  refine ⟨A, B', c, e, fun b hb hp => ?_⟩
  rw [flat_eq (chainBy_noFront hc)] at hb
  rcases List.mem_append.1 hb with k | k
  · exact chainBy_frontF hr ht hc (partsAt_baseF hr (K _) hall hbase) hF
      (fun a mk e f hf => (partsAt_roadWF (K _) e f hf).1) b k
  · exact chainBy_backF ht hc (partsAt_baseAllF hr (Ka _) hall hbase) hF b k hp

end Meaning.K2
