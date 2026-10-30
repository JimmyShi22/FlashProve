-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05PublicOfBuilt.lean: kind K5: THREE OF THE SIX PUBLIC BOOLS THAT THE TIE
BETWEEN THE LAW's WORLD AND THE TABLE OF JOINTS' ASKS (tiePublicB,
Johnson/Desc/First/Att/K05TiePublic.lean; u3PublicB, Johnson/Desc/First/Att/K05BehindWorth.lean) ARE
LAWS OF A TEXT THAT THE VERIFIER RUNS: a return of buildLinksH (OnBytes/Model/StagesLinks.lean: the
public tests on the links of a request's chain, on the first chain's parameters as read back) gives
them.

Why. An evaluated Bool is a premise until a text that the verifier runs asks it, or a law gives it.
Both planners end in buildLinksH: Verify.planned (OnBytes/Model/Verify.lean, through builtOf, at
linksOf X default) and the description's own copy ProofFile.Plain.planned
(Johnson/Desc/ProofFile/PlanPlain.lean, at linksPlain X). So the laws are
stated at buildLinksH's return, GENERAL IN THE LINKS links0 THAT IT IS HANDED.

IS IT EMPTY HERE? buildLinksH returns at the library's two written policy texts (an evaluation:
Verify.planned returned there); no member is shown in this file.

Main names:
  `sentOfBuilt p B`: D: codes, shape and layout of the first chain's parameters p; link by link the
    built links' arrayOf.
  `buildLinks_cut`: a run, cut: the yes of declareLinks, heldAgainst, reqOk, linksFit and
    numbersHeld. (The library's Fo.built_cut, OnBytes/Tie/Pv/Lookup/Ends/FoBuiltCut.lean, cuts
    builtOf and drops linksFit's yes.)
  `layout_of_built`: **reqLayoutOk p.codes p.shape p.layout = true** (linksFit's first line).
  `messages_held`: every message of every link passes messageHeld. `links_laid`: every built link
    passes linkLaid, under the shape's mask code. `forIn_each`, `shapes_own`, `messages_of_built`:
    tools.
  `oneMask_of_built`: **oneMaskB (sentOfBuilt p B) i = true at every i.**
  `masks_of_built`: **masksUpTo (sentOfBuilt p B) x x.ns = true** at a place x with x.link = l and
    x.ns = Y.ns, Y the link number l that was handed in: linkLaid (the scalars and the answers' pads
    have room in the mask row) · reqShapeOk (the message's mask code is the shape's) · reqLinkOk
    (the first message is of moment 0) · messageHeld (it holds the one mask row).
NOT HERE: symArraysB and u3PublicB (they want an invariant of declareOwn, foreign and declareLinks)
· Codes.lengthsOk: buildLinksH does not ask it: the run does, and the chain's start.
Limits. That the verifier under proof takes its public part from such a return at the proof's own
three files is not traced here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05TiePublic
import OnBytes.Tie.Pv.Lookup.Ends.FoBuiltCut
import OnBytes.Tie.Pv.Keeps.LinksBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Params OnBytes.Plan
open VerifiableInference.Desc.First.Look (Sent sigListCalls sigList keptAt messagesAt)

/-- D, off the first chain's parameters and the built links. -/
def sentOfBuilt (p : Params.First) (B : LinksH) : Sent :=
  { codes := p.codes, shape := p.shape, layout := p.layout, arrayOf := B.links.map (·.arrayOf) }

/-- A loop over a list that carries nothing and never breaks off: every step has returned. -/
theorem forIn_each {α : Type} (f : α → PUnit.{1} → Except String (ForInStep PUnit.{1}))
    (hy : ∀ a s, f a PUnit.unit = .ok s → s = .yield PUnit.unit) :
    ∀ (l : List α) (r : PUnit.{1}), forIn l PUnit.unit f = .ok r →
      ∀ a ∈ l, f a PUnit.unit = .ok (.yield PUnit.unit)
  | [], _, _, _, ha => by cases ha
  | b :: l, r, h, a, ha => by
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, h⟩ := exc_bind h
    obtain rfl := hy b s hs
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hs
    · exact forIn_each f hy l r h a ha

/-- The caller's list behind the kept messages is the link's own messages of moment 0. -/
theorem shapes_own {D : Sent} {i k : ℕ} {o : OracleShape}
    (h : (shapesCalls D i)[(keptAt D i).length + k]? = some o) :
    ∃ msg, (messagesAt D i)[k]? = some msg ∧ o = msg.shape := by
  unfold shapesCalls sigListCalls sigList at h
  rw [List.map_append, List.getElem?_append_right (by simp)] at h
  simp only [List.length_map, Nat.add_sub_cancel_left, List.map_map, List.getElem?_map] at h
  obtain ⟨msg, hm, e⟩ := Option.map_eq_some_iff.1 h
  exact ⟨msg, takeWhile_get _ _ _ _ hm, e.symm⟩

section
variable {links0 : Array LinkH} {NGr : ℕ} {p4 : Bool} {wsLay : WsLay} {p : Params.First} {B : LinksH}

/-- A run of buildLinksH, cut: five of its tests' yes. -/
theorem buildLinks_cut (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∃ declared, declareLinks links0 NGr p4 = .ok (B.links, declared) ∧
      heldAgainst declared p = .ok () ∧ reqOk p.codes p.shape = true ∧
      linksFit B.links p.codes p.shape p.layout p.lin.kCol = .ok () ∧
      numbersHeld B.links p = .ok () := by
  unfold buildLinksH at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨named, declared⟩, h3, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨⟨⟩, h4, h⟩ := exc_bind h
  obtain ⟨⟨⟩, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟩, _, h⟩ := exc_bind h
  have h8 := exc_guard_not h
  replace h := exc_guard h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟩, h10, h⟩ := exc_bind h
  obtain ⟨⟨⟩, h11, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  exact ⟨declared, h3, h4, by simpa using h8, h10, h11⟩

/-- **T1: the layout is lawful.** -/
theorem layout_of_built (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    reqLayoutOk p.codes p.shape p.layout = true := by
  obtain ⟨_, _, _, _, h10, _⟩ := buildLinks_cut h
  unfold linksFit at h10
  have := exc_guard_not h10
  simpa using this

/-- Every message of every link passes messageHeld. -/
theorem messages_held (h : buildLinksH links0 NGr p4 wsLay p = .ok B) {i : ℕ} {L : ReqLink}
    (hL : p.shape.link[i]? = some L) {k : ℕ} {m : ReqMessage} (hm : L.messages[k]? = some m) :
    ∃ n, messageHeld (k == 0) n m = true := by
  obtain ⟨declared, _, h4, _, _, _⟩ := buildLinks_cut h
  obtain ⟨e1, e2, e3⟩ := Fo.heldAgainst_cut h4
  have hi : i < p.shape.link.length := (List.getElem?_eq_some_iff.1 hL).1
  obtain ⟨Dl, hD⟩ : ∃ d, declared[i]? = some d :=
    ⟨_, Array.getElem?_eq_getElem (by rw [e1]; exact hi)⟩
  obtain ⟨Al, hA⟩ : ∃ d, p.layout.link[i]? = some d :=
    ⟨_, List.getElem?_eq_getElem (by rw [← e2, e1]; exact hi)⟩
  have hh := e3 i Dl L Al hD hL hA
  unfold linkHeld at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨_, h2⟩, _⟩, _⟩, _⟩ := hh
  exact ⟨_, List.all_eq_true.1 h2 (m, k) (List.mem_zipIdx_iff_getElem?.2 hm)⟩

/-- The messages of a link of D are the shape's. -/
theorem messages_of_built {i k : ℕ} {m : ReqMessage}
    (hm : (messagesAt (sentOfBuilt p B) i)[k]? = some m) :
    ∃ L, p.shape.link[i]? = some L ∧ L.messages[k]? = some m := by
  unfold messagesAt at hm
  cases hL : (sentOfBuilt p B).shape.link[i]? with
  | none =>
    rw [hL] at hm
    simp at hm
  | some L =>
    rw [hL] at hm
    exact ⟨L, hL, hm⟩

/-- **T2: the member that holds a link's mask row has one mask row.** -/
theorem oneMask_of_built (h : buildLinksH links0 NGr p4 wsLay p = .ok B) (i : ℕ) :
    oneMaskB (sentOfBuilt p B) i = true := by
  unfold oneMaskB maskMsg
  cases hf : (messagesAt (sentOfBuilt p B) i).findIdx? (fun y => y.shape.maskRows != 0) with
  | none => rfl
  | some mi =>
    show ((shapesCalls (sentOfBuilt p B) i)[(keptAt (sentOfBuilt p B) i).length + mi]?).all
      (fun o => o.maskRows == 1) = true
    cases ho : (shapesCalls (sentOfBuilt p B) i)[(keptAt (sentOfBuilt p B) i).length + mi]? with
    | none => rfl
    | some o =>
      show (o.maskRows == 1) = true
      obtain ⟨msg, hm, rfl⟩ := shapes_own ho
      obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
      have e : (messagesAt (sentOfBuilt p B) i)[mi] = msg :=
        Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hm)
      rw [e] at hp
      obtain ⟨L, hL, hm'⟩ := messages_of_built hm
      obtain ⟨n, hh⟩ := messages_held h hL hm'
      unfold messageHeld at hh
      simp only [Bool.and_eq_true, beq_iff_eq] at hh
      obtain ⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, _⟩, _⟩, _⟩ := hh
      by_cases h0 : mi = 0
      · rw [if_pos h0] at h3
        simpa using h3
      · rw [if_neg h0] at h3
        rw [h3] at hp
        simp at hp

/-- linkLaid's yes at every built link, under the shape's mask code. -/
theorem links_laid (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∃ zk, p.codes.mask[p.shape.maskCode]? = some zk ∧
      ∀ (l : ℕ) (X : LinkH), B.links[l]? = some X →
        linkLaid p.shape p.layout zk.ell l X = .ok () := by
  obtain ⟨_, _, _, _, h10, _⟩ := buildLinks_cut h
  unfold linksFit at h10
  replace h10 := exc_guard h10
  obtain ⟨⟨⟩, _, h10⟩ := exc_bind h10
  unfold linksLaid at h10
  cases hz : p.codes.mask[p.shape.maskCode]? with
  | none =>
    rw [hz] at h10
    cases h10
  | some zk =>
    rw [hz] at h10
    refine ⟨zk, rfl, fun l X hX => ?_⟩
    dsimp only at h10
    obtain ⟨r, h11, _⟩ := exc_bind h10
    have hstep := forIn_each _ (fun a s hs => by
      obtain ⟨X', l'⟩ := a
      obtain ⟨_, _, k⟩ := exc_bind hs
      exact (Except.ok.inj k).symm) _ r h11 (X, l)
      (List.mem_zipIdx_iff_getElem?.2 (by rw [Array.getElem?_toList]; exact hX))
    obtain ⟨⟨⟩, k1, _⟩ := exc_bind hstep
    exact k1

/-- **T3: every mask entry below the link's number of scalars has a seat.** -/
theorem masks_of_built (h : buildLinksH links0 NGr p4 wsLay p = .ok B) {l : ℕ} {Y : LinkH}
    (hY : links0[l]? = some Y) {x : VerifiableInference.Desc.First.Look.Place} (hx : x.link = l)
    (hns : x.ns = Y.ns) : masksUpTo (sentOfBuilt p B) x x.ns = true := by
  obtain ⟨declared, h3, _, h8, _, h11⟩ := buildLinks_cut h
  obtain ⟨a1, a2⟩ := OnBytes.L5.LinksOrder.declareLinks_at links0 NGr p4 B.links declared h3
  obtain ⟨ar, hX⟩ := a2 l Y hY
  obtain ⟨zk, hzk, hlaid⟩ := links_laid h
  have hl1 := hlaid l _ hX
  -- the scalars have room
  have hroom : Y.ns ≤ zk.ell := by
    unfold linkLaid at hl1
    have := exc_guard_not hl1
    simp only at this
    omega
  -- the link of the shape
  have hlen : l < p.shape.link.length := by
    have e := congrArg List.length (Fo.numbersHeld_cut h11).1
    simp only [List.length_map, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil] at e
    have hl : l < links0.size := (Array.getElem?_eq_some_iff.1 hY).1
    omega
  obtain ⟨L, hL⟩ : ∃ L, p.shape.link[l]? = some L := ⟨_, List.getElem?_eq_getElem hlen⟩
  -- what the shape's own test says of it
  have hs : reqShapeOk p.shape = true := by
    unfold reqOk at h8
    exact (Eq.mp (Bool.and_eq_true _ _) h8).1
  unfold reqShapeOk at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hall⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hs
  have hLl := List.all_eq_true.1 hall (L, l) (List.mem_zipIdx_iff_getElem?.2 hL)
  simp only [Bool.and_eq_true] at hLl
  obtain ⟨hlk, hms⟩ := hLl
  unfold reqLinkOk at hlk
  simp only [Bool.and_eq_true] at hlk
  obtain ⟨⟨hhead, _⟩, _⟩ := hlk
  cases hmsgs : L.messages with
  | nil =>
    rw [hmsgs] at hhead
    cases hhead
  | cons m0 rest =>
    rw [hmsgs] at hhead
    have hm0 : m0.moment = 0 := by simpa using hhead
    have hget : L.messages[0]? = some m0 := by rw [hmsgs]; rfl
    obtain ⟨n, hh⟩ := messages_held h hL hget
    unfold messageHeld at hh
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hrow⟩, _⟩, _⟩, _⟩, _⟩ := hh
    have hrow1 : m0.shape.maskRows = 1 := by simpa using hrow
    have hcode : m0.shape.maskCode = p.shape.maskCode := by
      have := List.all_eq_true.1 hms m0 (by rw [hmsgs]; exact List.mem_cons_self)
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
      rcases this.1.2 with h0 | h0
      · rw [hrow1] at h0
        cases h0
      · exact h0
    have hmA : messagesAt (sentOfBuilt p B) x.link = m0 :: rest := by
      unfold messagesAt
      rw [hx]
      show ((p.shape.link[l]?).map (·.messages)).getD [] = _
      rw [hL]
      exact hmsgs
    have hmask : maskMsg (sentOfBuilt p B) x.link =
        some ((keptAt (sentOfBuilt p B) x.link).length + 0) := by
      unfold maskMsg
      rw [hmA, List.findIdx?_cons, hrow1]
      rfl
    have hshape : (shapesCalls (sentOfBuilt p B) x.link)[
        (keptAt (sentOfBuilt p B) x.link).length + 0]? = some m0.shape := by
      unfold shapesCalls sigListCalls sigList
      rw [List.map_append, List.getElem?_append_right (by simp), hmA,
        List.takeWhile_cons_of_pos (by rw [hm0]; rfl)]
      simp
    unfold masksUpTo
    rw [hmask]
    simp only [hshape, hrow1]
    have hp : (Johnson.Pack.pMask (sentOfBuilt p B).codes m0.shape).ell = zk.ell := by
      unfold Johnson.Pack.pMask
      rw [hcode, Array.getD_eq_getD_getElem?]
      show ((p.codes.mask[p.shape.maskCode]?).getD default).ell = _
      rw [hzk]
      rfl
    rw [hp, hns]
    simp [hroom]

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.buildLinks_cut
#print axioms VerifiableInference.Desc.First.Att.P.layout_of_built
#print axioms VerifiableInference.Desc.First.Att.P.messages_held
#print axioms VerifiableInference.Desc.First.Att.P.oneMask_of_built
#print axioms VerifiableInference.Desc.First.Att.P.links_laid
#print axioms VerifiableInference.Desc.First.Att.P.masks_of_built
