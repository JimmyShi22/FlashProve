-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/PubAllAt.lean: WHAT THE COMPOSED PUBLIC ITEMS' BOOL `pubAll`
(Johnson/Desc/First/PubAll.lean) SAYS AT EACH SORT OF PUBLIC ITEM: ONE NAMED LEMMA AN OWNER, THE
OWNER's OWN Bool ON THE RIGHT. No Mathlib. Statements and proofs.

Why. A kind's law is proved under premises on a letter Mg ("Mg.pub (.look m) a = my Bool"); it is
counted at the composed meaning, whose pub is `pubAll D base`. These lemmas are those premises at
the composed function.

WHAT DOES NOT TURN. Each lemma's hypotheses speak of THE OWNER's OWN TEST ("is the item mine") and
of the layers that lie OUTSIDE the owner's. By the rule by which `pubAll` is composed (a later
layer that matches a constructor which an earlier layer matches is laid BENEATH that earlier layer)
an owner's lemma never gains a hypothesis; only its proof may turn.
  Items that one layer answers outright: `pubAll_ledger`, `_freeAbove`, `_unheard` (the table's own)
    · `_hasRow` (the row on the weights') · `_tokenSmall` (the head's) · `_linkFresh`, `_left`,
    `_leftOn` (the lookups') · `_noneSent`, `_indexIs`, `_indexThere`, `_frontOk`, `_evalLaid` (the
    index's and the last sub-protocols') ·
    `_formsIn`, `_formsInT`, `_totalIn` (the runs' forms').
  Items that a layer answers by a test: `_look_head` (the head's segment) · `_look_lay` (a layers'
    segment that is not the head's) · `_look_att` (an attention segment that is neither) ·
    `_callerIn_lay`, `_callerIn_att` · `_lookIn`, `_lookOut` (where the lookups' sort at the piece
    is there).
  The door, BY THE NAME: `_more_wSits` · `_more_sentIs`, `_more_treesAre`, `_more_sentIs1` (at
    every segment) · `_more_rowsBare`, `_more_lookLeft` (at a layers' segment) ·
    `_more_readsThere`, `_more_okAt`, `_more_liveReq`, `_more_plain` (at an attention segment).
    A NAME THAT A PART STILL ANSWERS NEED NOT BE OPEN AT ANY BORDER: which names are open is the
    composed meaning's list of extra public tests' to say (Johnson/Desc/Sound/MgAllAt.lean).
  AUXILIARY, IT TURNS WITH THE LAYERS: CALL THE LEMMAS ABOVE: `pubAll_look_chain`.
  `pubAll_some`: where `whoFills` names a layer, `pubAll` does not read base. Beneath it, each layer
    twice: `‹layer›_cong` (it hands an equation at the item through) · `‹layer›_own` (at an item of
    its own it does not read what lies beneath).

Limits. THREE OF Pub's 22 CONSTRUCTORS ARE TESTED BY NO Bool HERE: left and leftOn are `true` at
every state of the verifier (by the table's own word they have no Bool: their sentences stand in
`Meaning.pubP`); request is answered by no layer: no lemma: what `pubAll` says there is base, and
the next layer may turn it. At callerIn the head's segment is nobody's yet; at lookIn and lookOut a
piece without a sort. Nothing on what a Bool means. Nothing on soundness.

-/
import Johnson.Desc.First.PubAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc.K9 (pubForms)
open VerifiableInference.Desc.K13 (pubK13C k13ItemC noneSentC indexIsC indexThereC frontOkC
  evalLaidC wSitsC wSeatC)
open VerifiableInference.Desc.First.FillK4 (pubK4 k4Item isLay lookLayB callerInLayB)
open VerifiableInference.Desc.Kinds.Head (pubK6K7 k6k7Item tokenHeardB lookHeadB)
open VerifiableInference.Desc.First.Look (pubK3 k3Item k3SortAt lookInC lookOutC linkFreshC)
open VerifiableInference.Desc.First.FillP1 (pubP1 p1Item)
open VerifiableInference.Desc.First.FillSent (pubSent sentItem sentIsB treesAreB pubSent1 sent1Item)
open VerifiableInference.Desc.First.FillBare (pubLeft leftItem rowsBareB lookLeftB)
open H2K5.Door (pubK5 k5Item lookAttB callerIn3B readsThereB okThereB plainThereB bornOf)

variable {P : Type} (D : PubData) (base : Pub → P × S → Bool)

/-! ## 1 Items that one layer answers outright -/

/-- The table's own. -/
theorem pubAll_ledger (m : Nat) (a : P × S) : pubAll D base (.ledger m) a = ledgerB a.2 := rfl

theorem pubAll_freeAbove (m : Nat) (a : P × S) :
    pubAll D base (.freeAbove m) a = (D.nsOf m).any fun n => freeAboveB n a.2 := rfl

theorem pubAll_unheard (a : P × S) : pubAll D base .unheard a = unheardB a.2 := rfl

/-- The row on the weights'. -/
theorem pubAll_hasRow (m : Nat) (a : P × S) :
    pubAll D base (.hasRow m) a =
      Johnson.Desc.First.Walk.Law.hasRow D.d1.lay (D.d1.ncl m) D.d1.lin a.2 := rfl

/-- The head's. -/
theorem pubAll_tokenSmall (a : P × S) :
    pubAll D base .tokenSmall a = tokenHeardB D.hShape D.iU3 a.2 := rfl

/-- The lookups'. -/
theorem pubAll_linkFresh (m : Nat) (a : P × S) :
    pubAll D base (.linkFresh m) a = linkFreshC D.d3 m a.2 := rfl

theorem pubAll_left (m : Nat) (a : P × S) : pubAll D base (.left m) a = true := rfl

theorem pubAll_leftOn (m : Nat) (a : P × S) : pubAll D base (.leftOn m) a = true := rfl

/-- The index's and the last blocks'. The start's layer lies beneath and yields. -/
theorem pubAll_noneSent (a : P × S) : pubAll D base .noneSent a = noneSentC D.N a.2 := rfl

theorem pubAll_indexIs (a : P × S) : pubAll D base .indexIs a = indexIsC D.N.indexNo a.2 := rfl

theorem pubAll_indexThere (a : P × S) : pubAll D base .indexThere a = indexThereC a.2 := rfl

theorem pubAll_frontOk (a : P × S) : pubAll D base .frontOk a = frontOkC D.P13 a.2 := rfl

theorem pubAll_evalLaid (a : P × S) : pubAll D base .evalLaid a = evalLaidC D.P13 a.2 := rfl

/-- The runs' forms'. -/
theorem pubAll_formsIn (m k : Nat) (r : String) (a : P × S) :
    pubAll D base (.formsIn m k r) a =
      (D.runs m k r).all fun p =>
        if D.ah p.1 p.2 then K9.formsInA (D.Rd m) (D.N.sent m) (D.N.group m) p.1 p.2 a.2
        else K9.formsIn (D.Rd m) (D.N.group m) p.1 p.2 a.2 := rfl

theorem pubAll_formsInT (m k : Nat) (r : String) (a : P × S) :
    pubAll D base (.formsInT m k r) a =
      (D.runs m k r).all fun p => K9.formsInT (D.Rd m) (D.N.sent m 0) p.1 p.2 a.2 := rfl

theorem pubAll_totalIn (m : Nat) (a : P × S) :
    pubAll D base (.totalIn m) a = K9.totalIn (D.N.group m) a.2 := rfl

/-! ## 2 Items that a layer answers by a test -/

/-- AUXILIARY: IT TURNS WITH THE LAYERS: call `pubAll_look_head`, `pubAll_look_lay`. -/
theorem pubAll_look_chain (m : Nat) (a : P × S) :
    pubAll D base (.look m) a =
      (if m == D.mH then lookHeadB D.hShape D.iU3 a.2
      else if isLay D.links m then lookLayB a.2
      else if D.d5.isAtt m then lookAttB a.2 else base (.look m) a) := rfl

/-- The head's: at the head's segment. -/
theorem pubAll_look_head (m : Nat) (h : (m == D.mH) = true) (a : P × S) :
    pubAll D base (.look m) a = lookHeadB D.hShape D.iU3 a.2 := by
  rw [pubAll_look_chain, if_pos h]

/-- The feed-forward caller's: at a layers' segment that is not the head's. -/
theorem pubAll_look_lay (m : Nat) (h1 : (m == D.mH) = false) (h2 : isLay D.links m = true)
    (a : P × S) : pubAll D base (.look m) a = lookLayB a.2 := by
  rw [pubAll_look_chain, h1, if_neg (by simp), if_pos h2]

/-- The attention caller's: at an attention segment that is neither the head's nor a layers'. -/
theorem pubAll_look_att (m : Nat) (h0 : (m == D.mH) = false) (h1 : isLay D.links m = false)
    (h2 : D.d5.isAtt m = true) (a : P × S) : pubAll D base (.look m) a = lookAttB a.2 := by
  rw [pubAll_look_chain, h0, h1, if_neg (by simp), if_neg (by simp), if_pos h2]

theorem pubAll_callerIn_att (m : Nat) (h1 : isLay D.links m = false) (h2 : D.d5.isAtt m = true)
    (a : P × S) :
    pubAll D base (.callerIn m) a = (D.d5.first? m).any fun n => callerIn3B n a.2 := by
  show (if isLay D.links m then _
    else if D.d5.isAtt m then (D.d5.first? m).any fun n => callerIn3B n a.2 else _) = _
  rw [h1, if_neg (by simp), if_pos h2]

theorem pubAll_callerIn_lay (m : Nat) (h : isLay D.links m = true) (a : P × S) :
    pubAll D base (.callerIn m) a = (D.nextOf m).any fun n => callerInLayB n a.2 := by
  show (if isLay D.links m then (D.nextOf m).any fun n => callerInLayB n a.2 else _) = _
  rw [if_pos h]

/-- The lookups': where the piece has a sort. -/
theorem pubAll_lookIn (m pc : Nat) (dg : Bool) (h : k3SortAt D.d3.X m pc = some dg) (a : P × S) :
    pubAll D base (.lookIn m pc) a = lookInC D.d3 m dg a.2 := by
  show (match k3SortAt D.d3.X m pc with
    | some dg => lookInC D.d3 m dg a.2
    | none => _) = _
  rw [h]

theorem pubAll_lookOut (m pc : Nat) (dg : Bool) (h : k3SortAt D.d3.X m pc = some dg) (a : P × S) :
    pubAll D base (.lookOut m pc) a = lookOutC D.d3 m dg a.2 := by
  show (match k3SortAt D.d3.X m pc with
    | some dg => lookOutC D.d3 m dg a.2
    | none => _) = _
  rw [h]

/-! ## 3 The door, by the name -/

/-- The last blocks'. -/
theorem pubAll_more_wSits (a : P × S) :
    pubAll D base (.more none "K13.wSits") a = (wSitsC D.cs D.P13 a.2 && wSeatC D.N.w a.2) := rfl

/-- At a name of the door that is none of the attention caller's four, its layer hands on. -/
theorem pubK5_more_else (f : Pub → P × S → Bool) (m : Nat) (name : String)
    (h : (name == "K5.readsThere" || name == "K5.okAt" || name == "K5.liveReq" ||
      name == "K5.plain") = false) (a : P × S) :
    pubK5 D.d5 f (.more (some m) name) a = f (.more (some m) name) a := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  show (if (D.d5.isAtt m && name == "K5.readsThere") = true then _
    else if (D.d5.isAtt m && name == "K5.okAt") = true then _
    else if (D.d5.isAtt m && name == "K5.liveReq") = true then _
    else if (D.d5.isAtt m && name == "K5.plain") = true then _ else _) = _
  rw [h1, h2, h3, h4]
  cases D.d5.isAtt m <;> rfl

/-- What stands sent: at every segment. -/
theorem pubAll_more_sentIs (m : Nat) (a : P × S) :
    pubAll D base (.more (some m) "frame.sentIs") a = sentIsB D.dS m a.2 := by
  show pubK5 D.d5 _ (.more (some m) "frame.sentIs") a = _
  rw [pubK5_more_else D _ m _ rfl]
  rfl

theorem pubAll_more_treesAre (m : Nat) (a : P × S) :
    pubAll D base (.more (some m) "ledger.treesAre") a = treesAreB D.dS m a.2 := by
  show pubK5 D.d5 _ (.more (some m) "ledger.treesAre") a = _
  rw [pubK5_more_else D _ m _ rfl]
  rfl

theorem pubAll_more_sentIs1 (m : Nat) (a : P × S) :
    pubAll D base (.more (some m) "frame.sentIs1") a = sentIsB D.dS1 m a.2 := by
  show pubK5 D.d5 _ (.more (some m) "frame.sentIs1") a = _
  rw [pubK5_more_else D _ m _ rfl]
  rfl

/-- The feed-forward caller's two names: at a layers' segment. -/
theorem pubAll_more_rowsBare (m : Nat) (h : (D.links[m]? == some .layers) = true) (a : P × S) :
    pubAll D base (.more (some m) "K4.rowsBare") a = rowsBareB a.2 := by
  show pubK5 D.d5 _ (.more (some m) "K4.rowsBare") a = _
  rw [pubK5_more_else D _ m _ rfl]
  show (if (D.links[m]? == some .layers && "K4.rowsBare" == "K4.rowsBare") = true then _
    else _) = _
  rw [h]
  rfl

theorem pubAll_more_lookLeft (m : Nat) (h : (D.links[m]? == some .layers) = true) (a : P × S) :
    pubAll D base (.more (some m) "K4.lookLeft") a = lookLeftB a.2 := by
  show pubK5 D.d5 _ (.more (some m) "K4.lookLeft") a = _
  rw [pubK5_more_else D _ m _ rfl]
  show (if (D.links[m]? == some .layers && "K4.lookLeft" == "K4.rowsBare") = true then _
    else if (D.links[m]? == some .layers && "K4.lookLeft" == "K4.lookLeft") = true then _
    else _) = _
  rw [h]
  rfl

/-- The attention caller's four names: at an attention segment. -/
theorem pubAll_more_readsThere (m : Nat) (h : D.d5.isAtt m = true) (a : P × S) :
    pubAll D base (.more (some m) "K5.readsThere") a =
      readsThereB D.d5.W (D.d5.ownOf m) a.2 := by
  show (if (D.d5.isAtt m && "K5.readsThere" == "K5.readsThere") = true then _
    else if (D.d5.isAtt m && "K5.readsThere" == "K5.okAt") = true then _
    else if (D.d5.isAtt m && "K5.readsThere" == "K5.liveReq") = true then _
    else if (D.d5.isAtt m && "K5.readsThere" == "K5.plain") = true then _ else _) = _
  rw [h]
  rfl

theorem pubAll_more_okAt (m : Nat) (h : D.d5.isAtt m = true) (a : P × S) :
    pubAll D base (.more (some m) "K5.okAt") a =
      (D.d5.W.A[m / 2]?).any fun p => okThereB (Att.P.geoOf p.S) a.2 := by
  show (if (D.d5.isAtt m && "K5.okAt" == "K5.readsThere") = true then _
    else if (D.d5.isAtt m && "K5.okAt" == "K5.okAt") = true then _
    else if (D.d5.isAtt m && "K5.okAt" == "K5.liveReq") = true then _
    else if (D.d5.isAtt m && "K5.okAt" == "K5.plain") = true then _ else _) = _
  rw [h]
  rfl

theorem pubAll_more_liveReq (m : Nat) (h : D.d5.isAtt m = true) (a : P × S) :
    pubAll D base (.more (some m) "K5.liveReq") a =
      Att.P.liveReqB (bornOf D.d5.shape m) a.2 := by
  show (if (D.d5.isAtt m && "K5.liveReq" == "K5.readsThere") = true then _
    else if (D.d5.isAtt m && "K5.liveReq" == "K5.okAt") = true then _
    else if (D.d5.isAtt m && "K5.liveReq" == "K5.liveReq") = true then _
    else if (D.d5.isAtt m && "K5.liveReq" == "K5.plain") = true then _ else _) = _
  rw [h]
  rfl

theorem pubAll_more_plain (m : Nat) (h : D.d5.isAtt m = true) (a : P × S) :
    pubAll D base (.more (some m) "K5.plain") a =
      (D.d5.W.A[m / 2]?).any fun p => plainThereB p.iU3 p.nW a.2 := by
  show (if (D.d5.isAtt m && "K5.plain" == "K5.readsThere") = true then _
    else if (D.d5.isAtt m && "K5.plain" == "K5.okAt") = true then _
    else if (D.d5.isAtt m && "K5.plain" == "K5.liveReq") = true then _
    else if (D.d5.isAtt m && "K5.plain" == "K5.plain") = true then _ else _) = _
  rw [h]
  rfl

/-! ## 4 Where a layer answers, base is not read -/

section
variable {base' : Pub → P × S → Bool} (f f' : Pub → P × S → Bool) (q : Pub) (a : P × S)

/-! Each layer, twice: it hands an equation at q through ("cong"); at an item of its own it does not
read what lies beneath ("own"). -/

theorem pubForms_cong (h : f q a = f' q a) :
    pubForms D.Rd D.runs D.ah D.N f q a = pubForms D.Rd D.runs D.ah D.N f' q a := by
  cases q <;> first | rfl | exact h

theorem pubForms_own (h : formsItem q = true) :
    pubForms D.Rd D.runs D.ah D.N f q a = pubForms D.Rd D.runs D.ah D.N f' q a := by
  cases q <;> first | rfl | (simp [formsItem] at h)

theorem pubK13C_cong (h : f q a = f' q a) :
    pubK13C D.P13 D.cs D.N f q a = pubK13C D.P13 D.cs D.N f' q a := by
  cases q with
  | more seg name =>
    show (if seg.isNone && name == "K13.wSits" then _ else f (.more seg name) a) =
      (if seg.isNone && name == "K13.wSits" then _ else f' (.more seg name) a)
    rw [h]
  | _ => first | rfl | exact h

theorem pubK13C_own (h : k13ItemC q = true) :
    pubK13C D.P13 D.cs D.N f q a = pubK13C D.P13 D.cs D.N f' q a := by
  cases q with
  | more seg name =>
    have h' : (seg.isNone && name == "K13.wSits") = true := h
    show (if seg.isNone && name == "K13.wSits" then _ else f (.more seg name) a) =
      (if seg.isNone && name == "K13.wSits" then _ else f' (.more seg name) a)
    rw [if_pos h', if_pos h']
  | _ => first | rfl | (simp [k13ItemC] at h)

theorem pubK3_cong (h : f q a = f' q a) : pubK3 D.d3 f q a = pubK3 D.d3 f' q a := by
  cases q with
  | lookIn m pc =>
    show (match k3SortAt D.d3.X m pc with
      | some dg => lookInC D.d3 m dg a.2
      | none => f (.lookIn m pc) a) = (match k3SortAt D.d3.X m pc with
      | some dg => lookInC D.d3 m dg a.2
      | none => f' (.lookIn m pc) a)
    rw [h]
  | lookOut m pc =>
    show (match k3SortAt D.d3.X m pc with
      | some dg => lookOutC D.d3 m dg a.2
      | none => f (.lookOut m pc) a) = (match k3SortAt D.d3.X m pc with
      | some dg => lookOutC D.d3 m dg a.2
      | none => f' (.lookOut m pc) a)
    rw [h]
  | _ => first | rfl | exact h

theorem pubK3_own (h : k3Item D.d3 q = true) : pubK3 D.d3 f q a = pubK3 D.d3 f' q a := by
  cases q with
  | lookIn m pc =>
    obtain ⟨dg, e⟩ := Option.isSome_iff_exists.1 (show (k3SortAt D.d3.X m pc).isSome = true from h)
    show (match k3SortAt D.d3.X m pc with
      | some dg => lookInC D.d3 m dg a.2
      | none => f (.lookIn m pc) a) = (match k3SortAt D.d3.X m pc with
      | some dg => lookInC D.d3 m dg a.2
      | none => f' (.lookIn m pc) a)
    rw [e]
  | lookOut m pc =>
    obtain ⟨dg, e⟩ := Option.isSome_iff_exists.1 (show (k3SortAt D.d3.X m pc).isSome = true from h)
    show (match k3SortAt D.d3.X m pc with
      | some dg => lookOutC D.d3 m dg a.2
      | none => f (.lookOut m pc) a) = (match k3SortAt D.d3.X m pc with
      | some dg => lookOutC D.d3 m dg a.2
      | none => f' (.lookOut m pc) a)
    rw [e]
  | _ => first | rfl | (simp [k3Item] at h)

theorem pubK6K7_cong (h : f q a = f' q a) :
    pubK6K7 D.hShape D.iU3 D.mH f q a = pubK6K7 D.hShape D.iU3 D.mH f' q a := by
  cases q with
  | look m =>
    show (if m == D.mH then lookHeadB D.hShape D.iU3 a.2 else f (.look m) a) =
      (if m == D.mH then lookHeadB D.hShape D.iU3 a.2 else f' (.look m) a)
    rw [h]
  | _ => first | rfl | exact h

theorem pubK6K7_own (h : k6k7Item D.mH q = true) :
    pubK6K7 D.hShape D.iU3 D.mH f q a = pubK6K7 D.hShape D.iU3 D.mH f' q a := by
  cases q with
  | look m =>
    have h' : (m == D.mH) = true := h
    show (if m == D.mH then lookHeadB D.hShape D.iU3 a.2 else f (.look m) a) =
      (if m == D.mH then lookHeadB D.hShape D.iU3 a.2 else f' (.look m) a)
    rw [if_pos h', if_pos h']
  | _ => first | rfl | (simp [k6k7Item] at h)

theorem pubK4_cong (h : f q a = f' q a) :
    pubK4 D.links D.nextOf f q a = pubK4 D.links D.nextOf f' q a := by
  cases q with
  | look m =>
    show (if isLay D.links m then lookLayB a.2 else f (.look m) a) =
      (if isLay D.links m then lookLayB a.2 else f' (.look m) a)
    rw [h]
  | callerIn m =>
    show (if isLay D.links m then (D.nextOf m).any fun n => callerInLayB n a.2
      else f (.callerIn m) a) =
      (if isLay D.links m then (D.nextOf m).any fun n => callerInLayB n a.2
      else f' (.callerIn m) a)
    rw [h]
  | _ => exact h

theorem pubK4_own (h : k4Item D.links q = true) :
    pubK4 D.links D.nextOf f q a = pubK4 D.links D.nextOf f' q a := by
  cases q with
  | look m =>
    have h' : isLay D.links m = true := h
    show (if isLay D.links m then lookLayB a.2 else f (.look m) a) =
      (if isLay D.links m then lookLayB a.2 else f' (.look m) a)
    rw [if_pos h', if_pos h']
  | callerIn m =>
    have h' : isLay D.links m = true := h
    show (if isLay D.links m then (D.nextOf m).any fun n => callerInLayB n a.2
      else f (.callerIn m) a) =
      (if isLay D.links m then (D.nextOf m).any fun n => callerInLayB n a.2
      else f' (.callerIn m) a)
    rw [if_pos h', if_pos h']
  | _ => simp [k4Item] at h

theorem pubP1_cong (h : f q a = f' q a) : pubP1 D.d1 f q a = pubP1 D.d1 f' q a := by
  cases q with
  | _ => first | rfl | exact h

theorem pubP1_own (h : p1Item q = true) : pubP1 D.d1 f q a = pubP1 D.d1 f' q a := by
  cases q with
  | _ => first | rfl | (simp [p1Item] at h)

theorem pubK5_cong (h : f q a = f' q a) : pubK5 D.d5 f q a = pubK5 D.d5 f' q a := by
  cases q with
  | callerIn m =>
    show (if D.d5.isAtt m then (D.d5.first? m).any fun n => callerIn3B n a.2
      else f (.callerIn m) a) =
      (if D.d5.isAtt m then (D.d5.first? m).any fun n => callerIn3B n a.2
      else f' (.callerIn m) a)
    rw [h]
  | look m =>
    show (if D.d5.isAtt m then lookAttB a.2 else f (.look m) a) =
      (if D.d5.isAtt m then lookAttB a.2 else f' (.look m) a)
    rw [h]
  | more sg name =>
    cases sg with
    | none => exact h
    | some m =>
      show (if (D.d5.isAtt m && name == "K5.readsThere") = true then
          readsThereB D.d5.W (D.d5.ownOf m) a.2
        else if (D.d5.isAtt m && name == "K5.okAt") = true then
          (D.d5.W.A[m / 2]?).any fun p => okThereB (Att.P.geoOf p.S) a.2
        else if (D.d5.isAtt m && name == "K5.liveReq") = true then
          Att.P.liveReqB (bornOf D.d5.shape m) a.2
        else if (D.d5.isAtt m && name == "K5.plain") = true then
          (D.d5.W.A[m / 2]?).any fun p => plainThereB p.iU3 p.nW a.2
        else f (.more (some m) name) a) =
        (if (D.d5.isAtt m && name == "K5.readsThere") = true then
          readsThereB D.d5.W (D.d5.ownOf m) a.2
        else if (D.d5.isAtt m && name == "K5.okAt") = true then
          (D.d5.W.A[m / 2]?).any fun p => okThereB (Att.P.geoOf p.S) a.2
        else if (D.d5.isAtt m && name == "K5.liveReq") = true then
          Att.P.liveReqB (bornOf D.d5.shape m) a.2
        else if (D.d5.isAtt m && name == "K5.plain") = true then
          (D.d5.W.A[m / 2]?).any fun p => plainThereB p.iU3 p.nW a.2
        else f' (.more (some m) name) a)
      rw [h]
  | _ => exact h

theorem pubK5_own (h : k5Item D.d5 q = true) : pubK5 D.d5 f q a = pubK5 D.d5 f' q a := by
  cases q with
  | callerIn m =>
    have h' : D.d5.isAtt m = true := h
    show (if D.d5.isAtt m then (D.d5.first? m).any fun n => callerIn3B n a.2
      else f (.callerIn m) a) =
      (if D.d5.isAtt m then (D.d5.first? m).any fun n => callerIn3B n a.2
      else f' (.callerIn m) a)
    rw [if_pos h', if_pos h']
  | look m =>
    have h' : D.d5.isAtt m = true := h
    show (if D.d5.isAtt m then lookAttB a.2 else f (.look m) a) =
      (if D.d5.isAtt m then lookAttB a.2 else f' (.look m) a)
    rw [if_pos h', if_pos h']
  | more sg name =>
    cases sg with
    | none => simp [k5Item] at h
    | some m =>
      have h' : (D.d5.isAtt m && (name == "K5.readsThere" || name == "K5.okAt" ||
        name == "K5.liveReq" || name == "K5.plain")) = true := h
      show (if (D.d5.isAtt m && name == "K5.readsThere") = true then
          readsThereB D.d5.W (D.d5.ownOf m) a.2
        else if (D.d5.isAtt m && name == "K5.okAt") = true then
          (D.d5.W.A[m / 2]?).any fun p => okThereB (Att.P.geoOf p.S) a.2
        else if (D.d5.isAtt m && name == "K5.liveReq") = true then
          Att.P.liveReqB (bornOf D.d5.shape m) a.2
        else if (D.d5.isAtt m && name == "K5.plain") = true then
          (D.d5.W.A[m / 2]?).any fun p => plainThereB p.iU3 p.nW a.2
        else f (.more (some m) name) a) =
        (if (D.d5.isAtt m && name == "K5.readsThere") = true then
          readsThereB D.d5.W (D.d5.ownOf m) a.2
        else if (D.d5.isAtt m && name == "K5.okAt") = true then
          (D.d5.W.A[m / 2]?).any fun p => okThereB (Att.P.geoOf p.S) a.2
        else if (D.d5.isAtt m && name == "K5.liveReq") = true then
          Att.P.liveReqB (bornOf D.d5.shape m) a.2
        else if (D.d5.isAtt m && name == "K5.plain") = true then
          (D.d5.W.A[m / 2]?).any fun p => plainThereB p.iU3 p.nW a.2
        else f' (.more (some m) name) a)
      by_cases e1 : (D.d5.isAtt m && name == "K5.readsThere") = true
      · rw [if_pos e1, if_pos e1]
      · by_cases e2 : (D.d5.isAtt m && name == "K5.okAt") = true
        · rw [if_neg e1, if_neg e1, if_pos e2, if_pos e2]
        · by_cases e3 : (D.d5.isAtt m && name == "K5.liveReq") = true
          · rw [if_neg e1, if_neg e1, if_neg e2, if_neg e2, if_pos e3, if_pos e3]
          · by_cases e4 : (D.d5.isAtt m && name == "K5.plain") = true
            · rw [if_neg e1, if_neg e1, if_neg e2, if_neg e2, if_neg e3, if_neg e3, if_pos e4,
                if_pos e4]
            · exfalso
              cases hA : D.d5.isAtt m <;> simp_all
  | _ => simp [k5Item] at h

theorem pubSent_cong (h : f q a = f' q a) : pubSent D.dS f q a = pubSent D.dS f' q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => exact h
    | some m =>
      show (if name == "frame.sentIs" then sentIsB D.dS m a.2
        else if name == "ledger.treesAre" then treesAreB D.dS m a.2
        else f (.more (some m) name) a) =
        (if name == "frame.sentIs" then sentIsB D.dS m a.2
        else if name == "ledger.treesAre" then treesAreB D.dS m a.2
        else f' (.more (some m) name) a)
      rw [h]
  | _ => exact h

theorem pubSent_own (h : sentItem q = true) : pubSent D.dS f q a = pubSent D.dS f' q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => simp [sentItem] at h
    | some m =>
      have h' : (name == "frame.sentIs" || name == "ledger.treesAre") = true := h
      show (if name == "frame.sentIs" then sentIsB D.dS m a.2
        else if name == "ledger.treesAre" then treesAreB D.dS m a.2
        else f (.more (some m) name) a) =
        (if name == "frame.sentIs" then sentIsB D.dS m a.2
        else if name == "ledger.treesAre" then treesAreB D.dS m a.2
        else f' (.more (some m) name) a)
      by_cases e1 : (name == "frame.sentIs") = true
      · rw [if_pos e1, if_pos e1]
      · by_cases e2 : (name == "ledger.treesAre") = true
        · rw [if_neg e1, if_neg e1, if_pos e2, if_pos e2]
        · simp [e1, e2] at h'
  | _ => simp [sentItem] at h

theorem pubSent1_cong (h : f q a = f' q a) : pubSent1 D.dS1 f q a = pubSent1 D.dS1 f' q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => exact h
    | some m =>
      show (if name == "frame.sentIs1" then sentIsB D.dS1 m a.2 else f (.more (some m) name) a) =
        (if name == "frame.sentIs1" then sentIsB D.dS1 m a.2 else f' (.more (some m) name) a)
      rw [h]
  | _ => exact h

theorem pubSent1_own (h : sent1Item q = true) :
    pubSent1 D.dS1 f q a = pubSent1 D.dS1 f' q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => simp [sent1Item] at h
    | some m =>
      have h' : (name == "frame.sentIs1") = true := h
      show (if name == "frame.sentIs1" then sentIsB D.dS1 m a.2 else f (.more (some m) name) a) =
        (if name == "frame.sentIs1" then sentIsB D.dS1 m a.2 else f' (.more (some m) name) a)
      rw [if_pos h', if_pos h']
  | _ => simp [sent1Item] at h

theorem pubLeft_cong (h : f q a = f' q a) : pubLeft D.links f q a = pubLeft D.links f' q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => exact h
    | some m =>
      show (if (D.links[m]? == some .layers && name == "K4.rowsBare") = true then rowsBareB a.2
        else if (D.links[m]? == some .layers && name == "K4.lookLeft") = true then lookLeftB a.2
        else f (.more (some m) name) a) =
        (if (D.links[m]? == some .layers && name == "K4.rowsBare") = true then rowsBareB a.2
        else if (D.links[m]? == some .layers && name == "K4.lookLeft") = true then lookLeftB a.2
        else f' (.more (some m) name) a)
      rw [h]
  | _ => exact h

theorem pubLeft_own (h : leftItem D.links q = true) :
    pubLeft D.links f q a = pubLeft D.links f' q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => simp [leftItem] at h
    | some m =>
      have h' : (D.links[m]? == some .layers &&
        (name == "K4.rowsBare" || name == "K4.lookLeft")) = true := h
      show (if (D.links[m]? == some .layers && name == "K4.rowsBare") = true then rowsBareB a.2
        else if (D.links[m]? == some .layers && name == "K4.lookLeft") = true then lookLeftB a.2
        else f (.more (some m) name) a) =
        (if (D.links[m]? == some .layers && name == "K4.rowsBare") = true then rowsBareB a.2
        else if (D.links[m]? == some .layers && name == "K4.lookLeft") = true then lookLeftB a.2
        else f' (.more (some m) name) a)
      by_cases e1 : (D.links[m]? == some .layers && name == "K4.rowsBare") = true
      · rw [if_pos e1, if_pos e1]
      · by_cases e2 : (D.links[m]? == some .layers && name == "K4.lookLeft") = true
        · rw [if_neg e1, if_neg e1, if_pos e2, if_pos e2]
        · exfalso
          cases hA : (D.links[m]? == some .layers) <;> simp_all
  | _ => simp [leftItem] at h

theorem pubKeeper_own (h : keeperItem q = true) :
    pubKeeper D.nsOf f q a = pubKeeper D.nsOf f' q a := by
  cases q <;> first | rfl | (simp [keeperItem] at h)

end

/-- **Where `whoFills` names a layer, `pubAll` does not read base.** -/
theorem pubAll_some (base' : Pub → P × S → Bool) (q : Pub) (a : P × S)
    (h : (whoFills D q).isSome = true) : pubAll D base q a = pubAll D base' q a := by
  unfold pubAll
  by_cases h1 : formsItem q = true
  · exact pubForms_own D _ _ q a h1
  refine pubForms_cong D _ _ q a ?_
  by_cases h2 : k13ItemC q = true
  · exact pubK13C_own D _ _ q a h2
  refine pubK13C_cong D _ _ q a ?_
  by_cases h3 : k3Item D.d3 q = true
  · exact pubK3_own D _ _ q a h3
  refine pubK3_cong D _ _ q a ?_
  by_cases h4 : k6k7Item D.mH q = true
  · exact pubK6K7_own D _ _ q a h4
  refine pubK6K7_cong D _ _ q a ?_
  by_cases h5 : k4Item D.links q = true
  · exact pubK4_own D _ _ q a h5
  refine pubK4_cong D _ _ q a ?_
  by_cases h9 : p1Item q = true
  · exact pubP1_own D _ _ q a h9
  refine pubP1_cong D _ _ q a ?_
  by_cases h10 : k5Item D.d5 q = true
  · exact pubK5_own D _ _ q a h10
  refine pubK5_cong D _ _ q a ?_
  by_cases h11 : sentItem q = true
  · exact pubSent_own D _ _ q a h11
  refine pubSent_cong D _ _ q a ?_
  by_cases h13 : sent1Item q = true
  · exact pubSent1_own D _ _ q a h13
  refine pubSent1_cong D _ _ q a ?_
  by_cases h12 : leftItem D.links q = true
  · exact pubLeft_own D _ _ q a h12
  refine pubLeft_cong D _ _ q a ?_
  by_cases h8 : keeperItem q = true
  · exact pubKeeper_own D _ _ q a h8
  · simp [whoFills, h1, h2, h3, h4, h5, h8, h9, h10, h11, h12, h13] at h

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.pubAll_ledger
#print axioms VerifiableInference.Desc.First.pubAll_freeAbove
#print axioms VerifiableInference.Desc.First.pubAll_unheard
#print axioms VerifiableInference.Desc.First.pubAll_tokenSmall
#print axioms VerifiableInference.Desc.First.pubAll_linkFresh
#print axioms VerifiableInference.Desc.First.pubAll_left
#print axioms VerifiableInference.Desc.First.pubAll_leftOn
#print axioms VerifiableInference.Desc.First.pubAll_noneSent
#print axioms VerifiableInference.Desc.First.pubAll_indexIs
#print axioms VerifiableInference.Desc.First.pubAll_indexThere
#print axioms VerifiableInference.Desc.First.pubAll_frontOk
#print axioms VerifiableInference.Desc.First.pubAll_evalLaid
#print axioms VerifiableInference.Desc.First.pubAll_formsIn
#print axioms VerifiableInference.Desc.First.pubAll_formsInT
#print axioms VerifiableInference.Desc.First.pubAll_totalIn
#print axioms VerifiableInference.Desc.First.pubAll_look_chain
#print axioms VerifiableInference.Desc.First.pubAll_look_head
#print axioms VerifiableInference.Desc.First.pubAll_look_lay
#print axioms VerifiableInference.Desc.First.pubAll_callerIn_lay
#print axioms VerifiableInference.Desc.First.pubAll_lookIn
#print axioms VerifiableInference.Desc.First.pubAll_lookOut
#print axioms VerifiableInference.Desc.First.pubAll_more_wSits
#print axioms VerifiableInference.Desc.First.pubForms_cong
#print axioms VerifiableInference.Desc.First.pubForms_own
#print axioms VerifiableInference.Desc.First.pubK3_cong
#print axioms VerifiableInference.Desc.First.pubK3_own
#print axioms VerifiableInference.Desc.First.pubK6K7_cong
#print axioms VerifiableInference.Desc.First.pubK6K7_own
#print axioms VerifiableInference.Desc.First.pubK4_cong
#print axioms VerifiableInference.Desc.First.pubK4_own
#print axioms VerifiableInference.Desc.First.pubKeeper_own
#print axioms VerifiableInference.Desc.First.pubAll_some
#print axioms VerifiableInference.Desc.First.pubAll_hasRow
#print axioms VerifiableInference.Desc.First.pubAll_look_att
#print axioms VerifiableInference.Desc.First.pubAll_callerIn_att
#print axioms VerifiableInference.Desc.First.pubAll_more_readsThere
#print axioms VerifiableInference.Desc.First.pubAll_more_okAt
#print axioms VerifiableInference.Desc.First.pubAll_more_liveReq
#print axioms VerifiableInference.Desc.First.pubAll_more_plain
#print axioms VerifiableInference.Desc.First.pubK5_cong
#print axioms VerifiableInference.Desc.First.pubK5_own
#print axioms VerifiableInference.Desc.First.pubK5_more_else
#print axioms VerifiableInference.Desc.First.pubAll_more_sentIs
#print axioms VerifiableInference.Desc.First.pubAll_more_treesAre
#print axioms VerifiableInference.Desc.First.pubAll_more_rowsBare
#print axioms VerifiableInference.Desc.First.pubAll_more_lookLeft
#print axioms VerifiableInference.Desc.First.pubSent_cong
#print axioms VerifiableInference.Desc.First.pubSent_own
#print axioms VerifiableInference.Desc.First.pubLeft_cong
#print axioms VerifiableInference.Desc.First.pubLeft_own
#print axioms VerifiableInference.Desc.First.pubK13C_cong
#print axioms VerifiableInference.Desc.First.pubK13C_own
#print axioms VerifiableInference.Desc.First.pubP1_cong
#print axioms VerifiableInference.Desc.First.pubP1_own
#print axioms VerifiableInference.Desc.First.pubSent1_cong
#print axioms VerifiableInference.Desc.First.pubSent1_own
#print axioms VerifiableInference.Desc.First.pubAll_more_sentIs1
